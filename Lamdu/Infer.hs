module Lamdu.Infer
  ( typeInference
  ) where

import Control.Applicative ((<$>), Applicative(..))
import Control.Lens (mapped)
import Control.Lens.Operators
import Control.Lens.Tuple
import Control.Monad (join)
import Control.Monad.Error (throwError, catchError)
import Control.Monad.State (evalStateT)
import Control.Monad.Trans (lift)
import Control.Monad.Writer (runWriterT)
import Data.Monoid (Monoid(..))
import Lamdu.Expr
import Lamdu.Infer.Internal.FlatRecordType
import Lamdu.Infer.Internal.FreeTypeVars
import Lamdu.Infer.Internal.Monad
import Lamdu.Infer.Scheme
import Lamdu.Infer.Scope (Scope)
import Lamdu.Pretty
import Text.PrettyPrint ((<+>))
import qualified Control.Monad.State as State
import qualified Control.Monad.Writer as Writer
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Lamdu.Infer.Internal.FlatRecordType as FlatRecordType
import qualified Lamdu.Infer.Scope as Scope
import qualified Text.PrettyPrint as PP

varBind :: TypeVar -> Type -> InferW ()
varBind u (TVar t) | t == u          =  return ()
varBind u t
  | u `Set.member` freeTypeVars t  =
    throwError $ show $
    PP.text "occurs check fails:" <+>
    prTypeVar u <+> PP.text "vs." <+> prType t
  | otherwise                        =  Writer.tell $ substFromList [(u, t)]

unifyRecToPartial ::
  (Map.Map String Type, TypeVar) -> Map.Map String Type ->
  InferW ()
unifyRecToPartial (tfields, tname) ufields
  | not (Map.null uniqueTFields) =
    throwError $ show $
    PP.text "Incompatible record types:" <+>
    prFlatRecordType (FlatRecordType tfields (Just tname)) <+>
    PP.text " vs. " <+>
    prFlatRecordType (FlatRecordType ufields Nothing)
  | otherwise = varBind tname $ FlatRecordType.toType $ FlatRecordType uniqueUFields Nothing
  where
    uniqueTFields = tfields `Map.difference` ufields
    uniqueUFields = ufields `Map.difference` tfields

unifyRecPartials ::
  (Map.Map String Type, TypeVar) -> (Map.Map String Type, TypeVar) ->
  InferW ()
unifyRecPartials (tfields, tname) (ufields, uname) =
  do  restTv <- lift $ newTyVar "r"
      ((), s1) <-
        Writer.listen $ varBind tname $
        Map.foldWithKey TRecExtend restTv uniqueUFields
      varBind uname $ applySubst s1 (Map.foldWithKey TRecExtend restTv uniqueTFields)
  where
    uniqueTFields = tfields `Map.difference` ufields
    uniqueUFields = ufields `Map.difference` tfields

unifyRecFulls ::
  Map.Map String Type -> Map.Map String Type -> InferW ()
unifyRecFulls tfields ufields
  | Map.keys tfields /= Map.keys ufields =
    throwError $ show $
    PP.text "Incompatible record types:" <+>
    prFlatRecordType (FlatRecordType tfields Nothing) <+>
    PP.text "vs." <+>
    prFlatRecordType (FlatRecordType ufields Nothing)
  | otherwise = return mempty

unifyRecs :: FlatRecordType -> FlatRecordType -> InferW ()
unifyRecs (FlatRecordType tfields tvar)
          (FlatRecordType ufields uvar) =
  do  let unifyField t u =
              do  old <- State.get
                  ((), s) <- lift $ Writer.listen $ mgu (applySubst old t) (applySubst old u)
                  State.put (old `mappend` s)
      (`evalStateT` mempty) . sequence_ . Map.elems $ Map.intersectionWith unifyField tfields ufields
      case (tvar, uvar) of
          (Nothing   , Nothing   ) -> unifyRecFulls tfields ufields
          (Just tname, Just uname) -> unifyRecPartials (tfields, tname) (ufields, uname)
          (Just tname, Nothing   ) -> unifyRecToPartial (tfields, tname) ufields
          (Nothing   , Just uname) -> unifyRecToPartial (ufields, uname) tfields

mgu :: Type -> Type -> InferW ()
mgu (TFun l r) (TFun l' r')  =  do  ((), s1) <- Writer.listen $ mgu l l'
                                    mgu (applySubst s1 r) (applySubst s1 r')
mgu (TApp l r) (TApp l' r')  =  do  ((), s1) <- Writer.listen $ mgu l l'
                                    mgu (applySubst s1 r) (applySubst s1 r')
mgu (TVar u) t               =  varBind u t
mgu t (TVar u)               =  varBind u t
mgu (TCon t) (TCon u)
  | t == u                   =  return mempty
mgu TRecEmpty TRecEmpty      =  return mempty
mgu t@TRecExtend {}
    u@TRecExtend {}          =  join $ either throwError return $
                                unifyRecs <$>
                                FlatRecordType.from t <*>
                                FlatRecordType.from u
mgu t1 t2                    =  throwError $ show $
                                PP.text "types do not unify: " <+> prType t1 <+>
                                PP.text "vs." <+> prType t2
typeInference :: Scope -> Expr a -> Either String (Expr (Type, a))
typeInference rootScope rootExpr =
    runInfer $
    do  ((_, t), s) <- runWriterT $ infer (,) rootScope rootExpr
        return (t & mapped . _1 %~ applySubst s)

infer :: (Type -> a -> b) -> Scope -> Expr a -> InferW (Type, Expr b)
infer f scope expr@(Expr pl body) = case body of
  ELeaf leaf ->
    mkResult (ELeaf leaf) <$>
    case leaf of
    EVar n ->
        case Scope.lookupTypeOf n scope of
           Nothing     -> throwError $ "unbound variable: " ++ n
           Just sigma  -> lift (instantiate sigma)
    ELit (LInt _) -> return (TCon "Int")
    ELit (LChar _) -> return (TCon "Char")
    ERecEmpty -> return TRecEmpty
  EAbs n e ->
    do  tv <- lift $ newTyVar "a"
        let scope' = Scope.insertTypeOf n (Scheme Set.empty tv) scope
        ((t1, e'), s1) <- Writer.listen $ infer f scope' e
        return $ mkResult (EAbs n e') $ TFun (applySubst s1 tv) t1
  EApp e1 e2 ->
    do  tv <- lift $ newTyVar "a"
        ((t1, e1'), s1) <- Writer.listen $ infer f scope e1
        ((t2, e2'), s2) <- Writer.listen $ infer f (applySubst s1 scope) e2
        ((), s3) <- Writer.listen $ mgu (applySubst s2 t1) (TFun t2 tv)
        return $ mkResult (EApp e1' e2') $ applySubst s3 tv
    `catchError`
    \e -> throwError $ e ++ "\n in " ++ show (prExp expr)
  ELet x e1 e2 ->
    do  ((t1, e1'), s1) <- Writer.listen $ infer f scope e1
        -- TODO: (freeTypeVars (applySubst s1 scope)) makes no sense performance-wise
        -- improve it
        let t' = generalize (freeTypeVars (applySubst s1 scope)) t1
            scope' = Scope.insertTypeOf x t' scope
        (t2, e2') <- infer f (applySubst s1 scope') e2
        return $ mkResult (ELet x e1' e2') $ t2
  EGetField e name ->
    do  tv <- lift $ newTyVar "a"
        tvRec <- lift $ newTyVar "r"
        ((t, e'), s) <- Writer.listen $ infer f scope e
        ((), su) <- Writer.listen $ mgu (applySubst s t) (TRecExtend name tv tvRec)
        return $ mkResult (EGetField e' name) $ applySubst su tv
  ERecExtend name e1 e2 ->
    do  ((t1, e1'), s1) <- Writer.listen $ infer f scope e1
        (t2, e2') <- infer f (applySubst s1 scope) e2
        return $ mkResult (ERecExtend name e1' e2') $ TRecExtend name t1 t2
  where
    mkResult body' typ = (typ, Expr (f typ pl) body')
