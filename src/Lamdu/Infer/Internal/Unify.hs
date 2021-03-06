-- | Unify support for type ASTs
{-# LANGUAGE NoImplicitPrelude #-}
module Lamdu.Infer.Internal.Unify
    ( unifyUnsafe
    ) where

import           Control.Lens.Operators
import           Control.Monad (when, unless)
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.State (StateT, evalStateT)
import qualified Control.Monad.Trans.State as State
import qualified Data.Foldable as Foldable
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Lamdu.Calc.Type (Type)
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.FlatComposite (FlatComposite(..))
import qualified Lamdu.Calc.Type.FlatComposite as FlatComposite
import qualified Lamdu.Calc.Type.Vars as TV
import qualified Lamdu.Infer.Error as Err
import           Lamdu.Infer.Internal.Monad (Infer)
import qualified Lamdu.Infer.Internal.Monad as M
import           Lamdu.Infer.Internal.Scope (SkolemScope(..))
import qualified Lamdu.Infer.Internal.Scope as Scope
import           Lamdu.Infer.Internal.Subst (Subst, CanSubst)
import qualified Lamdu.Infer.Internal.Subst as Subst
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

{-# INLINE unifyUnsafe #-}
unifyUnsafe :: Type -> Type -> Infer ()
unifyUnsafe = unifyGeneric

-- These tvs appear in a context that only allows given skolems, so
-- narrow down the skolem scopes of these tvs
narrowSkolemScopesIn :: Monad m => SkolemScope -> TV.TypeVars -> M.InferCtx m ()
narrowSkolemScopesIn allowedSkolems (TV.TypeVars tvs rvs) =
    narrow tvs >> narrow rvs
    where
        narrow nonSkolems =
            Foldable.traverse_ (M.narrowTVScope allowedSkolems)
            (Set.toList nonSkolems)

varBind :: (M.VarKind t, Pretty t) => T.Var t -> t -> Infer ()
varBind u t
    | mtTv == Just u = pure ()
    | otherwise =
        do
            allSkolems <- M.getSkolems
            case (u `TV.member` allSkolems, mtTv) of
                (False, _) ->
                    -- Binding a non-skolem(u) to a type(t)
                    do
                        uAllowedSkolems <- M.getSkolemsInScope u
                        let tSkolems = TV.intersection allSkolems tFree
                        -- u&t both not skolems. Narrow the skolem
                        -- scope of any free var in t
                        narrowSkolemScopesIn uAllowedSkolems
                            (tFree `TV.difference` tSkolems)
                        -- Next we check if the skolems in 't' escape
                        -- the scope of u (uAllowedSkolems)
                        let unallowedSkolems =
                                tSkolems `TV.difference`
                                (uAllowedSkolems ^. Scope.skolemScopeVars)
                        unless (TV.null unallowedSkolems) $
                            M.throwError $ Err.SkolemEscapesScope (pPrint u) (pPrint t) (pPrint unallowedSkolems)
                        -- Occurs check:
                        when (u `TV.member` tFree) $
                            M.throwError $ Err.OccursCheckFail (pPrint u) (pPrint t)
                        M.tellSubst u t
                (True, Nothing) -> M.throwError $ Err.SkolemNotPolymorphic (pPrint u) (pPrint t)
                (True, Just tTv)
                    | tTv `TV.member` allSkolems -> M.throwError $ Err.SkolemsUnified (pPrint u) (pPrint t)
                    | otherwise ->
                      -- Binding a skolem(u) to a non-skolem type-var
                          do
                              SkolemScope tvAllowedSkolems <- M.getSkolemsInScope tTv
                              unless (u `TV.member` tvAllowedSkolems) $
                                  M.throwError $ Err.SkolemEscapesScope (pPrint u) (pPrint t) (pPrint u)
                              M.tellSubst tTv (TV.lift u)
    where
        tFree = TV.free t
        mtTv = TV.unlift t

class CanSubst t => Unify t where
    unifyGeneric :: t -> t -> Infer ()

closedRecord :: Map T.Tag Type -> T.Row
closedRecord fields = FlatComposite.toComposite (FlatComposite fields Nothing)

unifyFlatToPartial ::
    Subst -> (Map T.Tag Type, T.RowVar) -> Map T.Tag Type ->
    Infer ()
unifyFlatToPartial s (tfields, tname) ufields
    | not (Map.null uniqueTFields) =
        M.throwError $
        Err.TypesDoNotUnity
        (pPrint (FlatComposite.toComposite (FlatComposite tfields (Just tname))))
        (pPrint (closedRecord ufields))
    | otherwise =
            varBind tname $
            Subst.apply s $
            FlatComposite.toComposite $ FlatComposite uniqueUFields Nothing
    where
        uniqueTFields = tfields `Map.difference` ufields
        uniqueUFields = ufields `Map.difference` tfields

unifyFlatPartials ::
    Subst ->
    (Map T.Tag Type, T.RowVar) ->
    (Map T.Tag Type, T.RowVar) ->
    Infer ()
unifyFlatPartials s0 (tfields, tname) (ufields, uname) =
    do
        tScope <- M.getSkolemsInScope tname
        uScope <- M.getSkolemsInScope uname
        restTv <- M.freshInferredVar (tScope `Scope.skolemScopeIntersection` uScope) "r"
        ((), s1) <-
            M.listenSubst $ varBind tname $
            Subst.apply s0 $
            Map.foldrWithKey T.RExtend restTv uniqueUFields
        varBind uname $ Subst.apply (s0 <> s1) $
            Map.foldrWithKey T.RExtend restTv uniqueTFields
    where
        uniqueTFields = tfields `Map.difference` ufields
        uniqueUFields = ufields `Map.difference` tfields

unifyFlatFulls ::
    Map T.Tag Type -> Map T.Tag Type -> Infer ()
unifyFlatFulls tfields ufields
    | Map.keys tfields /= Map.keys ufields =
        M.throwError $
        Err.TypesDoNotUnity
        (pPrint (closedRecord tfields))
        (pPrint (closedRecord ufields))
    | otherwise = pure mempty

unifyChild :: Unify t => t -> t -> StateT Subst Infer ()
unifyChild t u =
    do
        old <- State.get
        ((), s) <- lift $ M.listenSubst $ unifyGeneric (Subst.apply old t) (Subst.apply old u)
        State.put (old <> s)

unifyIntersection :: (Unify a, Ord k) => Map k a -> Map k a -> Infer ()
unifyIntersection tfields ufields =
    (`evalStateT` mempty) . Foldable.sequence_ $
    Map.intersectionWith unifyChild tfields ufields

unifyFlattened :: FlatComposite -> FlatComposite -> Infer ()
unifyFlattened
    (FlatComposite tfields tvar)
    (FlatComposite ufields uvar) =
        do
                ((), s) <- M.listenSubst $ unifyIntersection tfields ufields
                case (tvar, uvar) of
                        (Nothing   , Nothing   ) -> unifyFlatFulls tfields ufields
                        (Just tname, Just uname) -> unifyFlatPartials s (tfields, tname) (ufields, uname)
                        (Just tname, Nothing   ) -> unifyFlatToPartial s (tfields, tname) ufields
                        (Nothing   , Just uname) -> unifyFlatToPartial s (ufields, uname) tfields

dontUnify :: Pretty t => t -> t -> Infer ()
dontUnify x y =
    M.throwError $ Err.TypesDoNotUnity (pPrint x) (pPrint y)

instance Unify Type where
    unifyGeneric (T.TFun l r) (T.TFun l' r') =
        do
            ((), s1) <- M.listenSubst $ unifyGeneric l l'
            unifyGeneric
                (Subst.apply s1 r)
                (Subst.apply s1 r')
    unifyGeneric (T.TInst c0 p0) (T.TInst c1 p1)
        | c0 == c1 && Map.keys p0 == Map.keys p1 = unifyIntersection p0 p1
    unifyGeneric (T.TVar u) t                =  varBind u t
    unifyGeneric t (T.TVar u)                =  varBind u t
    unifyGeneric (T.TRecord x) (T.TRecord y) =  unifyGeneric x y
    unifyGeneric (T.TVariant x)    (T.TVariant y)    =  unifyGeneric x y
    unifyGeneric t1 t2                       =  dontUnify t1 t2

instance Unify T.Row where
    unifyGeneric T.REmpty T.REmpty       =  pure ()
    unifyGeneric (T.RVar u) t            =  varBind u t
    unifyGeneric t (T.RVar u)            =  varBind u t
    unifyGeneric
        t@(T.RExtend f0 t0 r0)
        u@(T.RExtend f1 t1 r1)
        | f0 == f1 =
              do
                  ((), s) <- M.listenSubst $ unifyGeneric t0 t1
                  unifyGeneric (Subst.apply s r0) (Subst.apply s r1)
        | otherwise =
              unifyFlattened
              (FlatComposite.fromComposite t)
              (FlatComposite.fromComposite u)
    unifyGeneric t1 t2                   =  dontUnify t1 t2
