{-# LANGUAGE NoImplicitPrelude, RankNTypes, NoMonomorphismRestriction, FlexibleContexts #-}
module Lamdu.Expr.Lens
    -- ValLeaf prisms:
    ( _LHole
    , _LRecEmpty
    , _LAbsurd
    , _LVar
    , _LLiteral
    -- ValBody prisms:
    , _BLeaf
    , _BApp
    , _BLam
    , _BGetField
    , _BRecExtend
    , _BCase
    , _BInject
    , _BFromNom, _BToNom
    -- Leafs
    , valHole    , valBodyHole
    , valVar     , valBodyVar
    , valRecEmpty, valBodyRecEmpty
    , valLiteral , valBodyLiteral
    , valLeafs
    -- Non-leafs
    , valGetField
    , valApply
    , valAbs
    -- Pure vals:
    , pureValBody
    , pureValApply
    --
    , valTags, bodyTags, biTraverseBodyTags
    , valGlobals
    , valNominals
    , compositeTags, compositeFields
    -- Subexpressions:
    , subExprPayloads
    , subExprs
    , payloadsIndexedByPath
    , payloadsOf
    -- Type prisms:
    , _TVar
    , _TRecord
    , _TSum
    , _TFun
    , _TInst
    -- Composite prisms:
    , _CVar
    -- Type traversals:
    , compositeTypes
    , nextLayer
    , typeTIds
    ) where

import           Control.Lens (Traversal', Prism', prism', Iso', iso)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (void)
import           Data.Map (Map)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Lamdu.Expr.Type (Type)
import qualified Lamdu.Expr.Type as T
import qualified Lamdu.Expr.Val as V
import           Lamdu.Expr.Val.Annotated (Val(..))
import qualified Lamdu.Expr.Val.Annotated as Val

import           Prelude.Compat

{-# INLINE compositeTypes #-}
compositeTypes :: Lens.Traversal' (T.Composite p) Type
compositeTypes f (T.CExtend tag typ rest) = T.CExtend tag <$> f typ <*> compositeTypes f rest
compositeTypes _ T.CEmpty = pure T.CEmpty
compositeTypes _ (T.CVar tv) = pure (T.CVar tv)

{-# INLINE nextLayer #-}
-- | Traverse direct types within a type
nextLayer :: Lens.Traversal' Type Type
nextLayer _ (T.TVar tv) = pure (T.TVar tv)
nextLayer f (T.TFun a r) = T.TFun <$> f a <*> f r
nextLayer f (T.TInst tid m) = T.TInst tid <$> Lens.traverse f m
nextLayer f (T.TRecord p) = T.TRecord <$> compositeTypes f p
nextLayer f (T.TSum s) = T.TSum <$> compositeTypes f s

{-# INLINE typeTIds #-}
typeTIds :: Lens.Traversal' Type T.NominalId
typeTIds f (T.TInst tId args) =
    T.TInst <$> f tId <*> Lens.traverse (typeTIds f) args
typeTIds f x = nextLayer (typeTIds f) x

{-# INLINE valApply #-}
valApply :: Traversal' (Val a) (V.Apply (Val a))
valApply = Val.body . _BApp

{-# INLINE valAbs #-}
valAbs :: Traversal' (Val a) (V.Lam (Val a))
valAbs = Val.body . _BLam

{-# INLINE pureValBody #-}
pureValBody :: Iso' (Val ()) (V.Body (Val ()))
pureValBody = iso Val._valBody (Val ())

{-# INLINE pureValApply #-}
pureValApply :: Prism' (Val ()) (V.Apply (Val ()))
pureValApply = pureValBody . _BApp

{-# INLINE valHole #-}
valHole :: Traversal' (Val a) ()
valHole = Val.body . valBodyHole

{-# INLINE valVar #-}
valVar :: Traversal' (Val a) V.Var
valVar = Val.body . valBodyVar

{-# INLINE valRecEmpty #-}
valRecEmpty :: Traversal' (Val a) ()
valRecEmpty = Val.body . valBodyRecEmpty

{-# INLINE valLiteral #-}
valLiteral :: Traversal' (Val a) V.PrimVal
valLiteral = Val.body . valBodyLiteral

{-# INLINE valGetField #-}
valGetField  :: Traversal' (Val a) (V.GetField (Val a))
valGetField = Val.body . _BGetField

{-# INLINE _LHole #-}
_LHole :: Prism' V.Leaf ()
_LHole = prism' (\() -> V.LHole) get
    where
        get V.LHole = Just ()
        get _ = Nothing

{-# INLINE _LRecEmpty #-}
_LRecEmpty :: Prism' V.Leaf ()
_LRecEmpty = prism' (\() -> V.LRecEmpty) get
    where
        get V.LRecEmpty = Just ()
        get _ = Nothing

{-# INLINE _LAbsurd #-}
_LAbsurd :: Prism' V.Leaf ()
_LAbsurd = prism' (\() -> V.LAbsurd) get
    where
        get V.LAbsurd = Just ()
        get _ = Nothing

{-# INLINE _LVar #-}
_LVar :: Prism' V.Leaf V.Var
_LVar = prism' V.LVar get
    where
        get (V.LVar gid) = Just gid
        get _ = Nothing

{-# INLINE _LLiteral #-}
_LLiteral :: Prism' V.Leaf V.PrimVal
_LLiteral = prism' V.LLiteral get
    where
        get (V.LLiteral i) = Just i
        get _ = Nothing

{-# INLINE _BLeaf #-}
-- TODO: _V* -> _B*
_BLeaf :: Prism' (V.Body a) V.Leaf
_BLeaf = prism' V.BLeaf get
    where
        get (V.BLeaf x) = Just x
        get _ = Nothing

{-# INLINE _BApp #-}
_BApp :: Prism' (V.Body a) (V.Apply a)
_BApp = prism' V.BApp get
    where
        get (V.BApp x) = Just x
        get _ = Nothing

{-# INLINE _BLam #-}
_BLam :: Prism' (V.Body a) (V.Lam a)
_BLam = prism' V.BLam get
    where
        get (V.BLam x) = Just x
        get _ = Nothing

{-# INLINE _BGetField #-}
_BGetField :: Prism' (V.Body a) (V.GetField a)
_BGetField = prism' V.BGetField get
    where
        get (V.BGetField x) = Just x
        get _ = Nothing

{-# INLINE _BInject #-}
_BInject :: Prism' (V.Body a) (V.Inject a)
_BInject = prism' V.BInject get
    where
        get (V.BInject x) = Just x
        get _ = Nothing

{-# INLINE _BFromNom #-}
_BFromNom :: Prism' (V.Body a) (V.Nom a)
_BFromNom = prism' V.BFromNom get
    where
        get (V.BFromNom x) = Just x
        get _ = Nothing

{-# INLINE _BToNom #-}
_BToNom :: Prism' (V.Body a) (V.Nom a)
_BToNom = prism' V.BToNom get
    where
        get (V.BToNom x) = Just x
        get _ = Nothing

{-# INLINE _BRecExtend #-}
_BRecExtend :: Prism' (V.Body a) (V.RecExtend a)
_BRecExtend = prism' V.BRecExtend get
    where
        get (V.BRecExtend x) = Just x
        get _ = Nothing

{-# INLINE _BCase #-}
_BCase :: Prism' (V.Body a) (V.Case a)
_BCase = prism' V.BCase get
    where
        get (V.BCase x) = Just x
        get _ = Nothing

{-# INLINE valBodyHole #-}
valBodyHole :: Prism' (V.Body expr) ()
valBodyHole = _BLeaf . _LHole

{-# INLINE valBodyVar #-}
valBodyVar :: Prism' (V.Body expr) V.Var
valBodyVar = _BLeaf . _LVar

{-# INLINE valBodyRecEmpty #-}
valBodyRecEmpty :: Prism' (V.Body expr) ()
valBodyRecEmpty = _BLeaf . _LRecEmpty

{-# INLINE valBodyLiteral #-}
valBodyLiteral :: Prism' (V.Body expr) V.PrimVal
valBodyLiteral = _BLeaf . _LLiteral

{-# INLINE valLeafs #-}
valLeafs :: Traversal' (Val a) V.Leaf
valLeafs f (Val pl body) =
    case body of
    V.BLeaf l -> f l <&> V.BLeaf
    _ -> body & Lens.traverse . valLeafs %%~ f
    <&> Val pl

{-# INLINE _TVar #-}
_TVar :: Prism' Type T.TypeVar
_TVar = prism' T.TVar get
    where
        get (T.TVar x) = Just x
        get _ = Nothing

{-# INLINE _TRecord #-}
_TRecord :: Prism' Type T.Product
_TRecord = prism' T.TRecord get
    where
        get (T.TRecord x) = Just x
        get _ = Nothing

{-# INLINE _TSum #-}
_TSum :: Prism' Type T.Sum
_TSum = prism' T.TSum get
    where
        get (T.TSum x) = Just x
        get _ = Nothing

{-# INLINE _TFun #-}
_TFun :: Prism' Type (Type, Type)
_TFun = prism' (uncurry T.TFun) get
    where
        get (T.TFun arg res) = Just (arg, res)
        get _ = Nothing

{-# INLINE _TInst #-}
_TInst :: Prism' Type (T.NominalId, Map T.ParamId Type)
_TInst = prism' (uncurry T.TInst) get
    where
        get (T.TInst nomId params) = Just (nomId, params)
        get _ = Nothing

{-# INLINE _CVar #-}
_CVar :: Prism' (T.Composite p) (T.Var (T.Composite p))
_CVar = prism' T.CVar get
    where
        get (T.CVar x) = Just x
        get _ = Nothing

{-# INLINE compositeFields #-}
compositeFields :: Traversal' (T.Composite p) (T.Tag, Type)
compositeFields f (T.CExtend tag typ rest) =
    uncurry T.CExtend <$> f (tag, typ) <*> compositeFields f rest
compositeFields _ r = pure r

{-# INLINE compositeTags #-}
compositeTags :: Traversal' (T.Composite p) T.Tag
compositeTags = compositeFields . Lens._1

{-# INLINE subExprPayloads #-}
subExprPayloads :: Lens.IndexedTraversal (Val ()) (Val a) (Val b) a b
subExprPayloads f val@(Val pl body) =
    Val
    <$> Lens.indexed f (void val) pl
    <*> (Lens.traversed .> subExprPayloads) f body

{-# INLINE subExprs #-}
subExprs :: Lens.Fold (Val a) (Val a)
subExprs =
    Lens.folding f
    where
        f x = x : x ^.. Val.body . Lens.traversed . subExprs

{-# INLINE payloadsIndexedByPath #-}
payloadsIndexedByPath ::
    Lens.IndexedTraversal
    [Val ()]
    (Val a)
    (Val b)
    a b
payloadsIndexedByPath f =
    go []
    where
        go path val@(Val pl body) =
            Val
            <$> Lens.indexed f newPath pl
            <*> Lens.traversed (go newPath) body
            where
                newPath = void val : path

{-# INLINE payloadsOf #-}
payloadsOf ::
    Lens.Fold (V.Body (Val ())) a -> Lens.IndexedTraversal' (Val ()) (Val b) b
payloadsOf body =
    subExprPayloads . Lens.ifiltered predicate
    where
        predicate idx _ = Lens.has (Val.body . body) idx

{-# INLINE biTraverseBodyTags #-}
biTraverseBodyTags ::
    Applicative f =>
    (T.Tag -> f T.Tag) -> (a -> f b) ->
    V.Body a -> f (V.Body b)
biTraverseBodyTags onTag onChild body =
    case body of
    V.BInject (V.Inject t v) ->
        V.BInject <$> (V.Inject <$> onTag t <*> onChild v)
    V.BGetField (V.GetField r t) ->
        V.BGetField <$> (V.GetField <$> onChild r <*> onTag t)
    V.BCase (V.Case t v r) ->
        V.BCase <$> (V.Case <$> onTag t <*> onChild v <*> onChild r)
    V.BRecExtend (V.RecExtend t v r) ->
        V.BRecExtend <$> (V.RecExtend <$> onTag t <*> onChild v <*> onChild r)
    _ -> Lens.traverse onChild body

{-# INLINE bodyTags #-}
bodyTags :: Lens.Traversal' (V.Body a) T.Tag
bodyTags f = biTraverseBodyTags f pure

{-# INLINE valTags #-}
valTags :: Lens.Traversal' (Val a) T.Tag
valTags f = Val.body $ biTraverseBodyTags f (valTags f)

{-# INLINE valGlobals #-}
valGlobals :: Set V.Var -> Lens.Fold (Val a) V.Var
valGlobals scope f (Val pl body) =
    case body of
    V.BLeaf (V.LVar v)
        | Set.member v scope -> V.LVar v & V.BLeaf & pure
        | otherwise -> f v <&> V.LVar <&> V.BLeaf
    V.BLam (V.Lam var lamBody) ->
        valGlobals (Set.insert var scope) f lamBody
        <&> V.Lam var <&> V.BLam
    _ -> body & Lens.traverse . valGlobals scope %%~ f
    <&> Val pl

{-# INLINE valNominals #-}
valNominals :: Lens.Traversal' (Val a) T.NominalId
valNominals f (Val pl body) =
    case body of
    V.BFromNom nom -> onNom nom <&> V.BFromNom
    V.BToNom nom -> onNom nom <&> V.BToNom
    _ -> body & Lens.traverse . valNominals %%~ f
    <&> Val pl
    where
        onNom (V.Nom nomId val) = V.Nom <$> f nomId <*> valNominals f val
