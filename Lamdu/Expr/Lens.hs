{-# LANGUAGE NoImplicitPrelude, RankNTypes, NoMonomorphismRestriction, FlexibleContexts #-}
module Lamdu.Expr.Lens
    ( -- Leafs
      valHole    , valBodyHole
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
    -- Type traversals:
    , compositeTypes
    , nextLayer
    , typeTIds
    , typeTags
    , constraintsTags
    , compositeVarConstraintsTags
    ) where

import           Control.Lens (Traversal', Prism', Iso', iso)
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (void)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Lamdu.Calc.Type (Type)
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Constraints (CompositeVarConstraints(..), Constraints(..))
import qualified Lamdu.Calc.Val as V
import           Lamdu.Calc.Val.Annotated (Val(..))
import qualified Lamdu.Calc.Val.Annotated as Val

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

{-# INLINE typeTags #-}
typeTags :: Lens.Traversal' Type T.Tag
typeTags f (T.TRecord composite) = T.TRecord <$> compositeTags f composite
typeTags f (T.TSum composite) = T.TSum <$> compositeTags f composite
typeTags f x = nextLayer (typeTags f) x

compositeVarConstraintsTags :: Traversal' (CompositeVarConstraints t) (Set T.Tag)
compositeVarConstraintsTags f (CompositeVarConstraints m) =
    CompositeVarConstraints <$> Lens.traverse f m

constraintsTags :: Traversal' Constraints (Set T.Tag)
constraintsTags f (Constraints productCs sumCs) =
    Constraints
    <$> compositeVarConstraintsTags f productCs
    <*> compositeVarConstraintsTags f sumCs

{-# INLINE valApply #-}
valApply :: Traversal' (Val a) (V.Apply (Val a))
valApply = Val.body . V._BApp

{-# INLINE valAbs #-}
valAbs :: Traversal' (Val a) (V.Lam (Val a))
valAbs = Val.body . V._BLam

{-# INLINE pureValBody #-}
pureValBody :: Iso' (Val ()) (V.Body (Val ()))
pureValBody = iso Val._valBody (Val ())

{-# INLINE pureValApply #-}
pureValApply :: Prism' (Val ()) (V.Apply (Val ()))
pureValApply = pureValBody . V._BApp

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
valGetField = Val.body . V._BGetField

{-# INLINE valBodyHole #-}
valBodyHole :: Prism' (V.Body expr) ()
valBodyHole = V._BLeaf . V._LHole

{-# INLINE valBodyVar #-}
valBodyVar :: Prism' (V.Body expr) V.Var
valBodyVar = V._BLeaf . V._LVar

{-# INLINE valBodyRecEmpty #-}
valBodyRecEmpty :: Prism' (V.Body expr) ()
valBodyRecEmpty = V._BLeaf . V._LRecEmpty

{-# INLINE valBodyLiteral #-}
valBodyLiteral :: Prism' (V.Body expr) V.PrimVal
valBodyLiteral = V._BLeaf . V._LLiteral

{-# INLINE valLeafs #-}
valLeafs :: Traversal' (Val a) V.Leaf
valLeafs f (Val pl body) =
    case body of
    V.BLeaf l -> f l <&> V.BLeaf
    _ -> body & Lens.traverse . valLeafs %%~ f
    <&> Val pl

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
