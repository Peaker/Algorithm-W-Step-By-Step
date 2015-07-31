{-# LANGUAGE NoImplicitPrelude #-}
module Lamdu.Infer.Internal.Scheme
    ( makeScheme
    , instantiateWithRenames
    , instantiate
    , generalize
    , applyRenames
    ) where

import           Prelude.Compat

import           Control.Lens.Operators
import           Control.Monad (liftM)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Lamdu.Expr.Constraints (Constraints)
import qualified Lamdu.Expr.Constraints as Constraints
import           Lamdu.Expr.Scheme (Scheme(..))
import qualified Lamdu.Expr.Scheme as Scheme
import           Lamdu.Expr.Type (Type)
import qualified Lamdu.Expr.Type as T
import           Lamdu.Expr.TypeVars (TypeVars(..))
import qualified Lamdu.Expr.TypeVars as TV
import           Lamdu.Infer.Internal.Monad (InferCtx)
import qualified Lamdu.Infer.Internal.Monad as M
import           Lamdu.Infer.Internal.Scope (SkolemScope)
import qualified Lamdu.Infer.Internal.Subst as Subst

{-# INLINE makeScheme #-}
makeScheme :: M.Context -> Type -> Scheme
makeScheme = Scheme.make . M._constraints . M._ctxResults

{-# INLINE mkInstantiateSubstPart #-}
mkInstantiateSubstPart ::
    (M.VarKind t, Monad m) => SkolemScope -> String -> Set (T.Var t) -> InferCtx m (Map (T.Var t) (T.Var t))
mkInstantiateSubstPart skolemScope prefix =
    liftM Map.fromList . mapM f . Set.toList
    where
        f oldVar =
            do
                freshVarExpr <- M.freshInferredVarName skolemScope prefix
                return (oldVar, freshVarExpr)

generalize :: TypeVars -> Constraints -> Type -> Scheme
generalize outerTVs innerConstraints innerType =
    Scheme tvs (Constraints.intersect tvs innerConstraints) innerType
    where
        tvs = TV.free innerType `TV.difference` outerTVs

{-# INLINE instantiateWithRenames #-}
instantiateWithRenames :: Monad m => SkolemScope -> Scheme -> InferCtx m (TV.Renames, Type)
instantiateWithRenames skolemScope (Scheme (TypeVars tv rv sv) constraints t) =
    do
        typeVarSubsts <- mkInstantiateSubstPart skolemScope "i" tv
        recordSubsts <- mkInstantiateSubstPart skolemScope "k" rv
        sumSubsts <- mkInstantiateSubstPart skolemScope "s" sv
        let renames = TV.Renames typeVarSubsts recordSubsts sumSubsts
        let subst = Subst.fromRenames renames
            constraints' = Constraints.applyRenames renames constraints
        -- Avoid tell for these new constraints, because they refer to
        -- fresh variables, no need to apply the ordinary expensive
        -- and error-emitting tell
        M.Infer $ M.ctxResults . M.constraints <>= constraints'
        return (renames, Subst.apply subst t)

{-# INLINE instantiate #-}
instantiate :: Monad m => SkolemScope -> Scheme -> InferCtx m Type
instantiate skolemScope scheme = liftM snd (instantiateWithRenames skolemScope scheme)

{-# INLINE applyRenames #-}
applyRenames :: TV.Renames -> Scheme -> Scheme
applyRenames renames (Scheme forAll constraints typ) =
    Scheme
    (TV.applyRenames renames forAll)
    (Constraints.applyRenames renames constraints)
    (Subst.apply (Subst.fromRenames renames) typ)
