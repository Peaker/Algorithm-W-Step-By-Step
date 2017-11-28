{-# LANGUAGE NoImplicitPrelude #-}
module Lamdu.Infer.Internal.Scheme
    ( makeScheme
    , instantiateWithRenames
    , instantiate
    ) where

import           Control.Lens.Operators
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Lamdu.Calc.Type (Type)
import qualified Lamdu.Calc.Type as T
import qualified Lamdu.Calc.Type.Constraints as Constraints
import           Lamdu.Calc.Type.Scheme (Scheme(..))
import qualified Lamdu.Calc.Type.Scheme as Scheme
import           Lamdu.Calc.Type.Vars (TypeVars(..))
import qualified Lamdu.Calc.Type.Vars as TV
import           Lamdu.Infer.Internal.Monad (InferCtx)
import qualified Lamdu.Infer.Internal.Monad as M
import           Lamdu.Infer.Internal.Scope (SkolemScope)
import qualified Lamdu.Infer.Internal.Subst as Subst

import           Prelude.Compat

{-# INLINE makeScheme #-}
makeScheme :: M.Context -> Type -> Scheme
makeScheme = Scheme.make . M._constraints . M._ctxResults

{-# INLINE mkInstantiateSubstPart #-}
mkInstantiateSubstPart ::
    (M.VarKind t, Monad m) => SkolemScope -> String -> Set (T.Var t) -> InferCtx m (Map (T.Var t) (T.Var t))
mkInstantiateSubstPart skolemScope prefix =
    fmap Map.fromList . mapM f . Set.toList
    where
        f oldVar =
            do
                freshVarExpr <- M.freshInferredVarName skolemScope prefix
                return (oldVar, freshVarExpr)


{-# INLINE instantiateWithRenames #-}
instantiateWithRenames :: Monad m => SkolemScope -> Scheme -> InferCtx m (TV.Renames, Type)
instantiateWithRenames skolemScope (Scheme (TypeVars tv rv sv) constraints t) =
    do
        typeVarSubsts <- mkInstantiateSubstPart skolemScope "i" tv
        recordSubsts <- mkInstantiateSubstPart skolemScope "k" rv
        sumSubsts <- mkInstantiateSubstPart skolemScope "s" sv
        let renames = TV.Renames typeVarSubsts recordSubsts sumSubsts
        let subst = Subst.fromRenames renames
        let constraints' = Constraints.applyRenames renames constraints
        -- Avoid tell for these new constraints, because they refer to
        -- fresh variables, no need to apply the ordinary expensive
        -- and error-emitting tell
        M.Infer $ M.ctxResults . M.constraints <>= constraints'
        return (renames, Subst.apply subst t)

{-# INLINE instantiate #-}
instantiate :: Monad m => SkolemScope -> Scheme -> InferCtx m Type
instantiate skolemScope scheme = fmap snd (instantiateWithRenames skolemScope scheme)
