{-# LANGUAGE NoImplicitPrelude, BangPatterns, DeriveFunctor #-}
module Lamdu.Infer.Internal.Constraints
    ( Substituted(..), applySubst
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (foldM)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Constraints (Constraints(..))
import qualified Lamdu.Calc.Type.Constraints as Constraints
import           Lamdu.Infer.Error (Error(DuplicateField, DuplicateAlt))
import           Lamdu.Infer.Internal.Subst (Subst(..))

import           Prelude.Compat

data Substituted c = Substituted
    { newConstraints :: c
    -- ^ Constraints added as a result of applying substititions to
    -- the old constraints
    , allConstraints :: c
    } deriving Functor

applySubst ::
    Subst -> Constraints -> Either Error (Substituted Constraints)
applySubst (Subst _ rtvSubsts stvSubsts) (Constraints prodC sumC) =
    do
        Substituted prodCAdditions prodC' <-
            applySubstCompositeConstraints DuplicateField rtvSubsts prodC
        Substituted sumCAdditions sumC' <-
            applySubstCompositeConstraints DuplicateAlt stvSubsts sumC
        Substituted
            { newConstraints = Constraints prodCAdditions sumCAdditions
            , allConstraints = Constraints prodC' sumC'
            } & pure

-- When substituting a composite variable, we need to carry
-- its old constraints on the new variable. This may fail,
-- or generate new constraints. This function returns the new
-- constraint map with the substititions AND the map of "new"
-- constraints which are the old constraints carried to new variables.
applySubstCompositeConstraints ::
    (T.Tag -> T.Composite t -> err) ->
    Map (T.Var (T.Composite t)) (T.Composite t) ->
    Constraints.CompositeVars t ->
    Either err (Substituted (Constraints.CompositeVars t))
applySubstCompositeConstraints fieldForbidden rtvSubsts (Constraints.CompositeVars m) =
    foldM subst (Substituted mempty m) (Map.toList m)
    <&> fmap Constraints.CompositeVars
    where
        subst s@(Substituted !added !oldMap) (var, constraints) =
            case Map.lookup var rtvSubsts of
            Nothing -> Right s
            Just recType ->
                -- We have a constraint "var : constraints" and we're
                -- substituting "var" with "recType". Carry the old
                -- constraints into the tail of "recType"
                go recType
                where
                    go T.CEmpty =
                        -- There is no tail to carry the constraint to, we've
                        -- enforced it and now we can just delete it
                        Substituted added (Map.delete var oldMap)
                        & Right
                    go (T.CVar newVar) =
                        -- All Map.inserts go into the "added" map so we have a list
                        -- of added constraints.
                        -- Here we carry the old "constraints" constraint into the tail
                        -- of "recType"
                        Substituted
                        (Map.insert newVar constraints added)
                        (Map.insert newVar constraints oldMap)
                        & Right
                    go (T.CExtend field _ rest)
                        | constraints ^. Constraints.forbiddenFields . Lens.contains field =
                            Left $ fieldForbidden field recType
                        | otherwise = go rest
