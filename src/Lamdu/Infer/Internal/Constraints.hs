{-# LANGUAGE NoImplicitPrelude, BangPatterns #-}
module Lamdu.Infer.Internal.Constraints
    ( applySubst
    ) where

import           Prelude.Compat
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (foldM)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Constraints (Constraints(..), forbiddenFields, CompositeVarsConstraints(..))
import           Lamdu.Infer.Error (Error(DuplicateField, DuplicateAlt))
import           Lamdu.Infer.Internal.Subst (Subst(..))

applySubst ::
    Subst -> Constraints ->
    Either Error ({-additions-}Constraints, Constraints)
applySubst (Subst _ rtvSubsts stvSubsts) (Constraints prodC sumC) =
    do
        (prodCAdditions, prodC') <- applySubstCompositeConstraints DuplicateField rtvSubsts prodC
        (sumCAdditions, sumC') <- applySubstCompositeConstraints DuplicateAlt stvSubsts sumC
        pure
            ( Constraints prodCAdditions sumCAdditions
            , Constraints prodC' sumC'
            )

-- When substituting a composite variable, we need to carry
-- its old constraints on the new variable. This may fail,
-- or generate new constraints. This function returns the new
-- constraint map with the substititions AND the map of "new"
-- constraints which are the old constraints carried to new variables.
applySubstCompositeConstraints ::
    (T.Tag -> T.Composite t -> err) ->
    Map (T.Var (T.Composite t)) (T.Composite t) ->
    CompositeVarsConstraints t ->
    Either err (CompositeVarsConstraints t, CompositeVarsConstraints t)
applySubstCompositeConstraints fieldForbidden rtvSubsts (CompositeVarsConstraints m) =
    foldM subst (mempty, m) (Map.toList m)
    <&> Lens.both %~ CompositeVarsConstraints
    where
        subst (!added, !oldMap) (var, constraints) =
            case Map.lookup var rtvSubsts of
            Nothing -> Right (added, oldMap)
            Just recType ->
                -- We have a constraint "var : constraints" and we're
                -- substituting "var" with "recType". Carry the old
                -- constraints into the tail of "recType"
                go recType
                where
                    go T.CEmpty =
                        -- There is no tail to carry the constraint to, we've
                        -- enforced it and now we can just delete it
                        Right (added, Map.delete var oldMap)
                    go (T.CVar newVar) =
                        -- All Map.inserts go into the "added" map so we have a list
                        -- of added constraints.
                        -- Here we carry the old "constraints" constraint into the tail
                        -- of "recType"
                        Right
                        ( Map.insert newVar constraints added
                        , Map.insert newVar constraints oldMap
                        )
                    go (T.CExtend field _ rest)
                        | constraints ^. forbiddenFields . Lens.contains field = Left $ fieldForbidden field recType
                        | otherwise = go rest
