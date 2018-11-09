{-# LANGUAGE NoImplicitPrelude, BangPatterns #-}
module Lamdu.Infer.Internal.Constraints
    ( applySubst
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (foldM)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Constraints (Constraints(..), CompositeVarConstraints(..))
import           Lamdu.Infer.Error (Error(DuplicateField, DuplicateAlt))
import           Lamdu.Infer.Internal.Subst (Subst(..))

import           Prelude.Compat

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

applySubstCompositeConstraints ::
    (T.Tag -> T.Composite t -> err) ->
    Map (T.Var (T.Composite t)) (T.Composite t) ->
    CompositeVarConstraints t ->
    Either err (CompositeVarConstraints t, CompositeVarConstraints t)
applySubstCompositeConstraints fieldForbidden rtvSubsts (CompositeVarConstraints m) =
    foldM nextConstraints (mempty, m) (Map.toList m)
    <&> Lens.both %~ CompositeVarConstraints
    where
        nextConstraints (!added, !oldMap) (var, forbidden) =
            case Map.lookup var rtvSubsts of
            Nothing -> Right (added, oldMap)
            Just recType ->
                go recType
                where
                    go T.CEmpty =
                        Right (added, Map.delete var oldMap)
                    go (T.CVar newVar) =
                        Right (Map.insert newVar forbidden added, Map.insert newVar forbidden oldMap)
                    go (T.CExtend f _ rest)
                        | Set.member f forbidden = Left $ fieldForbidden f recType
                        | otherwise              = go rest
