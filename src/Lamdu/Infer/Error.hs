{-# LANGUAGE OverloadedStrings #-}

module Lamdu.Infer.Error
    ( Error(..)
    ) where

import qualified Lamdu.Calc.Term as V
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Constraints (Constraints)
import           Text.PrettyPrint ((<+>), Doc)
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

data Error
    = DuplicateField T.Tag T.Record
    | DuplicateAlt T.Tag T.Variant
    | AccessOpaqueNominal T.NominalId
    | MissingNominal T.NominalId
    | OccursCheckFail Doc Doc
    | TypesDoNotUnity Doc Doc
    | UnboundVariable V.Var
    | SkolemsUnified Doc Doc
    | SkolemNotPolymorphic Doc Doc
    | UnexpectedSkolemConstraint Constraints
    | SkolemEscapesScope Doc Doc Doc

instance Pretty Error where
    pPrint (DuplicateField t r) =
        "Field" <+> pPrint t <+> "forbidden in record" <+> pPrint r
    pPrint (DuplicateAlt t r) =
        "Alternative" <+> pPrint t <+> "forbidden in variant" <+> pPrint r
    pPrint (MissingNominal i) =
        "Missing nominal:" <+> pPrint i
    pPrint (AccessOpaqueNominal i) =
        "Accessing opaque nominal:" <+> pPrint i
    pPrint (OccursCheckFail v t) =
        "Occurs check fails:" <+> v <+> "vs." <+> t
    pPrint (UnboundVariable v) =
        "Unbound variable:" <+> pPrint v
    pPrint (TypesDoNotUnity x y) =
        "Types do not unify" <+> x <+> "vs." <+> y
    pPrint (SkolemsUnified x y) =
        "Two skolems unified" <+> x <+> "vs." <+> y
    pPrint (SkolemNotPolymorphic x y) =
        "Skolem" <+> x <+> "unified with non-polymorphic type" <+> y
    pPrint (UnexpectedSkolemConstraint constraints) =
        "Unexpected constraint on skolem[s] " <+> pPrint constraints
    pPrint (SkolemEscapesScope u v unallowedSkolems) =
        "Skolem escapes scope when unifying" <+> u <+> " & " <+> v <+>
        " unallowed skolems: " <+> unallowedSkolems
