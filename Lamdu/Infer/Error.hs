{-# LANGUAGE OverloadedStrings #-}

module Lamdu.Infer.Error
    ( Error(..)
    ) where

import           Lamdu.Expr.Constraints (Constraints)
import qualified Lamdu.Expr.Type as T
import qualified Lamdu.Expr.Val as V
import           Text.PrettyPrint ((<+>), Doc)
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

data Error
    = DuplicateField T.Tag T.Product
    | DuplicateAlt T.Tag T.Sum
    | MissingNominal T.NominalId
    | OccursCheckFail Doc Doc
    | TypesDoNotUnity Doc Doc
    | UnboundVariable V.Var
    | SkolemsUnified Doc Doc
    | SkolemNotPolymorphic Doc Doc
    | UnexpectedSkolemConstraint Constraints
    | SkolemEscapesScope

instance Pretty Error where
    pPrint (DuplicateField t r) =
        "Field" <+> pPrint t <+> "forbidden in record" <+> pPrint r
    pPrint (DuplicateAlt t r) =
        "Alternative" <+> pPrint t <+> "forbidden in sum" <+> pPrint r
    pPrint (MissingNominal i) =
        "Missing nominal:" <+> pPrint i
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
    pPrint SkolemEscapesScope = "Skolem escapes scope"
