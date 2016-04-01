{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, GeneralizedNewtypeDeriving #-}
module Lamdu.Infer.Internal.Scope
    ( Scope
    , emptyScope

    , scopeToTypeMap
    , insertTypeOf
    , lookupTypeOf

    , SkolemScope(..), skolemScopeVars, skolemScopeIntersection
    , skolems
    , insertSkolems
    ) where

import           Control.DeepSeq (NFData(..))
import           Control.DeepSeq.Generics (genericRnf)
import qualified Control.Lens as Lens
import           Data.Binary (Binary)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Monoid ((<>))
import           GHC.Generics (Generic)
import           Lamdu.Expr.Type (Type)
import qualified Lamdu.Expr.TypeVars as TV
import qualified Lamdu.Expr.Val as V
import           Lamdu.Infer.Internal.Subst (CanSubst(..))
import qualified Lamdu.Infer.Internal.Subst as Subst
import           Text.PrettyPrint (($+$), (<+>), text, nest, vcat)
import           Text.PrettyPrint.HughesPJClass (Pretty(..))
import           Text.PrettyPrint.Utils (pPrintMap)

import           Prelude.Compat hiding (any)

newtype SkolemScope = SkolemScope { _skolemScopeVars :: TV.TypeVars }
    deriving (Generic, Show, Monoid, NFData, Binary)

instance Pretty SkolemScope where
    pPrint (SkolemScope tvs) = text "Skolems:" <+> pPrint tvs

skolemScopeVars :: Lens.Iso' SkolemScope TV.TypeVars
skolemScopeVars = Lens.iso _skolemScopeVars SkolemScope
{-# INLINE skolemScopeVars #-}

skolemScopeIntersection :: SkolemScope -> SkolemScope -> SkolemScope
skolemScopeIntersection (SkolemScope a) (SkolemScope b) =
    SkolemScope (a `TV.intersection` b)

data Scope = Scope
    { scopeSkolems :: SkolemScope
    , scopeTypeOfVar :: Map V.Var Type
    } deriving (Generic, Show)

instance NFData Scope where rnf = genericRnf
instance Binary Scope

instance Pretty Scope where
    pPrint (Scope skolemScope tvTypes) =
        text "Scope:"
        $+$ nest 4
        ( vcat
          [ pPrint skolemScope
          , pPrintMap tvTypes
          ]
        )

instance TV.Free Scope where
    free (Scope _ env) =
        mconcat $ map TV.free $ Map.elems env

instance CanSubst Scope where
    -- Substs never have skolems in them, assert it?
    apply s (Scope skols env) = Scope skols $ Map.map (Subst.apply s) env

emptyScope :: Scope
emptyScope = Scope mempty Map.empty

lookupTypeOf :: V.Var -> Scope -> Maybe Type
lookupTypeOf key = Map.lookup key . scopeTypeOfVar

skolems :: Scope -> SkolemScope
skolems = scopeSkolems

insertTypeOf :: V.Var -> Type -> Scope -> Scope
insertTypeOf key scheme (Scope skols env) =
    Scope skols $ Map.insert key scheme env

insertSkolems :: TV.TypeVars -> Scope -> Scope
insertSkolems newSkolems (Scope (SkolemScope oldSkolems) env) = Scope (SkolemScope (oldSkolems <> newSkolems)) env

-- TODO: Rename to typeMap
scopeToTypeMap :: Scope -> Map V.Var Type
scopeToTypeMap = scopeTypeOfVar
