{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, TemplateHaskell #-}
module Lamdu.Expr.Nominal
    ( Nominal(..), nominalType
    , NominalType(..), _NominalType, _OpaqueNominal
    , apply
    ) where

import           Control.DeepSeq (NFData(..))
import           Control.DeepSeq.Generics (genericRnf)
import           Control.Lens (Lens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Data.Binary (Binary)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           GHC.Generics (Generic)
import           Lamdu.Expr.Scheme (Scheme)
import           Lamdu.Expr.Type (Type)
import qualified Lamdu.Expr.Type as T
import qualified Lamdu.Infer.Internal.Subst as Subst

import           Prelude.Compat

data NominalType = NominalType Scheme | OpaqueNominal
    deriving (Generic, Show)
instance NFData NominalType where rnf = genericRnf
instance Binary NominalType

Lens.makePrisms ''NominalType

data Nominal = Nominal
    { nParams :: Map T.ParamId T.TypeVar
    , nType :: NominalType
    } deriving (Generic, Show)
instance NFData Nominal where rnf = genericRnf
instance Binary Nominal

nominalType :: Lens' Nominal NominalType
nominalType f (Nominal params typ) = f typ <&> \typ' -> Nominal params typ'

-- errorizes if the map mismatches the map in the Nominal
apply :: Map T.ParamId Type -> Nominal -> NominalType
apply m (Nominal params scheme) =
    scheme & _NominalType %~ Subst.apply subst
    where
        subst = mempty { Subst.substTypes = Map.mapKeys (`find` params) m }
        find k =
            fromMaybe (error "Nominal.instantiate with wrong param map") .
            Map.lookup k
