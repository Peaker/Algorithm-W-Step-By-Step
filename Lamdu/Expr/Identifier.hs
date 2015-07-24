{-# LANGUAGE NoImplicitPrelude, DeriveGeneric, GeneralizedNewtypeDeriving #-}
module Lamdu.Expr.Identifier
    ( Identifier(..)
    ) where

import           Prelude.Compat

import           Control.DeepSeq (NFData(..))
import           Control.DeepSeq.Generics (genericRnf)
import           Data.Binary (Binary)
import           Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BS
import           Data.Hashable (Hashable)
import           Data.String (IsString(..))
import           GHC.Generics (Generic)
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

newtype Identifier = Identifier ByteString
    deriving (Eq, Ord, Generic, Show, Binary, Hashable)
instance NFData Identifier    where rnf = genericRnf
instance IsString Identifier  where fromString = Identifier . fromString
instance Pretty Identifier    where pPrint (Identifier x) = PP.text $ BS.unpack x
