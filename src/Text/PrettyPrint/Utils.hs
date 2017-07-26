{-# LANGUAGE NoImplicitPrelude #-}
module Text.PrettyPrint.Utils
    ( pPrintMap
    ) where

import           Data.Map (Map)
import qualified Data.Map as Map
import           Text.PrettyPrint (Doc, text, vcat, (<+>))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

import           Prelude.Compat

pPrintMap :: (Pretty k, Pretty v) => Map k v -> Doc
pPrintMap =
    vcat . map prettyPair . Map.toList
    where
        prettyPair (k, v) = pPrint k <+> text ", " <+> pPrint v
