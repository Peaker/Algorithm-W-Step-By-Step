{-# LANGUAGE NoImplicitPrelude #-}
module Data.Map.Utils
    ( differenceSet
    ) where

import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)

import           Prelude.Compat

differenceSet :: Ord k => Map k a -> Set k -> Map k a
differenceSet m = Map.difference m . Map.fromSet (const ())
