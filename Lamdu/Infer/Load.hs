{-# LANGUAGE NoImplicitPrelude #-}
module Lamdu.Infer.Load
    ( Loader(..)
    , loadInfer
    ) where

import           Prelude.Compat

import           Control.Lens.Operators
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Traversable as Traversable
import           Lamdu.Expr.Lens (valGlobals, valNominals)
import           Lamdu.Expr.Nominal (Nominal)
import           Lamdu.Expr.Scheme (Scheme)
import qualified Lamdu.Expr.Type as T
import           Lamdu.Expr.Val (Val)
import qualified Lamdu.Expr.Val as V
import           Lamdu.Infer (Scope, Infer, infer, Payload, Loaded(..), scopeToTypeMap)

data Loader m = Loader
    { loadTypeOf :: V.Var -> m Scheme
    , loadNominal :: T.NominalId -> m Nominal
    }

loadVal :: Applicative m => Loader m -> Scope -> Val a -> m Loaded
loadVal loader scope val =
    Loaded
    <$> loadMap loadTypeOf (val ^.. valGlobals (Map.keysSet (scopeToTypeMap scope)))
    <*> loadMap loadNominal (val ^.. valNominals)
    where
        loadMap f x = x & Set.fromList & Map.fromSet (f loader) & Traversable.sequenceA

loadInfer :: Applicative m => Loader m -> Scope -> Val a -> m (Infer (Val (Payload, a)))
loadInfer loader scope val =
    loadVal loader scope val
    <&> \loaded -> infer loaded scope val
