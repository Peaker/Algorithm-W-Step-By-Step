{-# LANGUAGE NoImplicitPrelude #-}
module Lamdu.Infer.Load
    ( Loader(..)
    , loadInfer
    ) where

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (unless)
import           Data.Foldable (traverse_)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Traversable as Traversable
import           Lamdu.Expr.Lens (nextLayer, valGlobals, valNominals)
import           Lamdu.Expr.Nominal (Nominal, nParams, nominalType, _NominalType)
import           Lamdu.Expr.Scheme (Scheme, schemeType)
import           Lamdu.Expr.Type (Type)
import qualified Lamdu.Expr.Type as T
import           Lamdu.Expr.Val (Val)
import qualified Lamdu.Expr.Val as V
import           Lamdu.Infer (Scope, Infer, infer, Payload, Loaded(..), scopeToTypeMap)

import           Prelude.Compat

data Loader m = Loader
    { loadTypeOf :: V.Var -> m Scheme
    , loadNominal :: T.NominalId -> m Nominal
    }

ascKeys :: Map a b -> [a]
ascKeys = map fst . Map.toAscList

validateType :: Monad m => Loader m -> Map T.NominalId Nominal -> Type -> m ()
validateType loader nominals typ =
    do
        validate typ
        typ ^.. nextLayer & traverse_ (validateType loader nominals)
    where
        validate (T.TInst nomId typeArgs) =
            do
                typeParams <-
                    Map.lookup nomId nominals
                    & maybe (loadNominal loader nomId) return
                    <&> nParams
                unless (ascKeys typeArgs == ascKeys typeParams) $
                    fail $ unwords
                    [ "TInst", show nomId, "gives type args", show typeArgs
                    , "but nomId expects", show typeParams
                    ]
        validate _ = return ()

validateLoaded :: Monad m => Loader m -> Loaded -> m ()
validateLoaded loader (Loaded types nominals) =
    (nominals ^.. Lens.folded . nominalType . _NominalType . schemeType) ++
    (types ^.. Lens.folded . schemeType)
    & traverse_ (validateType loader nominals)

loadVal :: Monad m => Loader m -> Scope -> Val a -> m Loaded
loadVal loader scope val =
    do
        loaded <-
            Loaded
            <$> loadMap loadTypeOf (val ^.. valGlobals (Map.keysSet (scopeToTypeMap scope)))
            <*> loadMap loadNominal (val ^.. valNominals)
        validateLoaded loader loaded
        return loaded
    where
        loadMap f x = x & Set.fromList & Map.fromSet (f loader) & Traversable.sequenceA

loadInfer :: Monad m => Loader m -> Scope -> Val a -> m (Infer (Val (Payload, a)))
loadInfer loader scope val =
    loadVal loader scope val
    <&> \loaded -> infer loaded scope val
