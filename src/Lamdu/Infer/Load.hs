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
import           Lamdu.Calc.Term (Val)
import qualified Lamdu.Calc.Term as V
import           Lamdu.Calc.Type (Type)
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Nominal (Nominal, nomParams, nomType, _NominalType)
import           Lamdu.Calc.Type.Scheme (Scheme, schemeType)
import           Lamdu.Expr.Lens (nextLayer, valGlobals, valNominals)
import           Lamdu.Infer (Scope, Infer, infer, Payload, Dependencies(..), scopeToTypeMap)

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
                    & maybe (loadNominal loader nomId) pure
                    <&> (^. nomParams)
                unless (ascKeys typeArgs == ascKeys typeParams) $
                    fail $ unwords
                    [ "TInst", show nomId, "gives type args", show typeArgs
                    , "but nomId expects", show typeParams
                    ]
        validate _ = pure ()

validateLoaded :: Monad m => Loader m -> Dependencies -> m ()
validateLoaded loader (Deps types nominals) =
    (nominals ^.. Lens.folded . nomType . _NominalType . schemeType) ++
    (types ^.. Lens.folded . schemeType)
    & traverse_ (validateType loader nominals)

loadVal :: Monad m => Loader m -> Scope -> Val a -> m Dependencies
loadVal loader scope val =
    do
        loaded <-
            Deps
            <$> loadMap loadTypeOf (val ^.. valGlobals (Map.keysSet (scopeToTypeMap scope)))
            <*> loadMap loadNominal (val ^.. valNominals)
        validateLoaded loader loaded
        pure loaded
    where
        loadMap f x = x & Set.fromList & Map.fromSet (f loader) & Traversable.sequenceA

loadInfer :: Monad m => Loader m -> Scope -> Val a -> m (Infer (Val (Payload, a)))
loadInfer loader scope val =
    loadVal loader scope val
    <&> \loaded -> infer loaded scope val
