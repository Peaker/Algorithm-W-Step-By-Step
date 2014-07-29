{-# LANGUAGE DeriveGeneric #-}
module Lamdu.Infer.Internal.Scheme
  ( Scheme(..)
  , makeScheme
  , instantiate
  ) where

import Control.Applicative ((<$>))
import Control.DeepSeq (NFData(..))
import Control.DeepSeq.Generics (genericRnf)
import Data.Map (Map)
import Data.Monoid (Monoid(..))
import Data.Set (Set)
import Data.String (IsString(..))
import GHC.Generics (Generic)
import Lamdu.Infer.Internal.Constraints (Constraints(..))
import Lamdu.Infer.Internal.Monad (Infer)
import Lamdu.Infer.Internal.TypeVars (applySubst, TypeVars(..), HasVar(..))
import Text.PrettyPrint ((<+>), (<>))
import Text.PrettyPrint.HughesPJClass (Pretty(..), prettyParen)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Lamdu.Expr as E
import qualified Lamdu.Infer.Internal.Constraints as Constraints
import qualified Lamdu.Infer.Internal.Monad as M
import qualified Lamdu.Infer.Internal.TypeVars as TypeVars
import qualified Text.PrettyPrint as PP

data Scheme = Scheme
  { schemeForAll :: TypeVars
  , schemeConstraints :: Constraints
  , schemeType :: E.Type
  } deriving (Generic)

instance NFData Scheme where
  rnf = genericRnf

instance Pretty Scheme where
  pPrintPrec lvl prec (Scheme vars@(TypeVars tv rv) constraints t)  =
    prettyParen (0 < prec) $
    forallStr <+> constraintsStr <+> pPrintPrec lvl 0 t
    where
      forallStr
        | mempty == vars = mempty
        | otherwise =
          PP.text "forall" <+>
          PP.hsep (map pPrint (Set.toList tv) ++ map pPrint (Set.toList rv)) <>
          PP.text "."
      constraintsStr
        | mempty == constraints = mempty
        | otherwise = pPrint constraints <+> PP.text "=>"

makeScheme :: E.Type -> Infer Scheme
makeScheme t = do
  c <- M.getConstraints
  return $ Scheme freeVars (Constraints.intersect freeVars c) t
  where
    freeVars = TypeVars.free t

mkInstantiateSubstPart :: (IsString v, Ord v) => String -> Set v -> Infer (Map v v)
mkInstantiateSubstPart prefix =
  fmap Map.fromList . mapM f . Set.toList
  where
    f oldVar =
      do
        newVarExpr <- M.newInferredVarName prefix
        return (oldVar, newVarExpr)

instantiate :: Scheme -> Infer E.Type
instantiate (Scheme (TypeVars tv rv) constraints t) =
  do
    recordSubsts <- mkInstantiateSubstPart "k" rv
    subst <-
      (`TypeVars.Subst` fmap liftVar recordSubsts) .
      fmap liftVar
      <$> mkInstantiateSubstPart "i" tv
    M.tellConstraints $ Constraints.applyRenames recordSubsts constraints
    return $ applySubst subst t
