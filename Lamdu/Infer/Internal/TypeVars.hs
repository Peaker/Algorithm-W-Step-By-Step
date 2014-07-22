{-# LANGUAGE DeriveGeneric, FlexibleInstances #-}
module Lamdu.Infer.Internal.TypeVars
  ( TypeVars(..)
  , HasVar(..), CompositeHasVar
  , difference
  , Subst(..), substDeleteVars
  , FreeTypeVars(..), NewSubst(..)
  ) where

import Control.Applicative ((<$>))
import Control.DeepSeq (NFData(..))
import Control.DeepSeq.Generics (genericRnf)
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Monoid (Monoid(..))
import Data.Set (Set)
import GHC.Generics (Generic)
import qualified Data.Map as Map
import qualified Data.Map.Utils as MapU
import qualified Data.Set as Set
import qualified Lamdu.Expr as E

data TypeVars = TypeVars (Set (E.TypeVar E.Type)) (Set (E.TypeVar E.ProductType))
  deriving (Eq, Generic)
instance NFData TypeVars where
  rnf = genericRnf
instance Monoid TypeVars where
  mempty = TypeVars mempty mempty
  mappend (TypeVars t0 r0) (TypeVars t1 r1) =
    TypeVars (mappend t0 t1) (mappend r0 r1)

class HasVar t where
  getVars :: TypeVars -> Set (E.TypeVar t)
  newVars :: Set (E.TypeVar t) -> TypeVars
  liftVar :: E.TypeVar t -> t

instance HasVar E.Type where
  getVars (TypeVars vs _) = vs
  newVars vs = TypeVars vs mempty
  liftVar = E.TVar

class CompositeHasVar p where
  compositeGetVars :: TypeVars -> Set (E.TypeVar (E.CompositeType p))
  compositeNewVars :: Set (E.TypeVar (E.CompositeType p)) -> TypeVars

instance CompositeHasVar E.Product where
  compositeGetVars (TypeVars _ vs) = vs
  compositeNewVars vs = TypeVars mempty vs

instance CompositeHasVar p => HasVar (E.CompositeType p) where
  getVars = compositeGetVars
  newVars = compositeNewVars
  liftVar = E.CVar

difference :: TypeVars -> TypeVars -> TypeVars
difference (TypeVars t0 r0) (TypeVars t1 r1) =
  TypeVars (Set.difference t0 t1) (Set.difference r0 r1)

type SubSubst t = Map (E.TypeVar t) t

data Subst = Subst
  { substTypes :: SubSubst E.Type
  , substRecordTypes :: SubSubst E.ProductType
  }

instance Monoid Subst where
  mempty = Subst Map.empty Map.empty
  mappend (Subst t0 r0) s1@(Subst t1 r1) =
    Subst
    (t1 `Map.union` Map.map (applySubst s1) t0)
    (r1 `Map.union` Map.map (applySubst s1) r0)

substDeleteVars :: TypeVars -> Subst -> Subst
substDeleteVars (TypeVars t r) (Subst st sr) =
  Subst (MapU.deleteKeySet t st) (MapU.deleteKeySet r sr)

class FreeTypeVars a where
  freeTypeVars :: a -> TypeVars
  applySubst   :: Subst -> a -> a

instance FreeTypeVars (E.CompositeType E.Product) where
  freeTypeVars E.CEmpty          = mempty
  freeTypeVars (E.CVar n)        = newVars (Set.singleton n)
  freeTypeVars (E.CExtend _ t r) = freeTypeVars t `mappend` freeTypeVars r

  applySubst _ E.CEmpty          = E.CEmpty
  applySubst s (E.CVar n)        = fromMaybe (E.CVar n) $ Map.lookup n (substRecordTypes s)
  applySubst s (E.CExtend n t r) = E.CExtend n (applySubst s t) (applySubst s r)

instance FreeTypeVars E.Type where
  freeTypeVars (E.TVar n)      =  newVars (Set.singleton n)
  freeTypeVars (E.TInst _ p)   =  mconcat $ map freeTypeVars $ Map.elems p
  freeTypeVars (E.TFun t1 t2)  =  freeTypeVars t1 `mappend` freeTypeVars t2
  freeTypeVars (E.TRecord r)   =  freeTypeVars r

  applySubst s (E.TVar n)      = fromMaybe (E.TVar n) $ Map.lookup n (substTypes s)
  applySubst s (E.TInst n p)   = E.TInst n $ applySubst s <$> p
  applySubst s (E.TFun t1 t2)  = E.TFun (applySubst s t1) (applySubst s t2)
  applySubst s (E.TRecord r)   = E.TRecord $ applySubst s r

class FreeTypeVars t => NewSubst t where
  newSubst :: E.TypeVar t -> t -> Subst

instance NewSubst E.Type          where
  newSubst tv t = Subst (Map.singleton tv t) mempty
  {-# INLINE newSubst #-}

instance NewSubst E.ProductType where
  newSubst tv t = Subst mempty (Map.singleton tv t)
  {-# INLINE newSubst #-}
