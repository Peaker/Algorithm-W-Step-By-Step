{-# LANGUAGE DeriveFunctor, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}
module Lamdu.Infer.Internal.Monad
  ( Results(..), emptyResults
  , deleteResultsVars

  , InferState(..)
  , Infer, run
  , tell, tellSubst, tellConstraint, tellConstraints
  , listen, listenNoTell
  , newInferredVar, newInferredVarName
  ) where

import Control.Applicative (Applicative(..))
import Control.Monad.Except (MonadError(..))
import Control.Monad.State (MonadState(..))
import Data.Monoid (Monoid(..))
import Data.String (IsString(..))
import Lamdu.Infer.Internal.Constraints (Constraints(..))
import Lamdu.Infer.Internal.TypeVars (TypeVars)
import qualified Control.Monad as Monad
import qualified Control.Monad.State as State
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Lamdu.Expr as E
import qualified Lamdu.Infer.Internal.Constraints as Constraints
import qualified Lamdu.Infer.Internal.FreeTypeVars as FreeTypeVars

data InferState = InferState { inferSupply :: Int }

data Results = Results
  { subst :: FreeTypeVars.Subst
  , constraints :: Constraints
  }

emptyResults :: Results
emptyResults = Results mempty mempty
{-# INLINE emptyResults #-}

appendResults :: Results -> Results -> Either String Results
appendResults (Results s0 c0) (Results s1 c1) =
  do
    c0' <- Constraints.applySubst s1 c0
    return $ Results (mappend s0 s1) (mappend c0' c1)
{-# INLINE appendResults #-}

deleteResultsVars :: TypeVars -> Results -> Results
deleteResultsVars vs (Results s c) =
  Results
  (FreeTypeVars.substDeleteVars vs s)
  (Constraints.constraintDeleteVars vs c)

newtype Infer a = Infer { runInfer :: InferState -> Either String (a, Results, InferState) }
  deriving Functor

instance Monad Infer where
  return x = Infer $ \s -> Right (x, emptyResults, s)
  {-# INLINE return #-}
  Infer x >>= f =
    Infer $ \s ->
    do
      (y, w0, s0) <- x s
      (z, w1, s1) <- runInfer (f y) s0
      w <- appendResults w0 w1
      Right (z, w, s1)
  {-# INLINE (>>=) #-}

instance Applicative Infer where
  pure = return
  {-# INLINE pure #-}
  (<*>) = Monad.ap
  {-# INLINE (<*>) #-}

instance MonadState InferState Infer where
  get = Infer $ \s -> Right (s, emptyResults, s)
  put s = Infer $ const $ Right ((), emptyResults, s)

instance MonadError [Char] Infer where
  throwError = Infer . const . Left
  catchError (Infer x) f =
    Infer $ \s ->
    case x s of
    Left e -> runInfer (f e) s
    Right r -> Right r

run :: Infer a -> Either String (a, Results)
run (Infer t) =
  do
    (r, w, _) <- t InferState{inferSupply = 0}
    Right (r, w)

tell :: Results -> Infer ()
tell w = Infer $ \s -> Right ((), w, s)
{-# INLINE tell #-}

tellSubst :: FreeTypeVars.NewSubst t => E.VarOf t -> t -> Infer ()
tellSubst v t =
  tell $ emptyResults
  { subst = FreeTypeVars.newSubst v t }

tellConstraints :: Constraints -> Infer ()
tellConstraints x = tell $ emptyResults { constraints = x }

tellConstraint :: E.RecordTypeVar -> E.Tag -> Infer ()
tellConstraint v tag = tellConstraints $ Constraints $ Map.singleton v (Set.singleton tag)

listen :: Infer a -> Infer (a, Results)
listen (Infer act) =
  Infer $ \s0 ->
  do
    (y, w, s1) <- act s0
    Right ((y, w), w, s1)
{-# INLINE listen #-}

-- Duplicate of listen because building one on top of the other has a
-- large (~15%) performance penalty.
listenNoTell :: Infer a -> Infer (a, Results)
listenNoTell (Infer act) =
  Infer $ \s0 ->
  do
    (y, w, s1) <- act s0
    Right ((y, w), emptyResults, s1)
{-# INLINE listenNoTell #-}

newInferredVarName :: IsString v => String -> Infer v
newInferredVarName prefix =
  do  s <- State.get
      State.put s{inferSupply = inferSupply s + 1}
      return $ fromString $ prefix ++ show (inferSupply s)

newInferredVar :: E.TypePart t => String -> Infer t
newInferredVar = fmap E.liftVar . newInferredVarName
