{-# LANGUAGE NoImplicitPrelude, FlexibleInstances #-}
{-# OPTIONS -fno-warn-orphans #-} -- Arbitrary E.Val
module Lamdu.Expr.Val.Arbitrary
    ( Name(..)
    ) where

import           Prelude.Compat hiding (any)

import           Control.Lens (Lens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad (replicateM, join)
import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Trans.Reader (ReaderT, runReaderT)
import qualified Control.Monad.Trans.Reader as Reader
import           Control.Monad.Trans.State (StateT, evalStateT)
import qualified Control.Monad.Trans.State as State
import qualified Data.ByteString as BS
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.String (IsString(..))
import           Lamdu.Expr.Identifier (Identifier(..))
import           Lamdu.Expr.Scheme (Scheme)
import qualified Lamdu.Expr.Type as T
import           Lamdu.Expr.Val (Val(..))
import qualified Lamdu.Expr.Val as V
import           Test.QuickCheck (Arbitrary(..), Gen)
import qualified Test.QuickCheck.Gen as Gen

data Env = Env
    { _envScope :: [V.Var]
    , __envGlobals :: Map V.GlobalId Scheme
    }
envScope :: Lens' Env [V.Var]
envScope f e = mkEnv <$> f (_envScope e)
    where
        mkEnv x = e { _envScope = x }

type GenExpr = ReaderT Env (StateT [V.Var] Gen)

liftGen :: Gen a -> GenExpr a
liftGen = lift . lift

next :: GenExpr V.Var
next = lift $ State.gets head <* State.modify tail

arbitraryLam :: Arbitrary a => GenExpr (V.Lam (Val a))
arbitraryLam = do
    par <- next
    V.Lam par {-TODO: Arbitrary constraints on param types??-}
        <$> Reader.local (envScope %~ (par :)) arbitraryExpr

arbitraryRecExtend :: Arbitrary a => GenExpr (V.RecExtend (Val a))
arbitraryRecExtend =
    V.RecExtend <$> liftGen arbitrary <*> arbitraryExpr <*> arbitraryExpr

arbitraryCase :: Arbitrary a => GenExpr (V.Case (Val a))
arbitraryCase =
    V.Case <$> liftGen arbitrary <*> arbitraryExpr <*> arbitraryExpr

arbitraryInject :: Arbitrary a => GenExpr (V.Inject (Val a))
arbitraryInject =
    V.Inject <$> liftGen arbitrary <*> arbitraryExpr

arbitraryGetField :: Arbitrary a => GenExpr (V.GetField (Val a))
arbitraryGetField = V.GetField <$> arbitraryExpr <*> liftGen arbitrary

arbitraryNom :: Arbitrary a => GenExpr (V.Nom (Val a))
arbitraryNom = V.Nom <$> liftGen arbitrary <*> arbitraryExpr

arbitraryApply :: Arbitrary a => GenExpr (V.Apply (Val a))
arbitraryApply = V.Apply <$> arbitraryExpr <*> arbitraryExpr

arbitraryLeaf :: GenExpr V.Leaf
arbitraryLeaf = do
    Env locals globals <- Reader.ask
    join . liftGen . Gen.elements $
        [ V.LLiteralInteger <$> liftGen arbitrary
        , pure V.LHole
        , pure V.LRecEmpty
        , pure V.LAbsurd
        ] ++
        map (pure . V.LVar) locals ++
        map (pure . V.LGlobal) (Map.keys globals)

arbitraryBody :: Arbitrary a => GenExpr (V.Body (Val a))
arbitraryBody =
    join . liftGen . Gen.frequency . (Lens.mapped . _2 %~ pure) $
    [ weight 2  $ V.BAbs         <$> arbitraryLam
    , weight 2  $ V.BRecExtend   <$> arbitraryRecExtend
    , weight 2  $ V.BCase        <$> arbitraryCase
    , weight 2  $ V.BInject      <$> arbitraryInject
    , weight 2  $ V.BGetField    <$> arbitraryGetField
    , weight 2  $ V.BFromNom     <$> arbitraryNom
    , weight 2  $ V.BToNom       <$> arbitraryNom
    , weight 5  $ V.BApp         <$> arbitraryApply
    , weight 17 $ V.BLeaf        <$> arbitraryLeaf
    ]
    where
        weight = (,)

arbitraryExpr :: Arbitrary a => GenExpr (Val a)
arbitraryExpr = Val <$> liftGen arbitrary <*> arbitraryBody

class Name n where
    names :: [n]

exprGen :: Arbitrary a => Map V.GlobalId Scheme -> Gen (Val a)
exprGen globals =
    (`evalStateT` names) .
    (`runReaderT` Env [] globals) $
    arbitraryExpr

instance Name V.Var where
    names = fromString . (: []) <$> ['a'..]

instance Arbitrary Identifier where
    arbitrary = Identifier . BS.pack <$> replicateM 8 arbitrary

instance Arbitrary T.Tag where
    arbitrary = T.Tag <$> arbitrary

instance Arbitrary T.NominalId where
    arbitrary = T.NominalId <$> arbitrary

-- TODO: This instance doesn't know which Definitions exist in the
-- world so avoids DefinitionRef and only has valid ParameterRefs to
-- its own lambdas.
instance Arbitrary a => Arbitrary (Val a) where
    arbitrary = exprGen Map.empty
