{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}

module TestVals
    ( env
    , list
    , factorialVal, euler1Val, solveDepressedQuarticVal
    , factorsVal
    , lambda, lambdaRecord, letItem, recordType
    , eLet
    , litInt, intType
    , listTypePair, boolTypePair, polyIdTypePair, unsafeCoerceTypePair
    , ignoredParamTypePair
    , xGetterPair, xGetterPairConstrained
    ) where

import           Prelude.Compat

import           Control.Lens.Operators
import qualified Data.ByteString.Char8 as BS8
import qualified Data.Map as Map
import           Data.Monoid ((<>))
import qualified Data.Set as Set
import           Lamdu.Expr.Constraints (Constraints(..), CompositeVarConstraints(..))
import           Lamdu.Expr.Nominal (Nominal(..))
import           Lamdu.Expr.Pure (($$), ($$:))
import qualified Lamdu.Expr.Pure as P
import           Lamdu.Expr.Scheme (Scheme(..))
import qualified Lamdu.Expr.Scheme as Scheme
import           Lamdu.Expr.Type (Type, (~>))
import qualified Lamdu.Expr.Type as T
import qualified Lamdu.Expr.TypeVars as TV
import           Lamdu.Expr.Val (Val)
import qualified Lamdu.Expr.Val as V
import           Lamdu.Infer (TypeVars(..), Loaded(..))

{-# ANN module ("HLint: ignore Redundant $" :: String) #-}

-- TODO: $$ to be type-classed for TApp vs BApp
-- TODO: TCon "->" instead of TFun

eLet :: V.Var -> Val () -> (Val () -> Val ()) -> Val ()
eLet name val mkBody = P.app (P.abs name body) val
    where
        body = mkBody $ P.var name

lambda :: V.Var -> (Val () -> Val ()) -> Val ()
lambda varName mkBody = P.abs varName $ mkBody $ P.var varName

lambdaRecord :: [T.Tag] -> ([Val ()] -> Val ()) -> Val ()
lambdaRecord names mkBody =
    lambda "paramsRecord" $ \paramsRec ->
    mkBody $ map (P.getField paramsRec) names

letItem :: V.Var -> Val () -> (Val () -> Val ()) -> Val ()
letItem name val mkBody = lambda name mkBody $$ val

openRecordType :: T.ProductVar -> [(T.Tag, Type)] -> Type
openRecordType tv = T.TRecord . foldr (uncurry T.CExtend) (T.CVar tv)

recordType :: [(T.Tag, Type)] -> Type
recordType = T.TRecord . foldr (uncurry T.CExtend) T.CEmpty

forAll :: [T.TypeVar] -> ([Type] -> Type) -> Scheme
forAll tvs mkType =
    Scheme mempty { typeVars = Set.fromList tvs } mempty $ mkType $ map T.TVar tvs

listTypePair :: (T.NominalId, Nominal)
listTypePair =
    ( "List"
    , Nominal
        { nParams = Map.singleton "elem" tvName
        , nScheme =
            T.CEmpty
            & T.CExtend "[]" (recordType [])
            & T.CExtend ":" (recordType [("head", tv), ("tail", listOf tv)])
            & T.TSum
            & Scheme.mono
        }
    )
    where
        tvName = "a"
        tv = T.TVar tvName

listOf :: Type -> Type
listOf = T.TInst (fst listTypePair) . Map.singleton "elem"

boolType :: Type
boolType = T.TInst (fst boolTypePair) Map.empty

intType :: Type
intType = T.TPrim "Int"

boolTypePair :: (T.NominalId, Nominal)
boolTypePair =
    ( "Bool"
    , Nominal
        { nParams = Map.empty
        , nScheme =
            T.CEmpty
            & T.CExtend "True" (recordType [])
            & T.CExtend "False" (recordType [])
            & T.TSum
            & Scheme.mono
        }
    )

tvA :: T.TypeVar
tvA = "a"

tvB :: T.TypeVar
tvB = "b"

ta :: Type
ta = TV.lift tvA

tb :: Type
tb = TV.lift tvB

polyIdTypePair :: (T.NominalId, Nominal)
polyIdTypePair =
    ( "PolyIdentity"
    , Nominal
        { nParams = Map.empty
        , nScheme =
            Scheme (TV.singleton tvA) mempty $
            ta ~> ta
        }
    )

unsafeCoerceTypePair :: (T.NominalId, Nominal)
unsafeCoerceTypePair =
    ( "UnsafeCoerce"
    , Nominal
        { nParams = Map.empty
        , nScheme =
            Scheme (TV.singleton tvA <> TV.singleton tvB) mempty $
            ta ~> tb
        }
    )

ignoredParamTypePair :: (T.NominalId, Nominal)
ignoredParamTypePair =
    ( "IgnoredParam"
    , Nominal
        { nParams = Map.singleton "res" tvB
        , nScheme =
            Scheme (TV.singleton tvA) mempty $
            ta ~> tb
        }
    )

xGetter :: (T.ProductVar -> Constraints) -> Nominal
xGetter constraints =
    Nominal
    { nParams = Map.empty
    , nScheme =
        Scheme (TV.singleton tvA <> TV.singleton tvRest) (constraints tvRest) $
        openRecordType tvRest [("x", ta)] ~> ta
    }
    where
        tvRest :: T.ProductVar
        tvRest = "rest"

xGetterPair :: (T.NominalId, Nominal)
xGetterPair =
    ( "XGetter"
    , xGetter mempty
    )

xGetterPairConstrained :: (T.NominalId, Nominal)
xGetterPairConstrained =
    ( "XGetterConstrained"
    , xGetter $
      \tvRest ->
          mempty
          { productVarConstraints =
              CompositeVarConstraints $ Map.singleton tvRest $
              Set.fromList ["x", "y"]
          }

    )

maybeOf :: Type -> Type
maybeOf t =
    T.TSum $
    T.CExtend "Nothing" (recordType []) $
    T.CExtend "Just" t T.CEmpty

infixType :: Type -> Type -> Type -> Type
infixType a b c = recordType [("l", a), ("r", b)] ~> c

infixArgs :: Val () -> Val () -> Val ()
infixArgs l r = P.record [("l", l), ("r", r)]

env :: Loaded
env =
    Loaded
    { loadedGlobalTypes =
        Map.fromList
        [ ("fix",    forAll ["a"] $ \ [a] -> (a ~> a) ~> a)
        , ("if",     forAll ["a"] $ \ [a] -> recordType [("condition", boolType), ("then", a), ("else", a)] ~> a)
        , ("==",     forAll ["a"] $ \ [a] -> infixType a a boolType)
        , (">",      forAll ["a"] $ \ [a] -> infixType a a boolType)
        , ("%",      forAll ["a"] $ \ [a] -> infixType a a a)
        , ("*",      forAll ["a"] $ \ [a] -> infixType a a a)
        , ("-",      forAll ["a"] $ \ [a] -> infixType a a a)
        , ("+",      forAll ["a"] $ \ [a] -> infixType a a a)
        , ("/",      forAll ["a"] $ \ [a] -> infixType a a a)
        , ("//",     forAll []    $ \ []  -> infixType intType intType intType)
        , ("sum",    forAll ["a"] $ \ [a] -> listOf a ~> a)
        , ("filter", forAll ["a"] $ \ [a] -> recordType [("from", listOf a), ("predicate", a ~> boolType)] ~> listOf a)
        , (":",      forAll ["a"] $ \ [a] -> recordType [("head", a), ("tail", listOf a)] ~> listOf a)
        , ("[]",     forAll ["a"] $ \ [a] -> listOf a)
        , ("concat", forAll ["a"] $ \ [a] -> listOf (listOf a) ~> listOf a)
        , ("map",    forAll ["a", "b"] $ \ [a, b] -> recordType [("list", listOf a), ("mapping", a ~> b)] ~> listOf b)
        , ("..",     forAll [] $ \ [] -> infixType intType intType (listOf intType))
        , ("||",     forAll [] $ \ [] -> infixType boolType boolType boolType)
        , ("head",   forAll ["a"] $ \ [a] -> listOf a ~> a)
        , ("negate", forAll ["a"] $ \ [a] -> a ~> a)
        , ("sqrt",   forAll ["a"] $ \ [a] -> a ~> a)
        , ("id",     forAll ["a"] $ \ [a] -> a ~> a)
        , ("zipWith",forAll ["a","b","c"] $ \ [a,b,c] ->
                                  (a ~> b ~> c) ~> listOf a ~> listOf b ~> listOf c )
        , ("Just",   forAll ["a"] $ \ [a] -> a ~> maybeOf a)
        , ("Nothing",forAll ["a"] $ \ [a] -> maybeOf a)
        , ("maybe",  forAll ["a", "b"] $ \ [a, b] -> b ~> (a ~> b) ~> maybeOf a ~> b)
        , ("plus1",  forAll [] $ \ [] -> intType ~> intType)
        , ("True",   forAll [] $ \ [] -> boolType)
        , ("False",  forAll [] $ \ [] -> boolType)
        ]
    , loadedNominals =
        Map.fromList
        [ listTypePair
        , boolTypePair
        , polyIdTypePair
        , unsafeCoerceTypePair
        , ignoredParamTypePair
        , xGetterPair
        , xGetterPairConstrained
        ]
    }

list :: [Val ()] -> Val ()
list = foldr cons (P.toNom "List" $ P.inject "[]" P.recEmpty)

cons :: Val () -> Val () -> Val ()
cons h t = P.toNom "List" $ P.inject ":" $ P.record [("head", h), ("tail", t)]

litInt :: Integer -> Val ()
litInt = P.lit "Int" . BS8.pack . show

factorialVal :: Val ()
factorialVal =
    P.global "fix" $$
    lambda "loop"
    ( \loop ->
        lambda "x" $ \x ->
        P.global "if" $$:
        [ ( "condition", P.global "==" $$
                infixArgs x (litInt 0) )
        , ( "then", litInt 1 )
        , ( "else", P.global "*" $$
                infixArgs x (loop $$ (P.global "-" $$ infixArgs x (litInt 1)))
            )
        ]
    )

euler1Val :: Val ()
euler1Val =
    P.global "sum" $$
    ( P.global "filter" $$:
        [ ("from", P.global ".." $$ infixArgs (litInt 1) (litInt 1000))
        , ( "predicate",
                lambda "x" $ \x ->
                P.global "||" $$ infixArgs
                ( P.global "==" $$ infixArgs
                    (litInt 0) (P.global "%" $$ infixArgs x (litInt 3)) )
                ( P.global "==" $$ infixArgs
                    (litInt 0) (P.global "%" $$ infixArgs x (litInt 5)) )
            )
        ]
    )

solveDepressedQuarticVal :: Val ()
solveDepressedQuarticVal =
    lambdaRecord ["e", "d", "c"] $ \[e, d, c] ->
    letItem "solvePoly" (P.global "id")
    $ \solvePoly ->
    letItem "sqrts"
    ( lambda "x" $ \x ->
        letItem "r"
        ( P.global "sqrt" $$ x
        ) $ \r ->
        list [r, P.global "negate" $$ r]
    )
    $ \sqrts ->
    P.global "if" $$:
    [ ("condition", P.global "==" $$ infixArgs d (litInt 0))
    , ( "then",
            P.global "concat" $$
            ( P.global "map" $$:
                [ ("list", solvePoly $$ list [e, c, litInt 1])
                , ("mapping", sqrts)
                ]
            )
        )
    , ( "else",
            P.global "concat" $$
            ( P.global "map" $$:
                [ ( "list", sqrts $$ (P.global "head" $$ (solvePoly $$ list
                        [ P.global "negate" $$ (d %* d)
                        , (c %* c) %- (litInt 4 %* e)
                        , litInt 2 %* c
                        , litInt 1
                        ]))
                    )
                , ( "mapping",
                        lambda "x" $ \x ->
                        solvePoly $$ list
                        [ (c %+ (x %* x)) %- (d %/ x)
                        , litInt 2 %* x
                        , litInt 2
                        ]
                    )
                ]
            )
        )
    ]
    where
        (%+) = inf "+"
        (%-) = inf "-"
        (%*) = inf "*"
        (%/) = inf "/"

inf :: V.GlobalId -> Val () -> Val () -> Val ()
inf str x y = P.global str $$ infixArgs x y

factorsVal :: Val ()
factorsVal =
    fix_ $ \loop ->
    lambdaRecord ["n", "min"] $ \ [n, m] ->
    if_ ((m %* m) %> n) (list [n]) $
    if_ ((n %% m) %== litInt 0)
    (cons m $ loop $$: [("n", n %// m), ("min", m)]) $
    loop $$: [ ("n", n), ("min", m %+ litInt 1) ]
    where
        fix_ f = P.global "fix" $$ lambda "loop" f
        if_ b t f =
            ( nullaryCase "False" f $
              nullaryCase "True" t $
              P.absurd
            ) $$ P.fromNom "Bool" b
        nullaryCase tag handler = P._case tag (defer handler)
        defer = P.lambda "_" . const
        (%>) = inf ">"
        (%%) = inf "%"
        (%*) = inf "*"
        (%+) = inf "+"
        (%//) = inf "//"
        (%==) = inf "=="
