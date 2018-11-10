{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}
{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}

module TestVals
    ( env
    , list
    , factorialVal, euler1Val, solveDepressedQuarticVal
    , factorsVal
    , letItem, recordType
    , infixArgs
    , eLet
    , litInt, intType
    , stTypePair, listTypePair, boolTypePair, polySTPair, polyIdTypePair, unsafeCoerceTypePair
    , ignoredParamTypePair
    , xGetterPair, xGetterPairConstrained
    ) where

import           Prelude.Compat

import           Control.Lens.Operators
import qualified Data.ByteString.Char8 as BS8
import qualified Data.Map as Map
import           Data.Monoid ((<>))
import qualified Data.Set as Set
import           Lamdu.Calc.Pure (($$), ($$:))
import qualified Lamdu.Calc.Pure as P
import           Lamdu.Calc.Term (Val)
import qualified Lamdu.Calc.Term as V
import           Lamdu.Calc.Type (Type, (~>))
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Constraints (Constraints(..))
import qualified Lamdu.Calc.Type.Constraints as Constraints
import           Lamdu.Calc.Type.Nominal (Nominal(..), NominalType(..))
import           Lamdu.Calc.Type.Scheme (Scheme(..))
import qualified Lamdu.Calc.Type.Scheme as Scheme
import qualified Lamdu.Calc.Type.Vars as TV
import           Lamdu.Infer (TypeVars(..), Dependencies(..))

{-# ANN module ("HLint: ignore Redundant $" :: String) #-}

-- TODO: $$ to be type-classed for TApp vs BApp
-- TODO: TCon "->" instead of TFun

eLet :: V.Var -> Val () -> (Val () -> Val ()) -> Val ()
eLet name val mkBody = P.app (P.abs name body) val
    where
        body = mkBody $ P.var name

letItem :: V.Var -> Val () -> (Val () -> Val ()) -> Val ()
letItem name val mkBody = P.lambda name mkBody $$ val

openRecordType :: T.RecordVar -> [(T.Tag, Type)] -> Type
openRecordType tv = T.TRecord . foldr (uncurry T.CExtend) (T.CVar tv)

recordType :: [(T.Tag, Type)] -> Type
recordType = T.TRecord . foldr (uncurry T.CExtend) T.CEmpty

forAll :: [T.TypeVar] -> ([Type] -> Type) -> Scheme
forAll tvs mkType =
    Scheme mempty { typeVars = Set.fromList tvs } mempty $ mkType $ map T.TVar tvs

stTypePair :: (T.NominalId, Nominal)
stTypePair =
    ( "ST"
    , Nominal
        { _nomParams = Map.fromList [("res", "A"), ("s", "S")]
        , _nomType = OpaqueNominal
        }
    )

stOf :: Type -> Type -> Type
stOf s a = T.TInst (fst stTypePair) $ Map.fromList [("res", a), ("s", s)]

listTypePair :: (T.NominalId, Nominal)
listTypePair =
    ( "List"
    , Nominal
        { _nomParams = Map.singleton "elem" tvName
        , _nomType =
            T.CEmpty
            & T.CExtend "[]" (recordType [])
            & T.CExtend ":" (recordType [("head", tv), ("tail", listOf tv)])
            & T.TVariant
            & Scheme.mono
            & NominalType
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
intType = T.TInst "Int" Map.empty

boolTypePair :: (T.NominalId, Nominal)
boolTypePair =
    ( "Bool"
    , Nominal
        { _nomParams = Map.empty
        , _nomType =
            T.CEmpty
            & T.CExtend "True" (recordType [])
            & T.CExtend "False" (recordType [])
            & T.TVariant
            & Scheme.mono
            & NominalType
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
        { _nomParams = Map.empty
        , _nomType =
            NominalType $ Scheme (TV.singleton tvA) mempty $
            ta ~> ta
        }
    )

polySTPair :: (T.NominalId, Nominal)
polySTPair =
    ( "PolyST"
    , Nominal
      { _nomParams = Map.singleton "res" tvA
      , _nomType =
          NominalType $ Scheme (TV.singleton tvS) mempty $
          T.TInst (fst stTypePair) $ Map.fromList
          [ ("s", T.TVar tvS)
          , ("res", T.TVar tvRes)
          ]
      }
    )
    where
        tvRes :: T.TypeVar
        tvRes = "res"
        tvS :: T.TypeVar
        tvS = "s"

unsafeCoerceTypePair :: (T.NominalId, Nominal)
unsafeCoerceTypePair =
    ( "UnsafeCoerce"
    , Nominal
        { _nomParams = Map.empty
        , _nomType =
            NominalType $ Scheme (TV.singleton tvA <> TV.singleton tvB) mempty $
            ta ~> tb
        }
    )

ignoredParamTypePair :: (T.NominalId, Nominal)
ignoredParamTypePair =
    ( "IgnoredParam"
    , Nominal
        { _nomParams = Map.singleton "res" tvB
        , _nomType =
            NominalType $ Scheme (TV.singleton tvA) mempty $
            ta ~> tb
        }
    )

xGetter :: (T.RecordVar -> Constraints) -> Nominal
xGetter constraints =
    Nominal
    { _nomParams = Map.empty
    , _nomType =
        NominalType $ Scheme (TV.singleton tvA <> TV.singleton tvRest) (constraints tvRest) $
        openRecordType tvRest [("x", ta)] ~> ta
    }
    where
        tvRest :: T.RecordVar
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
          { Constraints.recordVar =
              Constraints.CompositeVars $ Map.singleton tvRest
              Constraints.CompositeVar
              { Constraints._forbiddenFields = Set.fromList ["x", "y"]
              }
          }

    )

maybeOf :: Type -> Type
maybeOf t =
    T.TVariant $
    T.CExtend "Nothing" (recordType []) $
    T.CExtend "Just" t T.CEmpty

infixType :: Type -> Type -> Type -> Type
infixType a b c = recordType [("l", a), ("r", b)] ~> c

infixArgs :: Val () -> Val () -> Val ()
infixArgs l r = P.record [("l", l), ("r", r)]

env :: Dependencies
env =
    Deps
    { _depsGlobalTypes =
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

        , ("stBind", forAll ["s", "a", "b"] $ \ [s, a, b] -> infixType (stOf s a) (a ~> stOf s b) (stOf s b))
        ]
    , _depsNominals =
        Map.fromList
        [ stTypePair
        , listTypePair
        , boolTypePair
        , polyIdTypePair
        , polySTPair
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
    P.var "fix" $$
    P.lambda "loop"
    ( \loop ->
        P.lambda "x" $ \x ->
        P.var "if" $$:
        [ ( "condition", P.var "==" $$
                infixArgs x (litInt 0) )
        , ( "then", litInt 1 )
        , ( "else", P.var "*" $$
                infixArgs x (loop $$ (P.var "-" $$ infixArgs x (litInt 1)))
            )
        ]
    )

euler1Val :: Val ()
euler1Val =
    P.var "sum" $$
    ( P.var "filter" $$:
        [ ("from", P.var ".." $$ infixArgs (litInt 1) (litInt 1000))
        , ( "predicate",
                P.lambda "x" $ \x ->
                P.var "||" $$ infixArgs
                ( P.var "==" $$ infixArgs
                    (litInt 0) (P.var "%" $$ infixArgs x (litInt 3)) )
                ( P.var "==" $$ infixArgs
                    (litInt 0) (P.var "%" $$ infixArgs x (litInt 5)) )
            )
        ]
    )

solveDepressedQuarticVal :: Val ()
solveDepressedQuarticVal =
    P.lambdaRecord "params" ["e", "d", "c"] $ \[e, d, c] ->
    letItem "solvePoly" (P.var "id")
    $ \solvePoly ->
    letItem "sqrts"
    ( P.lambda "x" $ \x ->
        letItem "r"
        ( P.var "sqrt" $$ x
        ) $ \r ->
        list [r, P.var "negate" $$ r]
    )
    $ \sqrts ->
    P.var "if" $$:
    [ ("condition", P.var "==" $$ infixArgs d (litInt 0))
    , ( "then",
            P.var "concat" $$
            ( P.var "map" $$:
                [ ("list", solvePoly $$ list [e, c, litInt 1])
                , ("mapping", sqrts)
                ]
            )
        )
    , ( "else",
            P.var "concat" $$
            ( P.var "map" $$:
                [ ( "list", sqrts $$ (P.var "head" $$ (solvePoly $$ list
                        [ P.var "negate" $$ (d %* d)
                        , (c %* c) %- (litInt 4 %* e)
                        , litInt 2 %* c
                        , litInt 1
                        ]))
                    )
                , ( "mapping",
                        P.lambda "x" $ \x ->
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

inf :: V.Var -> Val () -> Val () -> Val ()
inf str x y = P.var str $$ infixArgs x y

factorsVal :: Val ()
factorsVal =
    fix_ $ \loop ->
    P.lambdaRecord "params" ["n", "min"] $ \ [n, m] ->
    if_ ((m %* m) %> n) (list [n]) $
    if_ ((n %% m) %== litInt 0)
    (cons m $ loop $$: [("n", n %// m), ("min", m)]) $
    loop $$: [ ("n", n), ("min", m %+ litInt 1) ]
    where
        fix_ f = P.var "fix" $$ P.lambda "loop" f
        if_ b t f =
            nullaryCase "False" f
            (nullaryCase "True" t P.absurd)
            $$ P.fromNom "Bool" b
        nullaryCase tag handler = P._case tag (defer handler)
        defer = P.lambda "_" . const
        (%>) = inf ">"
        (%%) = inf "%"
        (%*) = inf "*"
        (%+) = inf "+"
        (%//) = inf "//"
        (%==) = inf "=="
