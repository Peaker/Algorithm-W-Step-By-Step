{-# LANGUAGE NoImplicitPrelude, FlexibleContexts, OverloadedStrings #-}

import           Prelude.Compat hiding (any)

import           Control.Lens (zoom)
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad.State (StateT(..), runState, modify, get)
import qualified Data.Map as M
import           Lamdu.Expr.Pure (($$), ($$:), ($=), ($.))
import qualified Lamdu.Expr.Pure as P
import           Lamdu.Expr.Type ((~>), Type(..), Composite(..))
import           Lamdu.Expr.Val (Val(..))
import qualified Lamdu.Expr.Val as V
import           Lamdu.Expr.Val.Arbitrary ()
import           Lamdu.Infer
import qualified Lamdu.Infer.Recursive as Recursive
import           Lamdu.Infer.Unify
import qualified Lamdu.Infer.Update as Update
import qualified Test.Framework as TestFramework
import           Test.Framework.Providers.QuickCheck2 (testProperty)
import           TestVals
import           Text.PrettyPrint ((<>), (<+>), ($+$))
import qualified Text.PrettyPrint as PP
import           Text.PrettyPrint.HughesPJClass (Pretty(..))

{-# ANN module ("HLint: ignore Use const" :: String) #-}

-- I like case .. $ case .. $ absurd, so redundant $ is nice there
-- like trailing commas
{-# ANN module ("HLint: ignore Redundant $" :: String) #-}

exps :: [Val ()]
exps =
    [ eLet "id" (lambda "x" id) id

    , eLet "id" (lambda "x" id) $ \id' -> id' $$ id'

    , eLet "id" (lambda "x" (\x -> eLet "y" x id)) $ \id' -> id' $$ id'

    , eLet "id" (lambda "x" (\x -> eLet "y" x id)) $ \id' -> id' $$ id' $$ litInt 2

    , eLet "id" (lambda "x" (\x -> x $$ x)) id

    , lambda "m" $ \m ->
        eLet "y" m $ \y ->
        eLet "x" (y $$ litInt 3) id

    , litInt 2 $$ litInt 2

    , lambda "a" $ \a ->
        eLet "x"
        ( lambda "b"
            ( \_ -> eLet "y" (lambda "c" (\_ -> a $$ litInt 1))
                (\y -> y $$ litInt 2) )
        ) $ \x -> x $$ litInt 3

    , lambda "a" $ \a -> lambda "b" $ \b -> b $$ (a $$ (a $$ b))

    , lambda "vec" $ \vec ->
        "newX" $= (vec $. "x") $
        "newY" $= (vec $. "y") $
        P.recEmpty

    , eLet "vec" ("x" $= litInt 5 $ "y" $= litInt 7 $ P.recEmpty) ($. "x")

    , eLet "vec" ("x" $= litInt 5 $ "y" $= litInt 7 $ P.recEmpty) ($. "z")

    , lambda "x" $ \x -> "prev" $= (x $. "cur") $ x

    , "x" $= litInt 2 $ "x" $= litInt 3 $ P.recEmpty

    , lambda "r" ("x" $= litInt 2) $$ ("x" $= litInt 3) P.recEmpty

    , eLet "f" (lambda "r" ("x" $= litInt 3)) $
        \f -> f $$ ("x" $= litInt 2) P.recEmpty

    , "x" $= litInt 1 $ P.hole

    , lambda "x" $ \x -> list [x, x]

    , factorialVal, euler1Val, solveDepressedQuarticVal

    , eLet "open"
        ( lambda "x" $ \x ->
            eLet "y" (x $. "x") $
            \_y -> x ) $ \open ->
        open $$ ("x" $= litInt 0 $ P.recEmpty)

    , P.global "fix" $$ lambda "f"
        ( \f -> P.hole $$ (f $$ (f $$ (P.global "zipWith" $$ P.hole $$ P.hole $$ P.hole)))
        )

    , list [P.inject "x" (litInt 1), P.inject "y" (litInt 2), P.inject "x" P.hole]
    , P.absurd

    , --maybe:
      lambda "nothing" $ \nothingHandler ->
      lambda "just" $ \justHandler ->
      P._case "Nothing" (lambda "_" (const nothingHandler)) $
      P._case "Just" justHandler $
      P.absurd

    , "a" $= (P.global "maybe" $$ litInt 0 $$ P.global "plus1" $$ (P.global "Just" $$ litInt 1)) $
      "b" $= (P.global "maybe" $$ litInt 0 $$ P.global "plus1" $$ P.global "Nothing") $
      P.recEmpty

    , nullTest

    , P.toNom (fst polyIdTypePair) (P.lambda "x" id)
    , P.toNom (fst unsafeCoerceTypePair) (P.lambda "x" id)

    , P.toNom (fst ignoredParamTypePair) (P.lambda "x" id)

    , P.toNom (fst unsafeCoerceTypePair) (P.fromNom (fst polyIdTypePair) P.hole)
    , P.toNom (fst polyIdTypePair) (P.fromNom (fst unsafeCoerceTypePair) P.hole)

    , P.toNom (fst polyIdTypePair) (P.global "plus1")
    , P.lambda "a" $ \a -> P.toNom (fst polyIdTypePair) (P.lambda "_" $ \_ -> a)

    , P.toNom (fst xGetterPair) (P.lambda "record" $ \record -> record $. "x")
    , P.toNom (fst xGetterPairConstrained) (P.lambda "record" $ \record -> record $. "x")
    ]

nullTest :: Val ()
nullTest =
    lambda "list" $ \l ->
    ( P._case "[]" (lambda "_" (const (P.global "True"))) $
      P._case ":" (lambda "_" (const (P.global "False"))) $
      P.absurd
    ) $$ P.fromNom (fst listTypePair) l

recurseVar :: V.Var
recurseVar = V.Var "Recurse"

recurse :: V.Val ()
recurse = P.var recurseVar

recursiveExps :: [Val ()]
recursiveExps =
    [ eLet "id" (lambda "x" id) id
    , recurse
    , foldrTest
    ]

foldrTest :: Val ()
foldrTest =
    lambda "nil" $ \nil ->
    lambda "cons" $ \cons ->
    lambda "list" $ \l ->
    ( P._case "[]" (lambda "_" (const nil)) $
      P._case ":" (lambdaRecord ["head", "tail"] $
                   \ [head_, tail_] ->
                   let rest = recurse $$ nil $$ cons $$ tail_
                   in cons $$: [("head", head_), ("rest", rest)]) $
      P.absurd
    ) $$ P.fromNom (fst listTypePair) l

unifies :: [(Type, Type)]
unifies =
    [ ( ( TRecord $
          CExtend "z" (TVar "b") $
          CExtend "x" (TVar "c") $
          CExtend "y" (TVar "d") $
          CEmpty
        ) ~> TVar "e"
      , ( TRecord $
          CExtend "x" intType $
          CExtend "y" (TVar "a") $
          CExtend "z" (TVar "a") $
          CVar "r"
        ) ~> TVar "a"
      )
    ]

runAndPrint :: Val a -> Infer (Type, Val (Payload, b)) -> IO ()
runAndPrint e =
    printResult . (`runStateT` initialContext) . run
    where
        printResult (Left err) = print (V.pPrintUnannotated e $+$ pPrint err)
        printResult (Right ((typ, val), finalContext)) =
            do
                let scheme = makeScheme finalContext typ
                print $ V.pPrintUnannotated val <+> PP.text "::" <+> pPrint scheme
                let next = modify (+1) >> get
                    tag x =
                      do  n <- zoom _1 next
                          zoom _2 $ modify $ M.insert n x
                          return n
                let (taggedVal, (_, types)) =
                      runState (traverse (tag . _plType . fst) val) (0::Int, M.empty)
                print $ pPrint taggedVal
                let indent = PP.hcat $ replicate 4 PP.space
                mapM_ (\(k, t) -> print $ indent <> pPrint k <+> "=" <+> pPrint t) $ M.toList types

inferType :: Scope -> Val a -> Infer (Type, Val (Payload, a))
inferType scope e =
    do
        e' <- infer env scope e
        let t = e' ^. V.payload . _1 . plType
        return (t, e')

test :: Val () -> IO ()
test e = runAndPrint e $ inferType emptyScope e

inferInto :: Payload -> Val a -> Infer (Type, Val (Payload, a))
inferInto pl val =
    do
        (inferredType, inferredVal) <- inferType (pl ^. plScope) val
        unify inferredType (pl ^. plType)
        (,) <$> Update.update inferredType <*> Update.inferredVal inferredVal & Update.liftInfer

testRecursive :: Val () -> IO ()
testRecursive e =
    runAndPrint e $
    do
        recursivePos <- Recursive.inferEnv recurseVar emptyScope
        inferInto recursivePos e

testUnify :: Type -> Type -> IO ()
testUnify x y =
    do
        unify x y
        Update.update x & Update.liftInfer
    & printResult . (`runStateT` initialContext) . run
    where
        printCase = pPrint x <+> PP.text "=" <+> pPrint y <+> PP.text ":"
        printResult (Left err) = print $ printCase $+$ pPrint err
        printResult (Right (res, _ctx)) = print $ printCase $+$ pPrint res

prop_alphaEq :: Val () -> Bool
prop_alphaEq v = v `V.alphaEq` v

-- TODO: prop that top-level type equals the result type in scheme

main :: IO ()
main =
    do
        putStrLn "Expression types:"
        mapM_ test exps
        putStrLn "Recursive expression types:"
        mapM_ testRecursive recursiveExps
        putStrLn "Unify:"
        mapM_ (uncurry testUnify) unifies
        TestFramework.defaultMain [testProperty "alphaEq self" prop_alphaEq]
