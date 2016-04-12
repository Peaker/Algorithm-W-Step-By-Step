{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}
import Prelude.Compat

import Control.DeepSeq (rnf)
import Control.Exception (evaluate)
import Control.Lens (folded)
import Control.Lens.Operators
import Control.Lens.Tuple
import Control.Monad.State (evalStateT)
import Criterion (Benchmarkable, whnfIO)
import Criterion.Main (bench, defaultMain)
import Lamdu.Expr.Val.Annotated (Val)
import Lamdu.Infer (infer, plType, initialContext, run, emptyScope)
import Text.PrettyPrint ((<+>))
import Text.PrettyPrint.HughesPJClass (Pretty(..))

import TestVals

benchInfer :: Val () -> Benchmarkable
benchInfer e =
    whnfIO $
    case (`evalStateT` initialContext) $ run $ infer env emptyScope e of
    Left err -> fail $ show $ "error:" <+> pPrint err
    Right eTyped -> evaluate $ rnf $ eTyped ^.. folded . _1 . plType

benches :: [(String, Benchmarkable)]
benches =
    [ ("factorial", benchInfer factorialVal)
    , ("euler1", benchInfer euler1Val)
    , ("solveDepressedQuartic", benchInfer solveDepressedQuarticVal)
    , ("factors", benchInfer factorsVal)
    ]

main :: IO ()
main = defaultMain $ map (uncurry bench) benches
