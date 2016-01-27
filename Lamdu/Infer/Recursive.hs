{-# LANGUAGE NoImplicitPrelude, OverloadedStrings #-}
module Lamdu.Infer.Recursive
    ( inferEnv
    ) where

import           Prelude.Compat

import qualified Lamdu.Expr.Val as V
import           Lamdu.Infer (InferCtx, freshInferredVar)
import qualified Lamdu.Infer as Infer
import           Lamdu.Infer.Internal.Scope (Scope)
import qualified Lamdu.Infer.Internal.Scope as Scope

{-# INLINE inferEnv #-}
inferEnv :: Monad m => V.Var -> Scope -> InferCtx m Infer.Payload
inferEnv recurseVar scope =
    do
        recursiveType <- freshInferredVar scope "r"
        return $
                Infer.Payload recursiveType $
                Scope.insertTypeOf recurseVar recursiveType scope
