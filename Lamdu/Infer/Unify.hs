module Lamdu.Infer.Unify
    ( unify
    ) where

import           Lamdu.Calc.Type (Type)
import           Lamdu.Infer.Internal.Monad (Infer)
import qualified Lamdu.Infer.Internal.Monad as M
import qualified Lamdu.Infer.Internal.Subst as Subst
import           Lamdu.Infer.Internal.Unify (unifyUnsafe)

{-# INLINE unify #-}
unify :: Type -> Type -> Infer ()
unify x y =
    do
        s <- M.getSubst
        unifyUnsafe (Subst.apply s x) (Subst.apply s y)
