{-# LANGUAGE NoImplicitPrelude, GeneralizedNewtypeDeriving #-}
module Lamdu.Infer.Update
    ( Update(..), liftInfer
    , Subst.CanSubst, update, inferredVal
    ) where

import           Prelude.Compat

import           Control.Lens.Operators
import           Control.Lens.Tuple
import qualified Control.Monad.Trans.State as State
import           Lamdu.Calc.Val.Annotated (Val)
import qualified Lamdu.Infer as Infer
import qualified Lamdu.Infer.Internal.Monad as M
import qualified Lamdu.Infer.Internal.Subst as Subst

newtype Update a = Update { run :: Infer.Context -> a }
    deriving (Functor, Applicative, Monad)

liftInfer :: Monad m => Update a -> M.InferCtx m a
liftInfer = M.Infer . State.gets . run
{-# INLINE liftInfer #-}

-- | When inferring expressions in a non-empty scope, or unifying
-- different types, existing type expressions may refer to "old" type
-- variables that have known substitutions. To update old types to
-- contain knowledge from all accumulated substitutions, use this
-- action.
update :: Subst.CanSubst a => a -> Update a
update t = Update $ \ctx -> (Subst.apply . M._subst . M._ctxResults) ctx t
{-# INLINE update #-}

inferredVal :: Val (Infer.Payload, a) -> Update (Val (Infer.Payload, a))
inferredVal = traverse . _1 %%~ update
{-# INLINE inferredVal #-}
