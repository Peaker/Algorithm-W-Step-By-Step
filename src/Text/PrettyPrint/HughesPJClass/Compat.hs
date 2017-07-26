{-# LANGUAGE NoImplicitPrelude, CPP #-}
module Text.PrettyPrint.HughesPJClass.Compat
    ( module Text.PrettyPrint.HughesPJClass.Compat
    , module Text.PrettyPrint.HughesPJClass
    ) where

import Prelude.Compat

#if MIN_VERSION_pretty(1,1,2)
import Text.PrettyPrint.HughesPJClass hiding (maybeParens)
import qualified Text.PrettyPrint.HughesPJClass as C
#else
import Text.PrettyPrint.HughesPJClass
#endif

maybeParens :: Bool -> Doc -> Doc
#if !MIN_VERSION_pretty(1,1,2)
maybeParens = prettyParen
#else
maybeParens = C.maybeParens
#endif
