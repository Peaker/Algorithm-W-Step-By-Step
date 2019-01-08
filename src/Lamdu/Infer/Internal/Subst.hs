{-# LANGUAGE NoImplicitPrelude #-}
module Lamdu.Infer.Internal.Subst
    ( HasVar(new)
    , Subst(..), intersect
    , CanSubst(..)
    , fromRenames
    ) where

import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Map.Utils as MapUtils
import           Data.Maybe (fromMaybe)
import           Data.Semigroup (Semigroup(..))
import           Data.Set (Set)
import           Lamdu.Calc.Type (Type)
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Scheme (Scheme(..))
import           Lamdu.Calc.Type.Vars (TypeVars(..))
import qualified Lamdu.Calc.Type.Vars as TypeVars
import           Text.PrettyPrint (nest, text, vcat, ($+$))
import           Text.PrettyPrint.HughesPJClass (Pretty(..))
import           Text.PrettyPrint.Utils (pPrintMap)

import           Prelude.Compat hiding (null, lookup)

type SubSubst t = Map (T.Var t) t

data Subst = Subst
    { substTypes :: SubSubst Type
    , substRows :: SubSubst T.Row
    } deriving (Eq, Ord, Show)

instance Pretty Subst where
    pPrint (Subst t r) =
        text "Subst:"
        $+$ nest 4
        ( vcat
          [ pPrintMap t
          , pPrintMap r
          ]
        )

null :: Subst -> Bool
null (Subst t r) = Map.null t && Map.null r

unionDisjoint :: (Pretty a, Pretty k, Ord k) => Map k a -> Map k a -> Map k a
unionDisjoint m1 m2 =
    Map.unionWithKey collision m1 m2
    where
        collision k v0 v1 =
            error $ show $ vcat
            [ text "Given non-disjoint maps! Key=" <> pPrint k
            , text " V0=" <> pPrint v0
            , text " V1=" <> pPrint v1
            , text " in " <> pPrint (Map.toList m1)
            , text " vs " <> pPrint (Map.toList m2)
            ]

instance Semigroup Subst where
    subst0@(Subst t0 r0) <> subst1@(Subst t1 r1)
        | null subst1 = subst0
        | otherwise =
        Subst
        (t1 `unionDisjoint` Map.map (apply subst1) t0)
        (r1 `unionDisjoint` Map.map (apply subst1) r0)

instance Monoid Subst where
    mempty = Subst Map.empty Map.empty
    mappend = (<>)

intersectMapSet :: Ord k => Set k -> Map k a -> Map k a
intersectMapSet s m = Map.intersection m $ Map.fromSet (const ()) s

intersect :: TypeVars -> Subst -> Subst
intersect (TypeVars tvs rvs) (Subst ts rs) =
    Subst (intersectMapSet tvs ts) (intersectMapSet rvs rs)

class TypeVars.Free a => CanSubst a where
    apply   :: Subst -> a -> a

class (TypeVars.VarKind t, CanSubst t) => HasVar t where
    new :: T.Var t -> t -> Subst
    lookup :: T.Var t -> Subst -> Maybe t

instance CanSubst T.Row where
    apply _ T.REmpty          = T.REmpty
    apply s (T.RVar n)        = fromMaybe (T.RVar n) $ lookup n s
    apply s (T.RExtend n t r) = T.RExtend n (apply s t) (apply s r)

instance CanSubst Type where
    apply s (T.TVar n)      = fromMaybe (T.TVar n) $ lookup n s
    apply s (T.TInst n p)   = T.TInst n $ apply s <$> p
    apply s (T.TFun t1 t2)  = T.TFun (apply s t1) (apply s t2)
    apply s (T.TRecord r)   = T.TRecord $ apply s r
    apply s (T.TVariant r)      = T.TVariant $ apply s r

remove :: TypeVars -> Subst -> Subst
remove (TypeVars tvs rvs) (Subst subT subR) =
    Subst
    (MapUtils.differenceSet subT tvs)
    (MapUtils.differenceSet subR rvs)

instance CanSubst Scheme where
    apply s (Scheme forAll constraints typ) =
        Scheme forAll
        -- One need not apply subst on contraints because those are on forAll vars
        constraints
        (apply cleanS typ)
        where
            cleanS = remove forAll s

instance HasVar Type where
    {-# INLINE new #-}
    new tv t = mempty { substTypes = Map.singleton tv t }
    {-# INLINE lookup #-}
    lookup tv s = Map.lookup tv (substTypes s)

instance HasVar T.Row where
    {-# INLINE new #-}
    new tv t = mempty { substRows = Map.singleton tv t }
    {-# INLINE lookup #-}
    lookup tv t = Map.lookup tv (substRows t)

{-# INLINE fromRenames #-}
fromRenames :: TypeVars.Renames -> Subst
fromRenames (TypeVars.Renames tvRenames rvRenames) =
    Subst
    (fmap TypeVars.lift tvRenames)
    (fmap TypeVars.lift rvRenames)
