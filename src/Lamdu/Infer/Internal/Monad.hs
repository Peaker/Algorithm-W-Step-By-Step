{-# LANGUAGE NoImplicitPrelude, DeriveFunctor, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, BangPatterns, RecordWildCards, TypeFamilies, TemplateHaskell #-}
module Lamdu.Infer.Internal.Monad
    ( Results(..), subst, constraints
    , Context(..), ctxResults, initialContext
    , InferCtx(..), inferCtx
    , Infer
    , throwError

    , tell, tellSubst
    , tellRowConstraint
    , listen, listenNoTell
    , getSubst
    , listenSubst

    , getSkolems, addSkolems

    , narrowTVScope, getSkolemsInScope

    , VarKind
    , freshInferredVar, freshInferredVarName
    ) where

import           Control.Lens (Lens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad.Trans.State (StateT(..))
import qualified Control.Monad.Trans.State as State
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Semigroup (Semigroup(..))
import qualified Data.Set as Set
import           Data.String (IsString(..))
import           Lamdu.Calc.Type (Type)
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Constraints (Constraints(..))
import qualified Lamdu.Calc.Type.Constraints as Constraints
import qualified Lamdu.Calc.Type.Vars as TV
import           Lamdu.Infer.Error (Error)
import qualified Lamdu.Infer.Error as Err
import qualified Lamdu.Infer.Internal.Constraints as Constraints
import           Lamdu.Infer.Internal.Scope (SkolemScope)
import qualified Lamdu.Infer.Internal.Scope as Scope
import           Lamdu.Infer.Internal.Subst (Subst)
import qualified Lamdu.Infer.Internal.Subst as Subst

import           Prelude.Compat

data SkolemsInScope = SkolemsInScope
    { _sisTVs :: Map T.TypeVar SkolemScope
    , _sisRVs :: Map T.RowVar  SkolemScope
    } deriving (Eq, Ord)
instance Semigroup SkolemsInScope where
    SkolemsInScope tvs0 rvs0 <> SkolemsInScope tvs1 rvs1 =
        SkolemsInScope (tvs0 <> tvs1) (rvs0 <> rvs1)
instance Monoid SkolemsInScope where
    mempty = SkolemsInScope mempty mempty
    mappend = (<>)

Lens.makeLenses ''SkolemsInScope

class Subst.HasVar t => VarKind t where
    skolemsInScopeMap :: Lens' SkolemsInScope (Map (T.Var t) SkolemScope)

instance VarKind Type where
    skolemsInScopeMap = sisTVs
    {-# INLINE skolemsInScopeMap #-}

instance VarKind T.Row where
    skolemsInScopeMap = sisRVs
    {-# INLINE skolemsInScopeMap #-}

data InferState = InferState
    { _inferSupply :: {-# UNPACK #-}!Int
    , _inferSkolems :: {-# UNPACK #-}!TV.TypeVars
    , _inferSkolemConstraints :: !Constraints
    , _inferSkolemsInScope :: {-# UNPACK #-}!SkolemsInScope
    } deriving (Eq, Ord)

Lens.makeLenses ''InferState

data Results = Results
    { _subst :: {-# UNPACK #-} !Subst
    , _constraints :: !Constraints
    } deriving (Eq, Ord)

Lens.makeLenses ''Results

emptyResults :: Results
emptyResults = Results mempty mempty
{-# INLINE emptyResults #-}

verifySkolemConstraints :: InferState -> Constraints -> Either Error ()
verifySkolemConstraints state newConstraints
    | Constraints.null unexpectedConstraints = Right ()
    | otherwise = Left $ Err.UnexpectedSkolemConstraint unexpectedConstraints
    where
        unexpectedConstraints =
            Constraints.intersect (_inferSkolems state) newConstraints
            `Constraints.difference` _inferSkolemConstraints state
{-# INLINE verifySkolemConstraints #-}

appendResults :: Context -> Results -> Either Error Results
appendResults (Context (Results s0 c0) state) (Results s1 c1) =
    do
        Constraints.Substituted newC c0' <- Constraints.applySubst s1 c0
        -- TODO: c1 is usually empty, but c0' will contain ALL of c0,
        -- even though we're only interested in the NEW constraints
        -- that come from applySubst. Change applySubst to return a
        -- set of NEW constraints separately from the SUBST
        -- constraints and only verify skolem constraints against the
        -- new ones.
        verifySkolemConstraints state (newC <> c1)
        pure $ Results (s0 <> s1) (c0' <> c1)
{-# INLINE appendResults #-}

data Context = Context
    { _ctxResults :: {-# UNPACK #-} !Results
    , _ctxState :: {-# UNPACK #-} !InferState
    } deriving (Eq, Ord)

Lens.makeLenses ''Context

initialContext :: Context
initialContext =
    Context
    { _ctxResults = emptyResults
    , _ctxState =
        InferState
        { _inferSupply = 0
        , _inferSkolems = mempty
        , _inferSkolemConstraints = mempty
        , _inferSkolemsInScope = mempty
        }
    }

-- We use StateT, but it is composed of an actual stateful fresh
-- supply and a component used as a writer avoiding the
-- associativity/performance issues of WriterT
newtype InferCtx m a = Infer { run :: StateT Context m a }
    deriving (Functor, Applicative, Monad)

inferCtx ::
    Lens.Iso
    (InferCtx m a)
    (InferCtx n b)
    (StateT Context m a)
    (StateT Context n b)
inferCtx = Lens.iso run Infer

type Infer = InferCtx (Either Error)

throwError :: Error -> Infer a
throwError = Infer . StateT . const . Left
{-# INLINE throwError #-}

getSkolems :: Monad m => InferCtx m TV.TypeVars
getSkolems = Infer $ Lens.use (ctxState . inferSkolems)
{-# INLINE getSkolems #-}

addSkolems :: Monad m => TV.TypeVars -> Constraints -> InferCtx m ()
addSkolems skolems skolemConstraints =
    Infer $ Lens.zoom ctxState $
    do
        inferSkolems <>= skolems
        inferSkolemConstraints <>= skolemConstraints

{-# INLINE addSkolems #-}

tell :: Results -> Infer ()
tell w =
    Infer $ StateT $ \c ->
    do
        !newRes <- appendResults c w
        Right ((), c { _ctxResults = newRes} )
{-# INLINE tell #-}

tellSubst :: Subst.HasVar t => T.Var t -> t -> Infer ()
tellSubst v t = tell $ emptyResults { _subst = Subst.new v t }
{-# INLINE tellSubst #-}

tellConstraints :: Constraints -> Infer ()
tellConstraints x = tell $ emptyResults { _constraints = x }
{-# INLINE tellConstraints #-}

singleForbiddenField :: T.Var T.Row -> T.Tag -> Constraints
singleForbiddenField v tag =
    Constraints $ Map.singleton v $
    Constraints.CompositeVar
    { _forbiddenFields = Set.singleton tag
    }

tellRowConstraint :: T.RowVar -> T.Tag -> Infer ()
tellRowConstraint v = tellConstraints . singleForbiddenField v
{-# INLINE tellRowConstraint #-}

listen :: Infer a -> Infer (a, Results)
listen (Infer (StateT act)) =
    Infer $ StateT $ \c0 ->
    do
        (y, c1) <- act c0 { _ctxResults = emptyResults }
        !w <- appendResults c0 (_ctxResults c1)
        Right ((y, _ctxResults c1), c1 { _ctxResults = w} )
{-# INLINE listen #-}

-- Duplicate of listen because building one on top of the other has a
-- large (~15%) performance penalty.
listenNoTell :: Monad m => InferCtx m a -> InferCtx m (a, Results)
listenNoTell (Infer (StateT act)) =
    Infer $ StateT $ \c0 ->
    do
        (y, c1) <- act c0 { _ctxResults = emptyResults }
        pure ((y, _ctxResults c1), c1 { _ctxResults = _ctxResults c0} )
{-# INLINE listenNoTell #-}

nextInt :: Monad m => StateT Int m Int
nextInt =
    do
        old <- State.get
        id += 1
        pure old
{-# INLINE nextInt #-}

freshInferredVarName ::
    (VarKind t, Monad m) => SkolemScope -> String -> InferCtx m (T.Var t)
freshInferredVarName skolemScope prefix =
    do
        oldSupply <- Lens.zoom inferSupply nextInt
        let varName = fromString $ prefix ++ show oldSupply
        inferSkolemsInScope . skolemsInScopeMap . Lens.at varName ?= skolemScope
        pure varName
    & Lens.zoom ctxState
    & Infer
{-# INLINE freshInferredVarName #-}

getSkolemsInScope :: (Monad m, VarKind t) => T.Var t -> InferCtx m SkolemScope
getSkolemsInScope varName =
    Lens.use
    (ctxState . inferSkolemsInScope . skolemsInScopeMap . Lens.ix varName)
    & Infer
{-# INLINE getSkolemsInScope #-}

narrowTVScope :: (Monad m, VarKind t) => SkolemScope -> T.Var t -> InferCtx m ()
narrowTVScope skolems varName =
    ctxState . inferSkolemsInScope . skolemsInScopeMap . Lens.at varName .
    Lens._Just . Scope.skolemScopeVars %= TV.intersection (skolems ^. Scope.skolemScopeVars)
    & Infer
{-# INLINE narrowTVScope #-}

freshInferredVar :: Monad m => VarKind t => SkolemScope -> String -> InferCtx m t
freshInferredVar skolemScope = fmap TV.lift . freshInferredVarName skolemScope
{-# INLINE freshInferredVar #-}

listenSubst :: Infer a -> Infer (a, Subst)
listenSubst x = listen x <&> _2 %~ _subst
{-# INLINE listenSubst #-}

getSubst :: Monad m => InferCtx m Subst
getSubst = Infer $ State.gets (_subst . _ctxResults)
{-# INLINE getSubst #-}
