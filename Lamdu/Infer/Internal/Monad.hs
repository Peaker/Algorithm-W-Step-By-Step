{-# LANGUAGE NoImplicitPrelude, DeriveFunctor, FlexibleInstances, GeneralizedNewtypeDeriving, MultiParamTypeClasses, BangPatterns, RecordWildCards, TypeFamilies #-}
module Lamdu.Infer.Internal.Monad
    ( Results(..), subst, constraints
    , Context(..), ctxResults, initialContext
    , InferCtx(..), inferCtx
    , Infer
    , throwError

    , tell, tellSubst
    , tellProductConstraint
    , tellSumConstraint
    , listen, listenNoTell
    , getSubst
    , listenSubst

    , getSkolems, addSkolems

    , narrowTVScope, getSkolemsInScope

    , CompositeHasVar, VarKind
    , freshInferredVar, freshInferredVarName
    ) where

import           Control.Lens (Lens')
import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Lens.Tuple
import           Control.Monad (liftM)
import           Control.Monad.Trans.State (StateT(..))
import qualified Control.Monad.Trans.State as State
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Monoid ((<>))
import qualified Data.Set as Set
import           Data.String (IsString(..))
import           Lamdu.Calc.Type (Type)
import qualified Lamdu.Calc.Type as T
import           Lamdu.Calc.Type.Constraints (Constraints(..), CompositeVarConstraints(..))
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
    { _sisTVs  :: Map T.TypeVar    SkolemScope
    , _sisRTVs :: Map T.ProductVar SkolemScope
    , _sisSTVs :: Map T.SumVar     SkolemScope
    }
instance Monoid SkolemsInScope where
    mempty = SkolemsInScope mempty mempty mempty
    mappend (SkolemsInScope tvs0 rtvs0 stvs0) (SkolemsInScope tvs1 rtvs1 stvs1) =
        SkolemsInScope (tvs0 <> tvs1) (rtvs0 <> rtvs1) (stvs0 <> stvs1)

sisTVs :: Lens' SkolemsInScope (Map T.TypeVar SkolemScope)
sisTVs f SkolemsInScope {..} = f _sisTVs <&> \_sisTVs -> SkolemsInScope {..}
{-# INLINE sisTVs #-}

sisRTVs :: Lens' SkolemsInScope (Map T.ProductVar SkolemScope)
sisRTVs f SkolemsInScope {..} = f _sisRTVs <&> \_sisRTVs -> SkolemsInScope {..}
{-# INLINE sisRTVs #-}

sisSTVs :: Lens' SkolemsInScope (Map T.SumVar SkolemScope)
sisSTVs f SkolemsInScope {..} = f _sisSTVs <&> \_sisSTVs -> SkolemsInScope {..}
{-# INLINE sisSTVs #-}

class Subst.CompositeHasVar p => CompositeHasVar p where
    compositeSkolemsInScopeMap :: Lens' SkolemsInScope (Map (T.Var (T.Composite p)) SkolemScope)
instance CompositeHasVar T.ProductTag where
    compositeSkolemsInScopeMap = sisRTVs
    {-# INLINE compositeSkolemsInScopeMap #-}
instance CompositeHasVar T.SumTag where
    compositeSkolemsInScopeMap = sisSTVs
    {-# INLINE compositeSkolemsInScopeMap #-}

class Subst.HasVar t => VarKind t where
    skolemsInScopeMap :: Lens' SkolemsInScope (Map (T.Var t) SkolemScope)

instance VarKind Type where
    skolemsInScopeMap = sisTVs
    {-# INLINE skolemsInScopeMap #-}

instance CompositeHasVar p => VarKind (T.Composite p) where
    skolemsInScopeMap = compositeSkolemsInScopeMap
    {-# INLINE skolemsInScopeMap #-}

data InferState = InferState
    { _inferSupply :: {-# UNPACK #-}!Int
    , _inferSkolems :: {-# UNPACK #-}!TV.TypeVars
    , _inferSkolemConstraints :: {-# UNPACK #-}!Constraints
    , _inferSkolemsInScope :: {-# UNPACK #-}!SkolemsInScope
    }

inferSupply :: Lens' InferState Int
inferSupply f InferState {..} = f _inferSupply <&> \_inferSupply -> InferState {..}
{-# INLINE inferSupply #-}

inferSkolems :: Lens' InferState TV.TypeVars
inferSkolems f InferState {..} = f _inferSkolems <&> \_inferSkolems -> InferState {..}
{-# INLINE inferSkolems #-}

inferSkolemConstraints :: Lens' InferState Constraints
inferSkolemConstraints f InferState {..} = f _inferSkolemConstraints <&> \_inferSkolemConstraints -> InferState {..}
{-# INLINE inferSkolemConstraints #-}

inferSkolemsInScope :: Lens' InferState SkolemsInScope
inferSkolemsInScope f InferState {..} = f _inferSkolemsInScope <&> \_inferSkolemsInScope -> InferState {..}
{-# INLINE inferSkolemsInScope #-}

data Results = Results
    { _subst :: {-# UNPACK #-} !Subst
    , _constraints :: !Constraints
    }

subst :: Lens' Results Subst
subst f Results {..} = f _subst <&> \_subst -> Results {..}
{-# INLINE subst #-}

constraints :: Lens' Results Constraints
constraints f Results {..} = f _constraints <&> \_constraints -> Results {..}
{-# INLINE constraints #-}

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
        (newC, c0') <- Constraints.applySubst s1 c0
        -- TODO: c1 is usually empty, but c0' will contain ALL of c0,
        -- even though we're only interested in the NEW constraints
        -- that come from applySubst. Change applySubst to return a
        -- set of NEW constraints separately from the SUBST
        -- constraints and only verify skolem constraints against the
        -- new ones.
        verifySkolemConstraints state (newC <> c1)
        return $ Results (s0 <> s1) (c0' <> c1)
{-# INLINE appendResults #-}

data Context = Context
    { _ctxResults :: {-# UNPACK #-} !Results
    , _ctxState :: {-# UNPACK #-} !InferState
    }

ctxResults :: Lens' Context Results
ctxResults f Context {..} = f _ctxResults <&> \_ctxResults -> Context {..}
{-# INLINE ctxResults #-}

ctxState :: Lens' Context InferState
ctxState f Context {..} = f _ctxState <&> \_ctxState -> Context {..}
{-# INLINE ctxState #-}

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

tellProductConstraint :: T.ProductVar -> T.Tag -> Infer ()
tellProductConstraint v tag =
    tellConstraints $ mempty
    { productVarConstraints =
      CompositeVarConstraints $ Map.singleton v $ Set.singleton tag
    }
{-# INLINE tellProductConstraint #-}

tellSumConstraint :: T.SumVar -> T.Tag -> Infer ()
tellSumConstraint v tag =
    tellConstraints $ mempty
    { sumVarConstraints =
      CompositeVarConstraints $ Map.singleton v $ Set.singleton tag
    }
{-# INLINE tellSumConstraint #-}

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
        return ((y, _ctxResults c1), c1 { _ctxResults = _ctxResults c0} )
{-# INLINE listenNoTell #-}

nextInt :: Monad m => StateT Int m Int
nextInt =
    do
        old <- State.get
        id += 1
        return old
{-# INLINE nextInt #-}

freshInferredVarName ::
    (VarKind t, Monad m) => SkolemScope -> String -> InferCtx m (T.Var t)
freshInferredVarName skolemScope prefix =
    do
        oldSupply <- Lens.zoom inferSupply nextInt
        let varName = fromString $ prefix ++ show oldSupply
        inferSkolemsInScope . skolemsInScopeMap . Lens.at varName ?= skolemScope
        return varName
    & Lens.zoom ctxState
    & Infer
{-# INLINE freshInferredVarName #-}

getSkolemsInScope :: (Monad m, VarKind t) => T.Var t -> InferCtx m SkolemScope
getSkolemsInScope varName =
    Lens.use
    (ctxState . inferSkolemsInScope . skolemsInScopeMap . Lens.at varName .
     Lens._Just)
    & Infer
{-# INLINE getSkolemsInScope #-}

narrowTVScope :: (Monad m, VarKind t) => SkolemScope -> T.Var t -> InferCtx m ()
narrowTVScope skolems varName =
    ctxState . inferSkolemsInScope . skolemsInScopeMap . Lens.at varName .
    Lens._Just . Scope.skolemScopeVars %= TV.intersection (skolems ^. Scope.skolemScopeVars)
    & Infer
{-# INLINE narrowTVScope #-}

freshInferredVar :: Monad m => VarKind t => SkolemScope -> String -> InferCtx m t
freshInferredVar skolemScope = liftM TV.lift . freshInferredVarName skolemScope
{-# INLINE freshInferredVar #-}

listenSubst :: Infer a -> Infer (a, Subst)
listenSubst x = listen x <&> _2 %~ _subst
{-# INLINE listenSubst #-}

getSubst :: Monad m => InferCtx m Subst
getSubst = Infer $ State.gets (_subst . _ctxResults)
{-# INLINE getSubst #-}
