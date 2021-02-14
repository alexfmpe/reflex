{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
-- |
-- Module:
--   Reflex.Workflow
-- Description:
--   Provides a convenient way to describe a series of interrelated widgets that
--   can send data to, invoke, and replace one another. Useful for modeling user interface
--   "workflows."
module Reflex.Workflow (
    Workflow (..)
  , workflow
  , workflowView
  , mapWorkflow
  , mapWorkflowCheap
  , runWorkflow

  , machine
  , stop
  , replay
  , roundRobin

  , breadthFirst
  , depthFirst
  , stack
  , wizard
  ) where

import Control.Arrow ((***))
import Control.Monad (ap, (<=<))
import Control.Monad.Cont (ContT(..), MonadCont, callCC)
import Control.Monad.Fix (MonadFix, fix)
import Control.Monad.Free (Free(..))
import Control.Monad.Free.Church
import Control.Monad.Trans (lift)
import Data.Bifunctor (bimap)
import Data.Functor (void)
import Data.Functor.Bind (Apply(..), Bind(..))
import Data.Functor.Compose (Compose(..))
import Data.Tuple (swap)
import Reflex.Class
import Reflex.Adjustable.Class
import Reflex.PostBuild.Class

import Unsafe.Coerce

--------------------------------------------------------------------------------
-- Workflow
--------------------------------------------------------------------------------
-- | A widget in a workflow
-- When the 'Event' returned by a 'Workflow' fires, the current 'Workflow' is replaced by the one inside the firing 'Event'. A series of 'Workflow's must share the same return type.
newtype Workflow t m a = Workflow { unWorkflow :: m (a, Event t (Workflow t m a)) }

-- | Runs a 'Workflow' and returns the initial value together with an 'Event' that fires whenever one 'Workflow' is replaced by another.
runWorkflow :: (Adjustable t m, MonadFix m, MonadHold t m) => Workflow t m a -> m (a, Event t a)
runWorkflow w0 = mdo
  ((a, e0), eResult) <- runWithReplace (unWorkflow w0) (fmap unWorkflow eReplace)
  eReplace <- switchHold e0 $ fmap snd eResult
  return (a, fmap fst eResult)

-- | Similar to 'runWorkflow' but combines the result into a 'Dynamic'.
workflow :: (Adjustable t m, MonadFix m, MonadHold t m) => Workflow t m a -> m (Dynamic t a)
workflow = uncurry holdDyn <=< runWorkflow

-- | Similar to 'runWorkflow', but also puts the initial value in the 'Event'.
workflowView :: (Adjustable t m, MonadFix m, MonadHold t m, PostBuild t m) => Workflow t m a -> m (Event t a)
workflowView w = do
  postBuildEv <- getPostBuild
  (initialValue, replaceEv) <- runWorkflow w
  pure $ leftmost [initialValue <$ postBuildEv, replaceEv]

-- | Map a function over a 'Workflow', possibly changing the return type.
mapWorkflow :: (Reflex t, Functor m) => (a -> b) -> Workflow t m a -> Workflow t m b
mapWorkflow f (Workflow x) = Workflow (fmap (f *** fmap (mapWorkflow f)) x)

-- | Map a "cheap" function over a 'Workflow'. Refer to the documentation for 'pushCheap' for more information and performance considerations.
mapWorkflowCheap :: (Reflex t, Functor m) => (a -> b) -> Workflow t m a -> Workflow t m b
mapWorkflowCheap f (Workflow x) = Workflow (fmap (f *** fmapCheap (mapWorkflowCheap f)) x)

--------------------------------------------------------------------------------
-- Internal utils
--------------------------------------------------------------------------------
nowOrLater :: PostBuild t m => Either (Event t a) a -> m (Event t a)
nowOrLater = \case
  Left l -> pure l
  Right n -> (n <$) <$> getPostBuild

lateOrLater :: (MonadHold t m, Reflex t) => Event t (Either (Event t a) a) -> m (Event t a)
lateOrLater ev = mdo
  let (ltrEv, lt) = fanEither ev
  ltr <- switchHold never ltrEv
  pure $ leftmost [lt, ltr]

braidFree :: Functor f => Free f a -> Free f b -> Free f (a,b)
braidFree = curry $ \case
  (Free a, Free b) -> Free $ flip fmap a $ \fa -> fmap swap $ braidFree (Free b) fa
  (Pure a, b) -> fmap (a,) b
  (a, Pure b) -> fmap (,b) a

append :: (Adjustable t m, MonadHold t m, PostBuild t m) => Event t (Step t m a) -> m (Event t a)
append ev = do
  (h,t) <- headTailE ev
  ((), childEv) <- runWithReplace (pure ()) $ ffor h $ \m -> do
    hEv <- nowOrLater =<< unStep m
    tEv <- append t
    pure $ leftmost [hEv, tEv]
  switchHold (coincidence childEv) childEv

--------------------------------------------------------------------------------
-- Replacements layer
--------------------------------------------------------------------------------
newtype Step t m a = Step { unStep :: m (Either (Event t a) a) }
instance (Reflex t, Functor m) => Functor (Step t m) where
  fmap f = Step . fmap (bimap (fmap f) f) . unStep

runStep :: PostBuild t m => Step t m a -> m (Event t a)
runStep = nowOrLater <=< unStep

newtype M t m a = M { unM :: F (Compose m (Event t)) a } deriving (Functor, Applicative, Monad)

mkM :: forall m t a. (Functor m, Reflex t) => m (Event t a) -> M t m a
mkM = M . wrap . fmap pure . Compose

braidM :: (Functor m, Reflex t) => M t m a -> M t m b -> M t m (a,b)
braidM (M ma) (M mb) = M $ toF $ braidFree (fromF ma) (fromF mb)

bottomUp
  :: forall t m a. PostBuild t m
  => (forall x. Step t m (Step t m x) -> Step t m x)
  -> M t m a -> m (Event t a)
bottomUp f mm = runStep $ runF root leaf branch
  where
    root :: F (Compose m (Event t)) a
    root = unM mm

    leaf :: a -> Step t m a
    leaf = Step . pure . Right

    branch :: Compose m (Event t) (Step t m a) -> Step t m a
    branch = f . Step . fmap Left . getCompose

topDown
  :: forall t m a. (Adjustable t m, PostBuild t m)
  => (forall x. (Free (Step t m) x -> Step t m x) -> (Step t m (Free (Step t m) x) -> Step t m x))
  -> M t m a -> m (Event t a)
topDown f mm = runStep $ go $ runF root leaf branch
  where
    root :: F (Compose m (Event t)) a
    root = unM mm

    leaf :: a -> Free (Step t m) a
    leaf = pure

    branch :: Compose m (Event t) (Free (Step t m) a) -> Free (Step t m) a
    branch = Free . Step . fmap Left . getCompose

    go :: Free (Step t m) a -> Step t m a
    go = \case
      Pure a -> Step $ pure $ Right a
      Free m -> f go m

--------------------------------------------------------------------------------
-- Continuations layer
--------------------------------------------------------------------------------
newtype Machine t m a = Machine { unMachine :: forall r. ContT r (M t m) a } deriving Functor

instance Apply (Machine t m) where
  (<.>) = ap

instance Applicative (Machine t m) where
  pure a = Machine $ pure a
  (<*>) = (<.>)

instance Bind (Machine t m) where
  join mm = Machine $ (unMachine <=< unMachine) mm

instance Monad (Machine t m) where
  (>>=) = (>>-)

instance MonadCont (Machine t m) where
  callCC f = Machine $ callCC $ \g ->
    unMachine $ f $ \a -> Machine $ unsafeCoerce $ g a -- TODO: figure out the rank shenanigans needed to prove this

runMachine :: (M t m a -> x) -> Machine t m a -> x
runMachine f = f . flip runContT pure . unMachine

--------------------------------------------------------------------------------
-- Combinators
--------------------------------------------------------------------------------
-- | Make a single step machine
machine :: (Reflex t, Applicative m) => m (Event t a) -> Machine t m a
machine a = Machine $ lift $ mkM a

-- | Machine with zero steps
stop :: (Reflex t, Applicative m) => Machine t m a
stop = machine $ pure never

-- | Capture the steps past this point as a value, allowing backwards "goto" behavior by later replaying those steps
replay :: MonadCont m => m (m a)
replay = callCC $ pure . fix

-- | Interleave two machines by running their steps in a round-robin fashion
roundRobin :: (Functor m, Reflex t) => Machine t m a -> Machine t m b -> Machine t m (a,b)
roundRobin a b = Machine $ lift $ braidM (runMachine id a) (runMachine id b)

--------------------------------------------------------------------------------
-- Runners
--------------------------------------------------------------------------------
-- | A wizard only has a single step active at any given point, and any new step replaces its predecessor
wizard :: forall t m a. (Adjustable t m, MonadFix m, MonadHold t m, PostBuild t m) => Machine t m a -> m (Event t a)
wizard = runMachine $ bottomUp $ \m -> Step $ mdo
  (nl, ll) <- runWithReplace (unStep m) (unStep <$> replacement)
  replacement <- nowOrLater nl
  Left <$> lateOrLater ll

-- | A stack can have all steps active at a time, and the first one is always active.
-- When a step triggers, it replaces the (possibly empty) pile on top of itself with a single new step
stack :: forall t m a. (Adjustable t m, MonadHold t m, PostBuild t m) => Machine t m a -> m (Event t a)
stack = runMachine $ bottomUp $ \m -> Step $ do
  replacement <- runStep m
  ((), ll) <- runWithReplace (pure ()) (unStep <$> replacement)
  Left <$> lateOrLater ll

-- | A depth first places new steps after all immediate children of the one that triggered it. All steps remain active
depthFirst :: forall t m a. (Adjustable t m, MonadHold t m, PostBuild t m) => Machine t m a -> m (Event t a)
depthFirst = runMachine $ bottomUp $ \m -> Step $ do
  replacement <- runStep m
  Left <$> append replacement

-- | A breadth first places new steps after all steps of the same depth as the one that triggered it. All steps remain active.
breadthFirst :: forall t m a. (Adjustable t m, MonadHold t m, PostBuild t m) => Machine t m a -> m (Event t a)
breadthFirst = runMachine $ topDown $ \go m -> Step $ do
  outerEv <- runStep m

  let (frees, pures) = fanEither $ ffor outerEv $ \case
        Free f -> Left f
        Pure a -> Right a
  h <- headE $ void frees
  innerEv <- append frees

  let nextLayer = go $ Free $ Step $ pure $ Left innerEv
  ((), innermostEv) <- runWithReplace (pure ()) (unStep nextLayer <$ h)
  ev <- lateOrLater innermostEv
  pure $ Left $ leftmost [ev, pures]
