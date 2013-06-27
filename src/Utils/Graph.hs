{-# OPTIONS_GHC -Wall -Werror  -fno-warn-orphans -i..  #-}
{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}

module Utils.Graph(mapConcatGraph, mapConcatGraph') where

import Control.Monad
import Compiler.Hoopl

{- A mapConcat for graphs, similar in semantics to the list mapConcat.
 - This is specialized to Closed/Closed graphs, and might need to be
 - generalized later on.-}
mapConcatGraph :: forall n n' m. (UniqueMonad m, NonLocal n, NonLocal n') =>
                  (n C O -> m (Graph n' C O),
                   n O O -> m (Graph n' O O),
                   n O C -> m (Graph n' O C)) ->
                  Graph n C C -> m (Graph n' C C)
mapConcatGraph (nodeMapFnCO, nodeMapFnOO, nodeMapFnOC)
  (GMany NothingO lMap NothingO) =
  let newSubGraphs = map blockMapFn $ mapElems lMap
      newGraph = foldl1 (liftM2 (|*><*|)) newSubGraphs
  in newGraph
  where
    blockMapFn :: UniqueMonad m => Block n C C -> m (Graph n' C C)
    blockMapFn block =
      foldBlockNodesF3 (closeOpen, openOpen, openClose) block (
        return emptyClosedGraph :: m (Graph n' C C))

    closeOpen :: UniqueMonad m => n C O -> m (Graph n' e C) -> m (Graph n' e O)
    closeOpen node graph = liftM2 (|*><*|) graph $ nodeMapFnCO node

    openOpen :: UniqueMonad m => n O O -> m (Graph n' e O) -> m (Graph n' e O)
    openOpen node graph  = liftM2 (<*>) graph $ nodeMapFnOO node

    openClose :: UniqueMonad m => n O C -> m (Graph n' e O) -> m (Graph n' e C)
    openClose node graph = liftM2 (<*>) graph $ nodeMapFnOC node

mapConcatGraph' :: forall n n' m. (UniqueMonad m, NonLocal n, NonLocal n') =>
                   (forall e' x'. n e' x' -> m (Graph n' e' x')) ->
                   Graph n C C -> m (Graph n' C C)
mapConcatGraph' f = mapConcatGraph (f, f, f)
