{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans -i..  #-}
{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, ImpredicativeTypes, FunctionalDependencies #-}

module Utils.Common(M, FunctionId, SSAVar, IRMonad) where

import Compiler.Hoopl
import Control.Monad.State

type M = CheckingFuelMonad SimpleUniqueMonad
type FunctionId = Int
type SSAVar = Int

type IRMonad a = StateT [SSAVar] M a
instance UniqueMonad m => UniqueMonad (StateT s m) where
  freshUnique = StateT (\s -> liftM (\u -> (u, s)) freshUnique)
