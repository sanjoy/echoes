{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans -i..  #-}
{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, ImpredicativeTypes #-}

module Utils.Common(M, FunctionId, SSAVar, IRMonad, freshVarName,
                    runIRMonad, irGetCustom) where

import Compiler.Hoopl
import Control.Monad.State

type M = CheckingFuelMonad SimpleUniqueMonad
type FunctionId = Int
type SSAVar = Int

type IRMonad custom a = StateT ([SSAVar], custom) M a
instance UniqueMonad m => UniqueMonad (StateT s m) where
  freshUnique = StateT (\s -> liftM (\u -> (u, s)) freshUnique)

freshVarName :: IRMonad custom SSAVar
freshVarName = StateT (\(name:names, other) -> return (name, (names, other)))

runIRMonad :: IRMonad custom a -> SSAVar -> custom -> M (a, SSAVar, custom)
runIRMonad monad ssaVarInit cInit = do
  (result, (ssaVarFinal:_, cFinal)) <- runStateT monad ([ssaVarInit..], cInit)
  return (result, ssaVarFinal, cFinal)

irGetCustom :: IRMonad custom custom
irGetCustom = liftM snd get
