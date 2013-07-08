{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans -i.. #-}
{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, ImpredicativeTypes #-}

module Utils.Common(M, ClsrId, SSAVar, Rator, GenRator(..), mapGenRator,
                    ratorSubstitute, IRMonad, freshVarName, runIRMonad,
                    irGetCustom, irPutCustom, mApp) where

import Compiler.Hoopl
import Control.Monad.State
import qualified Data.Maybe as Mby

type M = CheckingFuelMonad SimpleUniqueMonad
type ClsrId = Int
type SSAVar = Int
data GenRator varTy litTy = LitR litTy | VarR varTy deriving(Show, Eq, Ord)
type Rator = GenRator SSAVar

mapGenRator :: (r -> s) -> GenRator r a -> GenRator s a
mapGenRator _ (LitR litTy) = LitR litTy
mapGenRator f (VarR varTy) = VarR $ f varTy

ratorSubstitute :: (SSAVar -> Maybe a) -> Rator a -> Rator a
ratorSubstitute _ v@(LitR _) = v
ratorSubstitute f v@(VarR var) = Mby.fromMaybe v (liftM LitR $ f var)

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

irPutCustom :: custom -> IRMonad custom ()
irPutCustom s = get >>= (\(a, _) -> put (a, s))

mApp :: (Monad m) => m [a] -> m [a] -> m [a]
mApp = liftM2 (++)
