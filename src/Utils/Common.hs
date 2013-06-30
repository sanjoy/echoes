{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans -i.. #-}
{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, ImpredicativeTypes #-}

module Utils.Common(M, ClsrId, SSAVar, Rator(..), ratorSubstitute,
                    IRMonad, freshVarName, runIRMonad, irGetCustom,
                    irPutCustom) where

import Compiler.Hoopl
import Control.Monad.State
import qualified Data.Maybe as Mby

type M = CheckingFuelMonad SimpleUniqueMonad
type ClsrId = Int
type SSAVar = Int
data Rator a = LitR a | VarR SSAVar deriving(Show, Eq, Ord)

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
