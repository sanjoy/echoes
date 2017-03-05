{-# OPTIONS_GHC -Wall -Werror -i.. #-}

module Codegen.Common(RegInfo, riNewRegInfo, riAddGCReg, riAddFreeReg,
                      riAddFreeReg', riRemoveFreeReg, riFreeRegs,
                      riNonFreeRegsIn)
       where

import qualified Data.Set as S

type RegInfo a = (S.Set a, S.Set a)

riNewRegInfo :: (Ord a) => RegInfo a
riNewRegInfo = (S.empty, S.empty)

riAddGCReg :: (Ord a) => a -> RegInfo a -> RegInfo a
riAddGCReg a (gcRegs, freeRegs) = (a `S.insert` gcRegs, freeRegs)

riAddFreeReg :: (Ord a) => a -> RegInfo a -> RegInfo a
riAddFreeReg a (gcRegs, freeRegs) = (gcRegs, a `S.insert` freeRegs)

riAddFreeReg' :: (Ord a) => S.Set a -> RegInfo a -> RegInfo a
riAddFreeReg' = flip (S.foldl (flip riAddFreeReg))

riRemoveFreeReg :: (Ord a) => a -> RegInfo a -> RegInfo a
riRemoveFreeReg a (gcRegs, freeRegs) = (gcRegs, a `S.delete` freeRegs)

riFreeRegs :: (Ord a) => RegInfo a -> [a]
riFreeRegs = S.toList . snd

riNonFreeRegsIn :: (Ord a) => RegInfo a -> [a] -> [a]
riNonFreeRegsIn (_, freeS) = filter (not . flip S.member freeS)
