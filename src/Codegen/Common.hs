{-# OPTIONS_GHC -Wall -Werror -i.. #-}

module Codegen.Common(RegInfo, riNewRegInfo, riAddGCReg, riAddFreeReg,
                      riAddFreeReg', riRemoveFreeReg, riFreeRegs,
                      riNonFreeRegsIn)
       where

import qualified Data.BitSet as BS
import qualified Data.Set as S

type RegInfo a = (BS.BitSet a, BS.BitSet a)

riNewRegInfo :: (Enum a) => RegInfo a
riNewRegInfo = (BS.empty, BS.empty)

riAddGCReg :: (Enum a) => a -> RegInfo a -> RegInfo a
riAddGCReg a (gcRegs, freeRegs) = (a `BS.insert` gcRegs, freeRegs)

riAddFreeReg :: (Enum a) => a -> RegInfo a -> RegInfo a
riAddFreeReg a (gcRegs, freeRegs) = (gcRegs, a `BS.insert` freeRegs)

riAddFreeReg' :: (Enum a) => S.Set a -> RegInfo a -> RegInfo a
riAddFreeReg' = flip (S.foldl (flip riAddFreeReg))

riRemoveFreeReg :: (Enum a) => a -> RegInfo a -> RegInfo a
riRemoveFreeReg a (gcRegs, freeRegs) = (gcRegs, a `BS.delete` freeRegs)

riFreeRegs :: RegInfo a -> [a]
riFreeRegs = BS.toList . snd

riNonFreeRegsIn :: (Enum a) => RegInfo a -> [a] -> [a]
riNonFreeRegsIn (_, freeBS) = filter (not . flip BS.member freeBS)
