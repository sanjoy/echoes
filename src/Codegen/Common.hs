{-# OPTIONS_GHC -Wall -Werror -i.. #-}

module Codegen.Common(RegInfo, riNewRegInfo, riAddGCReg, riAddFreeReg,
                      riGCRegs, riFreeRegs)
       where

import qualified Data.BitSet as BS

type RegInfo a = (BS.BitSet a, BS.BitSet a)

riNewRegInfo :: (Enum a) => RegInfo a
riNewRegInfo = (BS.empty, BS.empty)

riAddGCReg :: (Enum a) => a -> RegInfo a -> RegInfo a
riAddGCReg a (gcRegs, freeRegs) = (a `BS.insert` gcRegs, freeRegs)

riAddFreeReg :: (Enum a) => a -> RegInfo a -> RegInfo a
riAddFreeReg a (gcRegs, freeRegs) = (gcRegs, a `BS.insert` freeRegs)

riGCRegs :: RegInfo a -> [a]
riGCRegs = BS.toList . fst

riFreeRegs :: RegInfo a -> [a]
riFreeRegs = BS.toList . snd
