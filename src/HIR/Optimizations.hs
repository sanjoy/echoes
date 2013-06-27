{-# OPTIONS_GHC -Wall -Werror -fno-warn-unused-binds -i..  #-}
{-# LANGUAGE GADTs, RankNTypes #-}

module HIR.Optimizations(optimizeHIR) where

import Control.Monad

import HIR.ConstantPropagation
import HIR.DeadAssignmentElimination
import HIR.RemoveBadPhis
import HIR.HIR
import Utils.Common

optimizeHIR :: [HFunction] -> M [HFunction]
optimizeHIR = mapM (runConstantPropagation >=>
                    runDeadAssignmentElimination >=>
                    runRemoveBadPhis)
