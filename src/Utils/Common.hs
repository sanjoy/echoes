{-# OPTIONS_GHC -Wall -Werror -fno-warn-orphans -i..  #-}
{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables #-}

module Utils.Common(M) where

import Compiler.Hoopl

type M = CheckingFuelMonad SimpleUniqueMonad
