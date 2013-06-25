{-# OPTIONS_GHC -Wall -Werror -i..  #-}
{-# LANGUAGE GADTs, RankNTypes, TupleSections #-}

module Main where

import Control.Monad
import System.Environment

import Source.Parse
import HIR.HIR
import HIR.Optimizations

usage :: IO ()
usage = do
  progName <- getProgName
  putStrLn $ progName ++ " [ source file name ]"
  putStrLn $ progName ++ " reads from stdin if no source file is specified"

main :: IO ()
main = do
  args <- getArgs
  case getInputSource args of
    Nothing -> usage
    Just (source, fileN) -> do
      (text, fileName) <- liftM (, fileN) source
      case parseString fileName text of
        Left errorStr -> putStrLn $ "error: " ++ errorStr
        Right term -> case termToHIR term of
          Nothing -> putStrLn "error: term not closed!"
          Just hir ->
             putStrLn $ hirDebugShowGraph (hir >>= optimizeHIR)
  where getInputSource [] = Just (getContents, "(stdin)")
        getInputSource [fileN] = Just (readFile fileN, fileN)
        getInputSource _ = Nothing
