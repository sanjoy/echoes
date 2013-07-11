{-# OPTIONS_GHC -Wall -Werror -i..  #-}
{-# LANGUAGE GADTs, RankNTypes, TupleSections, DeriveDataTypeable #-}

module Main where

import Compiler.Hoopl
import Control.Monad
import System.Console.CmdArgs

import Source.Parse
import HIR.HIR
import HIR.Optimizations
import LIR.LIR
import Codegen.Codegen

data Args = Args {
  debug :: Bool,
  fuel :: Int,
  input :: FilePath,
  output :: FilePath
  } deriving(Show, Data, Typeable)

defaultArgs :: Args
defaultArgs = Args {
  debug = False &= help "print debug information",
  fuel  = maxBound &= help "optimization fuel",
  input = def &= typFile &= help "input file (leave blank for stdin)",
  output = def &= typFile &= help "output file (leave blank for stdout)"
  }

main :: IO ()
main = do
  parsedArgs <- cmdArgs defaultArgs
  let (inpSrc, fileN) = createSource $ input parsedArgs
      outSink = createSink $ output parsedArgs
      isDebug = debug parsedArgs
      initialFuel = fuel parsedArgs
  (text, fileName) <- liftM (, fileN) inpSrc
  case parseString fileName text of
    Left errorStr -> putStrLn $ "error: " ++ errorStr
    Right term -> case termToHIR term of
      Nothing -> putStrLn "error: term not closed!"
      Just hir -> do
        debugShow isDebug (hirDebugShowGraph hir) "Unoptimized HIR"
        let optimizedHIR = hir >>= optimizeHIR
        debugShow isDebug (hirDebugShowGraph optimizedHIR) "Optimized HIR"
        let lir = optimizedHIR >>= mapM hirToLIR
        debugShow isDebug (lirDebugShowGraph lir) "Unoptimized LIR"
        when isDebug $ putStrLn $ lirDebugCodegen lir
        let mcode = lir >>= lirCodegen
            code = runSimpleUniqueMonad $ runWithFuel initialFuel mcode
        outSink code
  where
    createSource "" = (getContents, "(stdin)")
    createSource fileN = (readFile fileN, fileN)
    createSink "" = putStr
    createSink fileName = writeFile fileName

    debugShow isDbg text header = when isDbg $ do
      putStrLn header
      putStrLn $ replicate (length header) '~'
      putStrLn ""
      putStrLn text
