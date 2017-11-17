{-# LANGUAGE LambdaCase #-}

module Main where

import Data.Maybe (listToMaybe)
import System.Environment (getArgs)

import qualified Language.Brainfuck as BF
import qualified LLVM.AST as LLVM

main :: IO ()
main = getArgs >>= \case
  []         -> printHelp
  ["-h"]     -> printHelp
  ["--help"] -> printHelp
  [fname]                    -> llcompileAndRun BF.jit                           fname
  [fname, "--fast"]          -> llcompileAndRun BF.jit                           fname
  [fname, "--slow"]          -> compileAndRun   BF.interpret                     fname
  [fname, "--verify"]        -> llcompileAndRun BF.verifyllvm                    fname
  [fname, "-o", out]         -> llcompileAndRun (BF.objcompile out)              fname
  (fname:"--dump-ir":rest)   -> compileAndRun   (BF.dumpir   (listToMaybe rest)) fname
  (fname:"--dump-llvm":rest) -> llcompileAndRun (BF.dumpllvm (listToMaybe rest)) fname
  (fname:"--dump-asm":rest)  -> llcompileAndRun (BF.dumpasm  (listToMaybe rest)) fname
  args -> do
    putStrLn ("Bad command line: '" ++ unwords args ++ "'\n")
    printHelp

-- | Display the help text.
printHelp :: IO ()
printHelp = putStrLn $ unlines
  [ "quickie: a fast brainfuck compiler & JIT interpreter"
  , "-------"
  , ""
  , "quickie file"
  , "quickie file --fast"
  , "    JIT compile and run the file"
  , "    the --fast flag is for similarity with --slow, it does nothing"
  , ""
  , "quickie file --slow"
  , "    run the file without JIT"
  , ""
  , "quickie file --verify"
  , "    run the LLVM verifier on the generated LLVM IR"
  , ""
  , "quickie file -o target"
  , "    compile the file and save the object file"
  , ""
  , "quickie file --dump-ir [target]"
  , "    dump the Quickie IR of the program to the target (or stdout)"
  , ""
  , "quickie file --dump-llvm [target]"
  , "    dump the LLVM IR of the program to the target (or stdout)"
  , ""
  , "quickie file --dump-asm [target]"
  , "    dump the assembly code of the program to the target (or stdout)"
  , ""
  , "quickie (--help | -h)"
  , "    see this text"
  ]

-- | Read a file, compile it to Quickie intermediate representation,
-- and run the provided action.
compileAndRun :: (BF.IR -> IO ()) -> String -> IO ()
compileAndRun f fname =
  f =<< (BF.compile <$> readFile fname)

-- | Read a file, compile it to LLVM intermediate representation, and
-- run the provided action.
llcompileAndRun :: (LLVM.Module -> IO ()) -> String -> IO ()
llcompileAndRun f fname =
  f =<< (BF.llcompile . BF.compile <$> readFile fname)
