module Language.Brainfuck where

import qualified Data.Vector.Unboxed as V
import qualified Data.Word as W
import qualified LLVM.AST as LLVM

-------------------------------------------------------------------------------
-- * Quickie IR

-- | Instructions are 32-bit words, from least to most significant
-- bits:
--
-- 4 bit opcode
-- 16-bit operand
type Instruction = W.Word32

-- | Quickie IR is just a sequence of instructions to execute.
type IR = V.Vector Instruction


-------------------------------------------------------------------------------
-- * Execution

-- | Interpret a Quickie IR program.
--
-- This will typically be slower than 'llcompile'ing and 'jit'ing it.
interpret :: IR -> IO ()
interpret = error "interpret: unimplemented"

-- | JIT compile and execute an LLVM IR program.
jit :: LLVM.Module -> IO ()
jit = error "jit: unimplemented"


-------------------------------------------------------------------------------
-- * Dumping

-- | Dump the Quickie IR to stdout or a file.
dumpir :: Maybe String -> IR -> IO ()
dumpir = error "dumpir: unimplemented"

-- | Dump the LLVM IR to stdout or a file.
dumpllvm :: Maybe String -> LLVM.Module -> IO ()
dumpllvm = error "dumpllvm: unimplemented"

-- | Dump the LLVM-compiled assembly to stdout or a file.
dumpasm :: Maybe String -> LLVM.Module -> IO ()
dumpasm = error "dumpasm: unimplemented"

-- | Dump the LLVM-compiled object code to a file.
objcompile :: String -> LLVM.Module -> IO ()
objcompile = error "objcompile: unimplemented"


-------------------------------------------------------------------------------
-- * Compilation

-- | Compile a brainfuck source program into Quickie intermediate
-- representation.
compile :: String -> IR
compile = error "compile: unimplemented"

-- | Compile a Quickie IR program to LLVM IR.
llcompile :: IR -> LLVM.Module
llcompile = error "llcompile: unimplemented"
