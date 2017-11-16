{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | The Quickie Brainfuck parser and compiler.
module Language.Brainfuck where

import           Data.Bits ((.|.), (.&.), unsafeShiftL, unsafeShiftR)
import qualified Data.ByteString.Char8 as BS
import           Data.String (fromString)
import qualified Data.Vector.Unboxed as V
import qualified Data.Word as W
import           Foreign.Ptr (FunPtr, castFunPtr)
import qualified LLVM.AST as AST
import qualified LLVM.Context as LLVM
import qualified LLVM.ExecutionEngine as LLVM
import qualified LLVM.Module as LLVM
import qualified LLVM.Target as LLVM

-------------------------------------------------------------------------------
-- * Quickie IR

-- | Instructions are 32-bit words, from least to most significant
-- bits:
--
-- * 4 bit opcode
-- * 16 bit operand
-- * 12 bits unused
--
-- Well-formed instructions are those constructed by the pattern
-- synonyms.  Any other instruction is ill-formed and may lead to a
-- runtime error.
type Instruction = W.Word32

-- | Quickie IR is just a sequence of instructions to execute.
--
-- Well-formed IR has every 'JZ' referring to the address of exactly
-- one 'JNZ', which refers back to the address of the same 'JZ'.
-- There must be no unbalanced 'JZ' / 'JNZ' instructions, or multiple
-- jumps to the same address.  The sequence should end with a 'Hlt'.
--
-- The 'compile' function outputs well-formed IR.  The 'llcompile' and
-- 'interpret' functions expect the input to be well-formed IR and may
-- lead to a runtime error if not.
type IR = V.Vector Instruction

-- ** Instructions

-- | Move the data pointer to the \"right\" (end) of the memory array.
--
-- The operand is how far to move by.
pattern GoR :: W.Word16 -> Instruction
pattern GoR w <- (unpack16 -> (0, w)) where GoR w = pack 0 w

-- | Move the data pointer to the \"left\" (beginning) of the memory
-- array.
--
-- The operand is how far to move by.
pattern GoL :: W.Word16 -> Instruction
pattern GoL w <- (unpack16 -> (1, w)) where GoL w = pack 1 w

-- | Increment (with wrapping) the value under the data pointer.
--
-- The operand is how much to increment by.
pattern Inc :: W.Word8 -> Instruction
pattern Inc w <- (unpack8 -> (2, w)) where Inc w = pack 2 w

-- | Decrement (with wrapping) the value under the data pointer.
--
-- The operand is how much to decrement by.
pattern Dec :: W.Word8 -> Instruction
pattern Dec w <- (unpack8 -> (3, w)) where Dec w = pack 3 w

-- | Set the value under the data pointer to a constant.
--
-- The operand is the value to set.
pattern Set :: W.Word8 -> Instruction
pattern Set w <- (unpack8 -> (4, w)) where Set w = pack 4 w

-- | Jump if the value under the data pointer is zero.
--
-- The operand is the address to jump to.
pattern JZ :: W.Word16 -> Instruction
pattern JZ a <- (unpack16 -> (5, a)) where JZ a = pack 5 a

-- | Jump if the value under the data pointer is nonzero.
--
-- The operand is the address to jump to.
pattern JNZ :: W.Word16 -> Instruction
pattern JNZ a <- (unpack16 -> (6, a)) where JNZ a = pack 6 a

-- | Print the value under the data pointer as an ASCII character
-- code.
pattern PutCh :: Instruction
pattern PutCh <- 7 where PutCh = 7

-- | Read a character and store it under the data pointer.  Behaviour
-- of EOF is unspecified.
pattern GetCh :: Instruction
pattern GetCh <- 8 where GetCh = 8

-- | Terminate execution.
pattern Hlt :: Instruction
pattern Hlt <- 9 where Hlt = 9


-------------------------------------------------------------------------------
-- * Execution

-- | Interpret a Quickie IR program.
--
-- This will typically be slower than 'llcompile'ing and 'jit'ing it.
interpret :: IR -> IO ()
interpret = error "interpret: unimplemented"

-- | JIT compile and execute an LLVM IR program.
jit :: AST.Module -> IO ()
jit =
    runLLVM $ \_ ctx m ->
    LLVM.withMCJIT ctx optlevel model ptrelim fastins $ \ee ->
    LLVM.withModuleInEngine ee m $ \em ->
    LLVM.getFunction em bfmain >>= \case
      Just fn -> haskFun (castFunPtr fn :: FunPtr (IO ()))
      Nothing -> error "cannot find program entry point"
  where
    optlevel = Just 3  -- optimization level
    model    = Nothing -- code model ( Default )
    ptrelim  = Nothing -- frame pointer elimination
    fastins  = Nothing -- fast instruction selection


-------------------------------------------------------------------------------
-- * Dumping

-- | Dump the Quickie IR to stdout or a file.
dumpir :: Maybe String -> IR -> IO ()
dumpir = error "dumpir: unimplemented"

-- | Dump the LLVM IR to stdout or a file.
dumpllvm :: Maybe String -> AST.Module -> IO ()
dumpllvm (Just fname) = runLLVM $ \_ _ m -> LLVM.writeLLVMAssemblyToFile (LLVM.File fname) m
dumpllvm Nothing      = runLLVM $ \_ _ m -> LLVM.moduleLLVMAssembly m >>= BS.putStrLn

-- | Dump the LLVM-compiled assembly to stdout or a file.
dumpasm :: Maybe String -> AST.Module -> IO ()
dumpasm (Just fname) = runLLVM $ \tgt _ m -> LLVM.writeTargetAssemblyToFile tgt (LLVM.File fname) m
dumpasm Nothing      = runLLVM $ \tgt _ m -> LLVM.moduleTargetAssembly tgt m >>= BS.putStrLn

-- | Dump the LLVM-compiled object code to a file.
objcompile :: String -> AST.Module -> IO ()
objcompile fname = runLLVM $ \tgt _ m -> LLVM.writeObjectToFile tgt (LLVM.File fname) m


-------------------------------------------------------------------------------
-- * Compilation

-- | Compile a brainfuck source program into Quickie intermediate
-- representation.
compile :: String -> IR
compile = error "compile: unimplemented"

-- | Compile a Quickie IR program to LLVM IR.
llcompile :: IR -> AST.Module
llcompile = error "llcompile: unimplemented"


-------------------------------------------------------------------------------
-- * Internal utilities

-- | Pack an instruction from its components.
--
-- You should not use this directly.
pack :: Integral i => W.Word32 -> i -> Instruction
pack op arg = op .|. unsafeShiftL (fromIntegral arg) 4

-- | Unpack an instruction into an opcode and an 8-bit argument.
unpack8 :: Instruction -> (W.Word32, W.Word8)
unpack8 instr = (instr .&. 15, fromIntegral (unsafeShiftR instr 4 .&. 255))

-- | Unpack an instruction into an opcode and a 16-bit argument.
unpack16 :: Instruction -> (W.Word32, W.Word16)
unpack16 instr = (instr .&. 15, fromIntegral (unsafeShiftR instr 4 .&. 65535))

-- | Run an LLVM operation on a module.
runLLVM :: (LLVM.TargetMachine -> LLVM.Context -> LLVM.Module -> IO ()) -> AST.Module -> IO ()
runLLVM f ast =
  LLVM.withHostTargetMachine $ \tgt ->
  LLVM.withContext $ \ctx ->
  LLVM.withModuleFromAST ctx ast $
  f tgt ctx

-- | The name of the brainfuck \"main\" function in the LLVM IR.
bfmain :: AST.Name
bfmain = AST.Name (fromString "bfmain")

-- | Plumbing to call the JIT-compiled code.
foreign import ccall "dynamic" haskFun :: FunPtr (IO ()) -> IO ()
