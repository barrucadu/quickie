{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | The Quickie Brainfuck parser and compiler.
module Language.Brainfuck where

import           Data.Bits ((.|.), (.&.), unsafeShiftL, unsafeShiftR)
import qualified Data.ByteString.Char8 as BS
import           Data.Char (chr, ord)
import           Data.String (fromString)
import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Unboxed.Mutable as VM
import qualified Data.Word as W
import           Foreign.Ptr (FunPtr, castFunPtr)
import qualified LLVM.AST as AST
import qualified LLVM.Context as LLVM
import qualified LLVM.ExecutionEngine as LLVM
import qualified LLVM.Module as LLVM
import qualified LLVM.Target as LLVM
import           System.IO (IOMode(..), hPutStrLn, openFile, stdout)
import           Text.Printf (printf)

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
interpret code = run' =<< VM.replicate memSize 0 where
  run' mem = go 0 0 where
    -- to improve performance we use unsafe vector operations
    -- everywhere, and do bounds checking only where necessary; in
    -- particular, well-formed IR cannot have the ip go out of range,
    -- so we can always unsafely index into the code
    go !ip !dp = case V.unsafeIndex code ip of
      -- dp = (dp + w), bounded to (memSize - 1)
      GoR w ->
        let dp' = dp + fromIntegral w
        in go (ip+1) (if dp' >= memSize then memSize-1 else dp')

      -- dp = (dp - w), bounded to 0
      GoL w ->
        let dp' = dp - fromIntegral w
        in go (ip+1) (if dp' < 0 then 0 else dp')

      -- mem[dp] = (mem[dp] + w), wrapping
      Inc w -> do
        VM.unsafeModify mem (+w) dp
        go (ip+1) dp

      -- mem[dp] = (mem[dp] - w), wrapping
      Dec w -> do
        VM.unsafeModify mem (subtract w) dp
        go (ip+1) dp

      -- mem[dp] = w
      Set w -> do
        VM.unsafeWrite mem dp w
        go (ip+1) dp

      -- ip = ((mem[dp] == 0 ? a : ip) + 1)
      JZ a -> do
        w <- VM.unsafeRead mem dp
        go (if w == 0 then fromIntegral a + 1 else ip + 1) dp

      -- ip = ((mem[dp] == 0 ? ip : a) + 1)
      JNZ a -> do
        w <- VM.unsafeRead mem dp
        go (if w == 0 then ip + 1 else fromIntegral a + 1) dp

      -- putchar(mem[dp])
      PutCh -> do
        w <- chr . fromIntegral <$> VM.unsafeRead mem dp
        putChar w
        go (ip+1) dp

      -- mem[dp] = getchar()
      GetCh -> do
        w <- fromIntegral . ord <$> getChar
        VM.unsafeWrite mem dp w
        go (ip+1) dp

      -- stop
      Hlt -> pure ()

      -- unreachable if the IR is well-formed
      instr -> error ("invalid opcode: " ++ show (fst (unpack8 instr)))

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
dumpir mfname ir = do
    h <- maybe (pure stdout) (`openFile` WriteMode) mfname
    V.ifoldM'_ (go h) 0 ir
  where
    go h lvl ip instr =
      let prn = hPutStrLn h . printf "%.4d %s %s" ip (replicate lvl '\t')
      in case instr of
        GoR w -> prn ("GoR  " ++ show w) >> pure lvl
        GoL w -> prn ("GoL  " ++ show w) >> pure lvl
        Inc w -> prn ("Inc  " ++ show w) >> pure lvl
        Dec w -> prn ("Dec  " ++ show w) >> pure lvl
        Set w -> prn ("Set  " ++ show w) >> pure lvl
        JZ  a -> prn ("JZ  @" ++ show a) >> pure (lvl + 1)
        JNZ a -> prn ("JNZ @" ++ show a) >> pure (lvl - 1)
        PutCh -> prn "PutCh" >> pure lvl
        GetCh -> prn "GetCh" >> pure lvl
        Hlt   -> prn "Hlt" >> pure lvl
        _     -> error ("invalid opcode: " ++ show (fst (unpack8 instr)))

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
compile s0 = V.create (compile' (filter isbf s0)) where
  -- filter out non-bf characters so that the run-length encoding is
  -- simpler
  isbf c = c `elem` "><+-.,[]"

  -- allocate a mutable vector and write each instruction in turn into
  -- it
  compile' scode = do
    vcode <- VM.unsafeNew chunkSize
    go vcode 0 chunkSize [] scode

  -- if there's no space left, grow the vector
  go vcode ip 0 stk cs = do
    vcode' <- VM.unsafeGrow vcode chunkSize
    go vcode' ip chunkSize stk cs

  -- if there's no source code left, write a 'Hlt' instruction,
  -- truncate any extra space in the vector, and return it
  go vcode ip _ _ [] = do
    VM.unsafeWrite vcode ip Hlt
    pure (VM.unsafeSlice 0 (ip+1) vcode)

  -- compile an instruction: 'vcode' is the output vector; 'ip' is the
  -- instruction pointer for this instruction (which is the same as
  -- the number of instructions compiled so far); 'sz' is the
  -- remaining space in the vector; 'stk' is a stack of loop start
  -- addresses; 'c' is the current instruction and 'cs' is the list of
  -- later instructions
  go vcode !ip !sz stk (c:cs) =
    let
      -- push an instruction with no operand into the vector and
      -- continue with the later instructions
      pushi instr = do
        VM.unsafeWrite vcode ip instr
        go vcode (ip+1) (sz-1) stk cs

      -- push an instruction into the vector, where the operand is the
      -- number of times the current instruction occurs (run-length
      -- encoding); this means that (eg) "+++" will be compiled to a
      -- single @Inc 3@, rather than three @Inc 1@s
      pushir instr = do
        let (eqs, rest) = span (==c) cs
        VM.unsafeWrite vcode ip (instr (1 + fromIntegral (length eqs)))
        go vcode (ip+1) (sz-1) stk rest
    in case c of
         '>' -> pushir GoR
         '<' -> pushir GoL
         '+' -> pushir Inc
         '-' -> pushir Dec
         '.' -> pushi PutCh
         ',' -> pushi GetCh
         '[' -> case cs of
           -- compile "[-]" and "[+]" to a @Set 0@ instruction
           ('-':']':cs') -> do
             VM.unsafeWrite vcode ip (Set 0)
             go vcode (ip+1) (sz-1) stk cs'
           ('+':']':cs') -> do
             VM.unsafeWrite vcode ip (Set 0)
             go vcode (ip+1) (sz-1) stk cs'
           -- otherwise, write a 'Hlt' for now and push the ip to the
           -- stack
           _ -> do
             VM.unsafeWrite vcode ip Hlt
             go vcode (ip+1) (sz-1) (ip:stk) cs
         ']' -> case stk of
           -- replace the "[" (which was compiled to a 'Hlt') with a
           -- @JZ <here>@, write a @JNZ <there>@, and pop the stack;
           -- this is correct as the ip is incremented after every
           -- instruction (even a jump) in the interpreter, and the
           -- 'llcompile' function mimics this
           (p:ps) -> do
             VM.unsafeWrite vcode p  (JZ  $ fromIntegral ip)
             VM.unsafeWrite vcode ip (JNZ $ fromIntegral p)
             go vcode (ip+1) (sz-1) ps cs
           -- if there isn't a matching "[", just ignore the "]"
           [] -> go vcode ip sz stk cs
         _ -> go vcode ip sz stk cs

  -- grow the vector in chunks of 256 instructions, to avoid very
  -- frequent reallocation
  chunkSize = 256

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

-- | The size of the heap
memSize :: Int
memSize = 30000

-- | Plumbing to call the JIT-compiled code.
foreign import ccall "dynamic" haskFun :: FunPtr (IO ()) -> IO ()
