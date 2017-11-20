{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | The Quickie Brainfuck parser and compiler.
module Language.Brainfuck where

import qualified Control.Concurrent as C
import           Control.Exception (try)
import           Control.Monad (void)
import           Data.Bits ((.|.), (.&.), unsafeShiftL, unsafeShiftR)
import qualified Data.ByteString.Char8 as BS
import           Data.Char (chr, ord)
import qualified Data.IntMap.Strict as M
import           Data.String (IsString(..))
import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Unboxed.Mutable as VM
import qualified Data.Vector.Storable.Mutable as VSM
import qualified Data.Word as W
import qualified Foreign.Ptr as F
import qualified LLVM.Analysis as LLVM
import qualified LLVM.AST as AST hiding (type')
import qualified LLVM.AST.CallingConvention as AST
import qualified LLVM.AST.Constant as ASTC
import qualified LLVM.AST.Global as AST
import qualified LLVM.AST.IntegerPredicate as AST
import qualified LLVM.AST.Linkage as AST
import qualified LLVM.AST.Type as AST
import qualified LLVM.Context as LLVM
import qualified LLVM.Exception as LLVM
import qualified LLVM.Module as LLVM
import qualified LLVM.OrcJIT as LLVM
import qualified LLVM.Internal.OrcJIT as LLVM
import qualified LLVM.PassManager as LLVM
import qualified LLVM.Target as LLVM
import qualified LLVM.Transforms as LLVM
import           System.IO (IOMode(..), hFlush, hPutStrLn, openFile, stdout)
import           System.IO.Error (isEOFError)
import           Text.Printf (printf)

-------------------------------------------------------------------------------
-- * Quickie IR

-- | Instructions are 64-bit words, from least to most significant
-- bits:
--
-- *  8 bit *op*code
-- * 32 bit *a*bsolute address (optional)
-- * 16 bit *r*elative address (optional)
-- *  8 bit operand *b*yte     (optional)
--
-- Well-formed instructions are those constructed by the pattern
-- synonyms.  Any other instruction is ill-formed and may lead to a
-- runtime error.
type Instruction = W.Word64

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
pattern GoR r <- (unpack -> (0, _, r, _)) where GoR r = pack 0 0 r 0

-- | Move the data pointer to the \"left\" (beginning) of the memory
-- array.
--
-- The operand is how far to move by.
pattern GoL :: W.Word16 -> Instruction
pattern GoL r <- (unpack -> (1, _, r, _)) where GoL r = pack 1 0 r 0

-- | Increment (with wrapping) the value under the data pointer.
--
-- The operand is how much to increment by.
pattern Inc :: W.Word8 -> Instruction
pattern Inc b <- (unpack -> (2, _, _, b)) where Inc b = pack 2 0 0 b

-- | Decrement (with wrapping) the value under the data pointer.
--
-- The operand is how much to decrement by.
pattern Dec :: W.Word8 -> Instruction
pattern Dec b <- (unpack -> (3, _, _, b)) where Dec b = pack 3 0 0 b

-- | Set the value under the data pointer to a constant.
--
-- The operand is the value to set.
pattern Set :: W.Word8 -> Instruction
pattern Set b <- (unpack -> (4, _, _, b)) where Set b = pack 4 0 0 b

-- | Add the value of the current cell to another (given by dp offset
-- to the right) with a multiplier.
pattern CMulR :: W.Word16 -> W.Word8 -> Instruction
pattern CMulR r b <- (unpack -> (10, _, r, b)) where CMulR r b = pack 10 0 r b

-- | Add the value of the current cell to another (given by dp offset
-- to the left) with a multiplier.
pattern CMulL :: W.Word16 -> W.Word8 -> Instruction
pattern CMulL r b <- (unpack -> (11, _, r, b)) where CMulL r b = pack 11 0 r b

-- | Jump if the value under the data pointer is zero.
--
-- The operand is the address to jump to.  The address should not
-- exceed @2^28-1@.
pattern JZ :: W.Word32 -> Instruction
pattern JZ a <- (unpack -> (5, a, _, _)) where JZ a = pack 5 a 0 0

-- | Jump if the value under the data pointer is nonzero.
--
-- The operand is the address to jump to.  The address should not
-- exceed @2^28-1@.
pattern JNZ :: W.Word32 -> Instruction
pattern JNZ a <- (unpack -> (6, a, _, _)) where JNZ a = pack 6 a 0 0

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
interpret = interpretWithJIT Nothing

-- | JIT compile and execute an LLVM IR program.
--
-- This will use 'interpret' initially and compile the program in a
-- separate thread.  It will switch to the compiled code as it
-- completes.
jit :: IR -> IO ()
jit code = do
    putcharPtr <- haskFunPut putchar_c
    getcharPtr <- haskFunGet getchar_c
    fnvar   <- C.newEmptyMVar
    killvar <- C.newEmptyMVar
    _ <- C.forkIO (jitCompile putcharPtr getcharPtr fnvar killvar)
    interpretWithJIT (Just fnvar) code
    C.putMVar killvar ()
    F.freeHaskellFunPtr putcharPtr
    F.freeHaskellFunPtr getcharPtr
  where
    jitCompile putPtr getPtr fnvar killvar = runLLVM go (llcompileForJIT code) where
      go tgt m =
        LLVM.withObjectLinkingLayer $ \ol ->
        LLVM.withIRCompileLayer ol tgt $ \cl ->
        LLVM.withModule cl m (resolver cl) $ \_ -> do
          vo <- C.newEmptyMVar
          C.putMVar fnvar vo
          let loop = do
                (ip, vr) <- C.takeMVar vo
                sym <- LLVM.mangleSymbol cl (fromString $ show ip)
                LLVM.JITSymbol fn _ <- LLVM.findSymbol cl sym True
                if fn == 0
                  -- couldn't find function, try again
                  then do
                    C.putMVar vr (Left JITNoSuchFunc)
                    loop
                  else do
                    C.putMVar vr . Right $ haskFun (F.castPtrToFunPtr (F.wordPtrToPtr fn))
                    -- LLVM context is destroyed when the action
                    -- terminates, so keep the thread alive
                    C.takeMVar killvar
          loop

      resolver cl = LLVM.SymbolResolver (\s -> LLVM.findSymbol cl s True) $ \(LLVM.MangledSymbol s) -> pure $ if
        | s == fromString "putchar" -> LLVM.JITSymbol (F.ptrToWordPtr $ F.castFunPtrToPtr putPtr) (LLVM.JITSymbolFlags False True)
        | s == fromString "getchar" -> LLVM.JITSymbol (F.ptrToWordPtr $ F.castFunPtrToPtr getPtr) (LLVM.JITSymbolFlags False True)
        | otherwise -> LLVM.JITSymbol 0 (LLVM.JITSymbolFlags False False)

    putchar_c w = putChar (chr (fromIntegral w)) >> pure 0
    getchar_c = do
      hFlush stdout
      try getChar >>= \case
        Right w -> pure (fromIntegral (ord w))
        Left e
          | isEOFError e -> pure 0
          | otherwise    -> pure 0 -- maybe distinguish these cases?

-- | Helper for 'interpret' and 'jit': starts interpreting the IR,
-- periodically checking if the JIT-compiled version is ready.
--
-- If an @MVar@ is provided, it will be checked (non-blockingly) at
-- the end of every loop.  If it contains a function pointer at that
-- time, then it shall call the function to jump to the compiled code.
--
-- You should not call this directly.
interpretWithJIT
  :: Maybe (C.MVar (C.MVar (W.Word32, C.MVar (Either JITError (F.Ptr W.Word8 -> W.Word16 -> IO ())))))
  -> IR
  -> IO ()
interpretWithJIT fnvar code = run' =<< VSM.replicate memSize 0 where
  run' mem = go 0 initialdp where
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
        VSM.unsafeModify mem (+w) dp
        go (ip+1) dp

      -- mem[dp] = (mem[dp] - w), wrapping
      Dec w -> do
        VSM.unsafeModify mem (subtract w) dp
        go (ip+1) dp

      -- mem[dp] = w
      Set w -> do
        VSM.unsafeWrite mem dp w
        go (ip+1) dp

      -- mem[dp+a] = mem[dp+a] + mem[dp] * i
      CMulR a w -> do
        let dp' = dp + fromIntegral a
        x <- VSM.unsafeRead mem dp
        VSM.unsafeModify mem (\y -> y + x * w) (if dp' >= memSize then memSize-1 else dp')
        go (ip+1) dp

      -- mem[dp-a] = mem[dp-a] + mem[dp] * i
      CMulL a w -> do
        let dp' = dp - fromIntegral a
        x <- VSM.unsafeRead mem dp
        VSM.unsafeModify mem (\y -> y + x * w) (if dp' < 0 then 0 else dp')
        go (ip+1) dp

      -- ip = ((mem[dp] == 0 ? a : ip) + 1)
      JZ a -> do
        w <- VSM.unsafeRead mem dp
        let tgt = if w == 0 then fromIntegral a else ip
        tryjit tgt dp

      -- ip = ((mem[dp] == 0 ? ip : a) + 1)
      JNZ a -> do
        w <- VSM.unsafeRead mem dp
        let tgt = if w == 0 then ip else fromIntegral a
        tryjit tgt dp

      -- putchar(mem[dp])
      PutCh -> do
        w <- chr . fromIntegral <$> VSM.unsafeRead mem dp
        putChar w
        go (ip+1) dp

      -- mem[dp] = getchar()
      GetCh -> do
        hFlush stdout
        w <- fromIntegral . ord <$> getChar
        VSM.unsafeWrite mem dp w
        go (ip+1) dp

      -- stop
      Hlt -> pure ()

      -- unreachable if the IR is well-formed
      instr -> error ("invalid opcode: " ++ show (instr .&. 255))

    -- switch to the JIT if it's ready
    tryjit tgt dp = case fnvar of
      Just fnvar' -> C.tryReadMVar fnvar' >>= \case
        Just vo -> VSM.unsafeWith mem $ \memptr -> do
          vr <- C.newEmptyMVar
          C.putMVar vo (fromIntegral tgt, vr)
          C.takeMVar vr >>= \case
            -- if we can't find the function, llvm may have merged it
            -- with another or renamed it (it does that with
            -- LostKng.b); but the next function we want might be
            -- present.
            Left JITNoSuchFunc -> go (tgt + 1) dp
            Right fn -> fn memptr (fromIntegral dp)
        Nothing -> go (tgt + 1) dp
      Nothing -> go (tgt + 1) dp


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
          s :: String -> Maybe W.Word32 -> Maybe W.Word16 -> Maybe W.Word8 -> IO ()
          s opname ma mr mb = prn $
            opname ++
            maybe [] (\a -> " @" ++ show a) ma ++
            maybe [] (\r -> " +" ++ show r) mr ++
            maybe [] (\b -> " "  ++ show b) mb
      in case instr of
        CMulL   r b -> s "CMulL" Nothing  (Just r) (Just b) >> pure lvl
        CMulR   r b -> s "CMulR" Nothing  (Just r) (Just b) >> pure lvl
        Dec       b -> s "Dec"   Nothing  Nothing  (Just b) >> pure lvl
        GetCh       -> s "GetCh" Nothing  Nothing  Nothing  >> pure lvl
        GoL     r   -> s "GoL"   Nothing  (Just r) Nothing  >> pure lvl
        GoR     r   -> s "GoR"   Nothing  (Just r) Nothing  >> pure lvl
        Hlt         -> s "Hlt"   Nothing  Nothing  Nothing  >> pure lvl
        Inc       b -> s "Inc"   Nothing  Nothing  (Just b) >> pure lvl
        JNZ   a     -> s "JNZ"   (Just a) Nothing  Nothing  >> pure (lvl - 1)
        JZ    a     -> s "JZ"    (Just a) Nothing  Nothing  >> pure (lvl + 1)
        PutCh       -> s "PutCh" Nothing  Nothing  Nothing  >> pure lvl
        Set       b -> s "Set"   Nothing  Nothing  (Just b) >> pure lvl
        _ -> error ("invalid opcode: " ++ show (instr .&. 255))

-- | Dump the LLVM IR to stdout or a file.
dumpllvm :: Maybe String -> AST.Module -> IO ()
dumpllvm (Just fname) = runLLVM $ \_ m -> LLVM.writeLLVMAssemblyToFile (LLVM.File fname) m
dumpllvm Nothing      = runLLVM $ \_ m -> LLVM.moduleLLVMAssembly m >>= BS.putStrLn

-- | Dump the LLVM-compiled assembly to stdout or a file.
dumpasm :: Maybe String -> AST.Module -> IO ()
dumpasm (Just fname) = runLLVM $ \tgt m -> LLVM.writeTargetAssemblyToFile tgt (LLVM.File fname) m
dumpasm Nothing      = runLLVM $ \tgt m -> LLVM.moduleTargetAssembly tgt m >>= BS.putStrLn

-- | Dump the LLVM-compiled object code to a file.
objcompile :: String -> AST.Module -> IO ()
objcompile fname = runLLVM $ \tgt m -> LLVM.writeObjectToFile tgt (LLVM.File fname) m


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
      pushi instr = pushi' instr cs

      -- pushi, but takes the instruction sequence to continue from
      pushi' instr rest = do
        VM.unsafeWrite vcode ip instr
        go vcode (ip+1) (sz-1) stk rest

      -- push an instruction into the vector, where the operand is the
      -- number of times the current instruction occurs (run-length
      -- encoding); this means that (eg) "+++" will be compiled to a
      -- single @Inc 3@, rather than three @Inc 1@s
      pushir instr = do
        let (eqs, rest) = span (==c) cs
        VM.unsafeWrite vcode ip (instr (1 + fromIntegral (length eqs)))
        go vcode (ip+1) (sz-1) stk rest

      -- see if a loop body corresponds to a known pattern:
      --
      -- - a loop which just adds or subtracts from the current cell
      --   and doesn't move the data pointer will zero the current
      --   cell, if the delta is nonzero
      --
      -- - a loop which adds to some other cells and decrements the
      --   current cell by one is a copy/multiply loop
      loop l0 = lgo (0 :: Int) (0 :: Int) (M.empty :: M.IntMap Int) l0 where
        lgo dpoff delta factors ('>':ls) = lgo (dpoff+1) delta factors ls
        lgo dpoff delta factors ('<':ls) = lgo (dpoff-1) delta factors ls
        lgo dpoff delta factors ('-':ls)
          | dpoff == 0 = lgo dpoff (delta-1) factors ls
          | otherwise  = lgo dpoff delta (M.alter (Just . maybe (-1) (subtract 1)) dpoff factors) ls
        lgo dpoff delta factors ('+':ls)
          | dpoff == 0 = lgo dpoff (delta+1) factors ls
          | otherwise  = lgo dpoff delta (M.alter (Just . maybe 1 (+1)) dpoff factors) ls
        lgo 0 delta factors (']':ls)
          | M.null factors && delta /= 0 = pushi' (Set 0) ls
          | delta == -1 && all (>=0) (M.elems factors) = do
              (vcode', sz') <- if sz < 1 + M.size factors
                               then (\v' -> (v', sz + chunkSize)) <$> VM.unsafeGrow vcode chunkSize
                               else pure (vcode, sz)
              let cmul dpoff factor = if dpoff < 1
                                      then CMulL (fromIntegral $ abs dpoff) (fromIntegral factor)
                                      else CMulR (fromIntegral dpoff) (fromIntegral factor)
              let (ip', m) = M.foldrWithKey' (\dpoff factor (ip_, m_) -> (ip_ + 1, m_ >> VM.unsafeWrite vcode' ip_ (cmul dpoff factor))) (ip, pure ()) factors
              m
              VM.unsafeWrite vcode' ip' (Set 0)
              go vcode' (ip'+1) (sz' - M.size factors - 1) stk ls
          | otherwise = defloop l0
        lgo _ _ _ _ = defloop l0

        -- a regular loop starter
        defloop rest = do
          VM.unsafeWrite vcode ip Hlt
          go vcode (ip+1) (sz-1) (ip:stk) rest
    in case c of
         '>' -> pushir GoR
         '<' -> pushir GoL
         '+' -> pushir Inc
         '-' -> pushir Dec
         '.' -> pushi PutCh
         ',' -> pushi GetCh
         '[' -> loop cs
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

-- | Compile a Quickie IR program to LLVM IR, as a standalone program.
--
-- This produces a function callable from C with the type @bfmain ::
-- (uint8_t**, uint32_t) -> uint32_t@.  The first parameter is the
-- memory array, the second is the starting data pointer address.
--
-- With a memory array of 40,000 cells and an initial data pointer of
-- 10,000 (to make it a bit less likely for programs to run out of
-- bounds and crash), the following C shim can be used to produce an
-- executable program:
--
-- @
--    char mem[40000] = {0};
--
--    void bfmain(char**, int);
--
--    int main(void) {
--      return bfmain((char**)&mem, 10000);
--    }
-- @
--
-- Build with @quickie foo.b -o foo.o; gcc main.c foo.o -o foo@.
llcompileForStandalone :: IR -> AST.Module
llcompileForStandalone code = AST.defaultModule
  { AST.moduleDefinitions =
    [ AST.GlobalDefinition $ llcompileFun (AST.mkName bfmain) code
    , extern getchar []        AST.i32
    , extern putchar [AST.i32] AST.i32
    ]
  }

-- | Compile a Quickie IR program to LLVM IR, to be invoked from the
-- JIT interpreter.
--
-- You should not call this directly.
llcompileForJIT :: IR -> AST.Module
llcompileForJIT code = AST.defaultModule
    { AST.moduleDefinitions = map blockToFun (llcompileFunBBs True code) ++
      [ extern getchar []        AST.i32
      , extern putchar [AST.i32] AST.i32
      ]
    }
  where
    blockToFun (b@(AST.BasicBlock name _ _)) =
      AST.GlobalDefinition $ llblocksToFun name [b]

-- | Compile a sequence of instructions into a function.
--
-- You should not call this directly.
llcompileFun :: AST.Name -> IR -> AST.Global
llcompileFun name = llblocksToFun name . llcompileFunBBs False

-- | Convert a sequence of basic blocks to a function.
--
-- You should not call this directly.
llblocksToFun :: AST.Name -> [AST.BasicBlock] -> AST.Global
llblocksToFun name blocks = AST.functionDefaults
  { AST.name        = name
  , AST.parameters  = ([AST.Parameter ty n [] | (ty, n) <- [(AST.ptr $ AST.ArrayType (fromIntegral memSize) AST.i8, memname), (AST.i16, diname)]], False)
  , AST.returnType  = AST.void
  , AST.basicBlocks = blocks
  }

-- | Helper for 'llcompileFun'.
--
-- You should not call this directly.
llcompileFunBBs :: Bool -> IR -> [AST.BasicBlock]
llcompileFunBBs blocksAreFuns code = reverse blocks where
  -- an LLVM function consists of a sequence of "basic blocks", where
  -- a basic block is a sequence of instructions followed by a single
  -- terminator.  jumping to or from the middle of a basic block is
  -- not possible.
  --
  -- we're going to construct the sequence of instructions of a basic
  -- block in reverse, as prepending to a list is efficient; but then
  -- the list must be reversed when a block is completed
  --
  -- LLVM does mutable state by pointers; local variables are
  -- immutable.  so we're going to store the data pointer (as an index
  -- into the mem array) behind a pointer (so a value of type *i16)
  -- and load/store it when necessary; but in the simple case that
  -- leads to a lot of loads and stores as every instruction uses the
  -- cell the data pointer points to.  we can reduce these loads and
  -- stores by keeping around the data pointer in an immutable
  -- variable, creating a fresh variable every time we do a 'GoL' or
  -- 'GoR'; then we just load it once at the start of a basic block
  -- and store it once (if it changed at all!) at the end.  this saves
  -- about 3000 loads/stores in the mandelbrot program, and enables
  -- llvm's "mem2reg" optimisation which pushes the data pointer into
  -- a register, so it's a good optimisation to do.
  header =
    [ store dp (refm16 (AST.mkName "dp0"))
    , AST.mkName "dp0" .= add (cint16 0) (refm16 diname)
    , AST.mkName "dp"  .= AST.Alloca AST.i16 Nothing 0 []
    ]

  -- as long as the IR is well formed, the final block will end
  -- with a ret and there will be no leftover instructions
  (_, _, _, _, blocks) = V.ifoldl' gen ("entry", [], Clean (AST.mkName "dp0"), Nothing, []) code

  -- generate code, the arguments are: 'n', the name of the current
  -- basic block; 'ops', the (reverse order) list of instructions in
  -- the current basic block; 'dpT', the name of the immutable
  -- variable currently holding the data pointer; 'dpV', the name of
  -- the immutable variable last stored to the memory referenced by
  -- the data pointer (if known) and the postponed store instruction;
  -- 'bs', the (reverse order) list of previous blocks (with the
  -- instructions of each in the correct order).

  -- %dpT' = add %dpT, w          -- also execute a postponed store
  gen (n, ops, dpT, dpV, bs) ip (GoR w) =
    let final = AST.mkName (show ip ++ ".F")
        ops' =
          [ final .= add (refm16 (tname dpT)) (cint16 w)
          ] ++ maybe [] ((:[]) . snd) dpV ++ ops
    in (n, ops', Dirty final, Nothing, bs)

  -- %dpT' = sub %dpT, w          -- also execute a postponed store
  gen (n, ops, dpT, dpV, bs) ip (GoL w) =
    let final = AST.mkName (show ip ++ ".F")
        ops' =
          [ final .= sub (refm16 (tname dpT)) (cint16 w)
          ] ++ maybe [] ((:[]) . snd) dpV ++ ops
    in (n, ops', Dirty final, Nothing, bs)

  -- %tmpP = gep mem [0, %dpT]
  -- %tmp1 = load %tmpP           -- or just %dpV, if known
  -- %tmp2 = add %tmp1, w
  -- store %tmpP, %tmp2           -- store is postponed until next GoL, GoR, JZ, or JNZ
  gen (n, ops, dpT, dpV, bs) ip (Inc w) = incdec n ops dpT dpV bs ip w add

  -- %tmpP = gep mem [0, %dpT]
  -- %tmp1 = load %tmpP           -- or just %dpV, if known
  -- %tmp2 = sub %tmp1, w
  -- store %tmpP, %tmp2           -- store is postponed until next GoL, GoR, JZ, or JNZ
  gen (n, ops, dpT, dpV, bs) ip (Dec w) = incdec n ops dpT dpV bs ip w sub

  -- %tmpP = gep mem [0, %dpT]
  -- %tmp1 = load %tmpP           -- or just %dpV, if known
  -- %tmp2 = mul %tmp1, w
  -- %tmp3 = add %gpT, a
  -- %tmp4 = gep mem [0, %tmp3]
  -- %tmp5 = load %tmp4
  -- %tmp6 = add %tmp5, %tmp2
  -- store %tmp4, %tmp6
  gen (n, ops, dpT, dpV, bs) ip (CMulR a w) = cmul n ops dpT dpV bs ip a w add

  -- %tmpP = gep mem [0, %dpT]
  -- %tmp1 = load %tmpP           -- or just %dpV, if known
  -- %tmp2 = mul %tmp1, w
  -- %tmp3 = add %gpT, a
  -- %tmp4 = gep mem [0, %tmp3]
  -- %tmp5 = load %tmp4
  -- %tmp6 = add %tmp5, %tmp2
  -- store %tmp4, %tmp6
  gen (n, ops, dpT, dpV, bs) ip (CMulL a w) = cmul n ops dpT dpV bs ip a w sub

  -- %tmpP = gep mem [0, %dpT]
  -- %tmp1 = w
  -- store %tmpP, %tmp1           -- store is postponed until next GoL, GoR, JZ, or JNZ
  gen (n, ops, dpT, _, bs) ip (Set w) =
    let tmpP = AST.mkName (show ip ++ ".P")
        tmp1 = AST.mkName (show ip ++ ".T1")
        ops' =
          [ tmp1 .= add (cint8 0) (cint8 w)
          , tmpP .= gepmem (tname dpT)
          ] ++ ops
    in (n, ops', dpT, Just (tmp1, store (refp tmpP) (refm tmp1)), bs)

  -- %tmpP = gep mem [0, %dpT]
  -- %tmp1 = load %tmpP           -- or just %dpV, if known
  -- %tmp2 = icmp eq 0, %tmp1
  -- cbr %tmp2, TRUE, FALSE       -- also execute a postponed store
  gen (n, ops, dpT, dpV, bs) ip (JZ a) = jmp n ops dpT dpV bs ip (show a) (show ip)

  -- %tmpP = gep mem [0, %dpT]
  -- %tmp1 = load %tmpP           -- or just %dpV, if known
  -- %tmp2 = icmp eq 0, %tmp1
  -- cbr %tmp2, FALSE, TRUE       -- also execute a postponed store
  gen (n, ops, dpT, dpV, bs) ip (JNZ a) = jmp n ops dpT dpV bs ip (show ip) (show a)

  -- %tmpP = gep mem [0, %dpT]
  -- %tmp1 = load %tmpP           -- or just %dpV, if known
  -- %tmp2 = zext %tmp1
  -- call "putchar" %tmp2
  gen (n, ops, dpT, dpV, bs) ip PutCh =
    let tmpP = AST.mkName (show ip ++ ".P")
        tmp1 = AST.mkName (show ip ++ ".T1")
        tmp2 = AST.mkName (show ip ++ ".T2")
        ops' = AST.Do (call (gname (funty [AST.i32] AST.i32) putchar) [refm32 tmp2]) : (case dpV of
          Just (var, _) ->
             [ tmp2 .= zext (refm var) AST.i32 ]
          Nothing ->
            [ tmp2 .= zext (refm tmp1) AST.i32
            , tmp1 .= load (refp tmpP)
            , tmpP .= gepmem (tname dpT)
            ]) ++ ops
    in (n, ops', dpT, dpV, bs)

  -- %tmpP = gep mem [0, %dpT]
  -- %tmp1 = call "getchar"
  -- %tmp2 = trunc %tmp1
  -- store %tmpP, %tmp2           -- store is postponed until next GoL, GoR, JZ, or JNZ
  gen (n, ops, dpT, _, bs) ip GetCh =
    let tmpP = AST.mkName (show ip ++ ".P")
        tmp1 = AST.mkName (show ip ++ ".T1")
        tmp2 = AST.mkName (show ip ++ ".T2")
        ops' =
          [ tmp2 .= trunc (refm32 tmp1) AST.i8
          , tmp1 .= call (gname (funty [] AST.i32) getchar) []
          , tmpP .= gepmem (tname dpT)
          ] ++ ops
    in (n, ops', dpT, Just (tmp2, store (refp tmpP) (refm tmp2)), bs)

  -- ret
  gen (n, ops, dpT, _, bs) ip Hlt =
    let b = mkblock n ops (AST.Ret Nothing [])
    in (show ip, [], dpT, Nothing, b : bs)

  -- unreachable if the IR is well-formed
  gen _ _ instr = error ("invalid opcode: " ++ show (instr .&. 255))

  -- reference to an external name
  gname ty = AST.ConstantOperand . ASTC.GlobalReference ty

  refm = AST.LocalReference AST.i8

  -- reference to an i16
  refm16 = AST.LocalReference AST.i16

  -- reference to an i32
  refm32 = AST.LocalReference AST.i32

  -- reference to a *i8
  refp = AST.LocalReference (AST.ptr AST.i8)

  -- reference to a bool
  refb = AST.LocalReference AST.i1

  (.=) = (AST.:=)

  -- the data pointer
  dp = AST.LocalReference (AST.ptr AST.i16) (AST.mkName "dp")

  -- the global memory
  mem = AST.LocalReference (AST.ArrayType (fromIntegral memSize) AST.i8) memname

  -- index into the global memory
  gepmem idx = gep mem [cint8 0, refm16 idx]

  -- a helper for 'Inc' / 'Dec', as they use the same logic but differ
  -- in the arithmetic instruction used
  incdec n ops dpT dpV bs ip w llop =
    let tmpP = AST.mkName (show ip ++ ".P")
        tmp1 = AST.mkName (show ip ++ ".T1")
        tmp2 = AST.mkName (show ip ++ ".T2")
        ops' = (case dpV of
          Just (var, _) ->
            [ tmp2 .= llop (refm var) (cint8 w) ]
          Nothing ->
            [ tmp2 .= llop (refm tmp1) (cint8 w)
            , tmp1 .= load (refp tmpP)
            ]) ++ ((tmpP .= gepmem (tname dpT)) : ops)
    in (n, ops', dpT, Just (tmp2, store (refp tmpP) (refm tmp2)), bs)

  -- a helper for 'CMulR' / 'CMulL', as they use the same logic but
  -- differ in the direction of pointer movement
  cmul n ops dpT dpV bs ip a w llop =
    let tmpP = AST.mkName (show ip ++ ".P")
        tmp1 = AST.mkName (show ip ++ ".T1")
        tmp2 = AST.mkName (show ip ++ ".T2")
        tmp3 = AST.mkName (show ip ++ ".T3")
        tmp4 = AST.mkName (show ip ++ ".T4")
        tmp5 = AST.mkName (show ip ++ ".T5")
        tmp6 = AST.mkName (show ip ++ ".T6")
        ops' =
          [ store (refp tmp4) (refm tmp6)
          , tmp6 .= add (refm tmp5) (refm tmp2)
          , tmp5 .= load (refp tmp4)
          , tmp4 .= gepmem tmp3
          , tmp3 .= llop (refm16 (tname dpT)) (cint16 a)
          ] ++ (case dpV of
          Just (var, _) ->
            [ tmp2 .= mul (refm var) (cint8 w) ]
          Nothing ->
            [ tmp2 .= mul (refm tmp1) (cint8 w)
            , tmp1 .= load (refp tmpP)
            , tmpP .= gepmem (tname dpT)
            ]) ++ ops
    in (n, ops', dpT, dpV, bs)

  -- a helper for 'JZ' / 'JNZ', as they use the same comparison but
  -- just swap the true and false cases
  jmp n ops dpT dpV bs ip true false =
    let tmpP = AST.mkName (show ip ++ ".P")
        tmp1 = AST.mkName (show ip ++ ".T1")
        tmp2 = AST.mkName (show ip ++ ".T2")
        tmpK = AST.mkName (show ip ++ ".K")
        dp0  = AST.mkName ("dp" ++ show ip)
        truename  = AST.mkName true
        falsename = AST.mkName false
        storedp = case dpT of
          Clean _ -> []
          Dirty _ -> [ store dp (refm16 (tname dpT)) ]
        term
          | blocksAreFuns = AST.Ret Nothing []
          | otherwise = AST.CondBr (refb tmp2) truename falsename []
        select
          | blocksAreFuns =
            [ AST.Do $ callblock dpT (AST.LocalReference callblockty tmpK)
            , tmpK .= AST.Select (refb tmp2) (gname callblockty truename) (gname callblockty falsename) []
            ]
          | otherwise = []
        ops' = select ++ (case dpV of
          Just (var, st) ->
            [ st
            , tmp2 .= AST.ICmp AST.EQ (cint8 0) (refm var) []
            ]
          Nothing ->
            [ tmp2 .= AST.ICmp AST.EQ (cint8 0) (refm tmp1) []
            , tmp1 .= load (refp tmpP)
            , tmpP .= gepmem (tname dpT)
            ]) ++ storedp ++ ops
        b = mkblock n ops' term
    in (show ip, [dp0 .= load dp], Clean dp0, Nothing, b : bs)

  -- call a block
  callblockty     = funty [AST.ptr $ AST.ArrayType (fromIntegral memSize) AST.i8, AST.i16] AST.void
  callblock dpT n = notailcall n [mem, refm16 (tname dpT)]

  -- make a block
  mkblock n ops term
    | blocksAreFuns || n == "entry" = block (AST.mkName n) (ops ++ header) term
    | otherwise = block (AST.mkName n) ops term

-------------------------------------------------------------------------------
-- * Internal utilities

-- | Pack an instruction from its components.
--
-- You should not use this directly.
pack :: W.Word8 -> W.Word32 -> W.Word16 -> W.Word8 -> Instruction
pack op a r b =
  fromIntegral op .|.
  unsafeShiftL (fromIntegral a)  8 .|.
  unsafeShiftL (fromIntegral r) 40 .|.
  unsafeShiftL (fromIntegral b) 56

-- | Unpack an instruction.
unpack :: Instruction -> (W.Word8, W.Word32, W.Word16, W.Word8)
unpack instr =
  ( fromIntegral $              instr    .&.        255
  , fromIntegral $ unsafeShiftR instr  8 .&. 4294967295
  , fromIntegral $ unsafeShiftR instr 40 .&.      65535
  , fromIntegral $ unsafeShiftR instr 56
  )

-- | Run an LLVM operation on a module.
runLLVM :: (LLVM.TargetMachine -> LLVM.Module -> IO ()) -> AST.Module -> IO ()
runLLVM f ast =
    LLVM.withHostTargetMachine $ \tgt ->
    LLVM.withContext $ \ctx ->
    LLVM.withModuleFromAST ctx ast $ \m -> try (LLVM.verify m) >>= \case
      Right () -> do
        void . LLVM.withPassManager passes $ \pm -> LLVM.runPassManager pm m
        f tgt m
      Left (LLVM.VerifyException err) -> do
        putStrLn "LLVM verification errors:"
        putStr err
  where
    passes = LLVM.defaultPassSetSpec
      { LLVM.transforms =
        [ LLVM.PromoteMemoryToRegister
        , LLVM.GlobalValueNumbering True
        , LLVM.InstructionCombining
        , LLVM.DeadStoreElimination
        , LLVM.SimplifyControlFlowGraph
        ]
      }

-- | The name of the brainfuck \"main\" function in the LLVM IR.
bfmain :: IsString s => s
bfmain = fromString "bfmain"

-- | Name of the memory array parameter.
memname :: AST.Name
memname = AST.mkName "mem"

-- | Name of the data index parameter.
diname :: AST.Name
diname  = AST.mkName "di"

-- | The C putchar stdlib function.
putchar :: AST.Name
putchar = AST.mkName "putchar"

-- | The C getchar stdlib function.
getchar :: AST.Name
getchar = AST.mkName "getchar"

-- | The size of the heap
memSize :: Int
memSize = 40000

-- | The initial data pointer
initialdp :: Int
initialdp = 10000

-- | Keep track of whether a cached memory value is \"clean\"
-- (unchanged since it was loaded) or \"dirty\" (changed and must be
-- stored again).
data Tagged = Clean { tname :: !AST.Name } | Dirty { tname :: !AST.Name }

-- | An external binding
extern :: AST.Name -> [AST.Type] -> AST.Type -> AST.Definition
extern name ptys rty = AST.GlobalDefinition AST.functionDefaults
  { AST.name        = name
  , AST.linkage     = AST.External
  , AST.parameters  = ([AST.Parameter ty (AST.mkName "") [] | ty <- ptys], False)
  , AST.returnType  = rty
  }

-- | Get a pointer to a substructure of a larger structure
gep :: AST.Operand -> [AST.Operand] -> AST.Instruction
gep tgt idxs = AST.GetElementPtr True tgt idxs []

-- | Load a value from an address.
load :: AST.Operand -> AST.Instruction
load p = AST.Load False p Nothing 0 []

-- | Store a value to an address.
store :: AST.Operand -> AST.Operand -> AST.Named AST.Instruction
store p val = AST.Do $ AST.Store False p val Nothing 0 []

-- | Integer addition.
add :: AST.Operand -> AST.Operand -> AST.Instruction
add op1 op2 = AST.Add False False op1 op2 []

-- | Integer subtraction.
sub :: AST.Operand -> AST.Operand -> AST.Instruction
sub op1 op2 = AST.Sub False False op1 op2 []

-- | Integer multiplication.
mul :: AST.Operand -> AST.Operand -> AST.Instruction
mul op1 op2 = AST.Mul False False op1 op2 []

-- | Call a function.
call :: AST.Operand -> [AST.Operand] -> AST.Instruction
call fn args = AST.Call Nothing AST.C [] (Right fn) [(a, []) | a <- args] [] []

-- | Definitely not a tail call!
--
-- TODO: Figure out why tail calls make it segfault.
notailcall :: AST.Operand -> [AST.Operand] -> AST.Instruction
notailcall fn args = AST.Call (Just AST.NoTail) AST.C [] (Right fn) [(a, []) | a <- args] [][]

-- | Truncate a larger type to a smaller one.
trunc :: AST.Operand -> AST.Type -> AST.Instruction
trunc op ty = AST.Trunc op ty []

-- | Zero-extend a smaller type to a larger one.
zext :: AST.Operand -> AST.Type -> AST.Instruction
zext op ty = AST.ZExt op ty []

-- | Function type
funty :: [AST.Type] -> AST.Type -> AST.Type
funty args ret = AST.ptr $ AST.FunctionType ret args False

-- | Constant unsigned 8-bit int.
cint8 :: W.Word8 -> AST.Operand
cint8 = AST.ConstantOperand . ASTC.Int 8 . fromIntegral

-- | Constant unsigned 16-bit int.
cint16 :: W.Word16 -> AST.Operand
cint16 = AST.ConstantOperand . ASTC.Int 16 . fromIntegral

-- | End a basic block (instructions are assumed to be in reverse)
block :: AST.Name -> [AST.Named AST.Instruction] -> AST.Terminator -> AST.BasicBlock
block n ops = AST.BasicBlock n (reverse ops) . AST.Do

-- | Error responses
data JITError
  = JITNoSuchFunc
  -- ^ The symbol couldn't be resolved.  This is not necessarily fatal
  -- as, eg, in LostKng.b function "3" gets renamed but all others are
  -- fine.

-- | Plumbing to call the JIT-compiled code.
foreign import ccall "dynamic" haskFun
  :: F.FunPtr (F.Ptr W.Word8 -> W.Word16 -> IO ())
  -> F.Ptr W.Word8 -> W.Word16 -> IO ()

-- | Plumbing to pass putchar to the JIT-compiled code.
foreign import ccall "wrapper" haskFunPut
  :: (W.Word32 -> IO W.Word32)
  -> IO (F.FunPtr (W.Word32 -> IO W.Word32))

-- | Plubming to pass getchar to the JIT-compiled code.
foreign import ccall "wrapper" haskFunGet
  :: IO W.Word32
  -> IO (F.FunPtr (IO W.Word32))
