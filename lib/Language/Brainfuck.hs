{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | The Quickie Brainfuck parser and compiler.
module Language.Brainfuck where

import           Control.Arrow (first)
import           Data.Bits ((.|.), (.&.), unsafeShiftL, unsafeShiftR)
import qualified Data.ByteString.Char8 as BS
import           Data.Char (chr, ord)
import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Unboxed.Mutable as VM
import qualified Data.Word as W
import           Control.Exception (try)
import           Control.Monad (void, when)
import           Foreign.Ptr (FunPtr, castFunPtr)
import qualified LLVM.Analysis as LLVM
import qualified LLVM.AST as AST hiding (type')
import qualified LLVM.AST.AddrSpace as AST
import qualified LLVM.AST.CallingConvention as AST
import qualified LLVM.AST.Constant as ASTC
import qualified LLVM.AST.Global as AST
import qualified LLVM.AST.IntegerPredicate as AST
import qualified LLVM.AST.Linkage as AST
import qualified LLVM.AST.Type as AST
import qualified LLVM.Context as LLVM
import qualified LLVM.ExecutionEngine as LLVM
import qualified LLVM.Exception as LLVM
import qualified LLVM.Module as LLVM
import qualified LLVM.PassManager as LLVM
import qualified LLVM.Target as LLVM
import qualified LLVM.Transforms as LLVM
import           System.IO (IOMode(..), hPutStrLn, openFile, stdout)
import           Text.Printf (printf)

-------------------------------------------------------------------------------
-- * Quickie IR

-- | Instructions are 32-bit words, from least to most significant
-- bits:
--
-- * 4 bit opcode
-- * 16 bit unsigned data pointer offset
-- * 8 bit operand
-- * 4 bits unused
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
pattern GoR w <- (unpack -> (0, w, _)) where GoR w = pack 0 w 0

-- | Move the data pointer to the \"left\" (beginning) of the memory
-- array.
--
-- The operand is how far to move by.
pattern GoL :: W.Word16 -> Instruction
pattern GoL w <- (unpack -> (1, w, _)) where GoL w = pack 1 w 0

-- | Increment (with wrapping) the value under the data pointer.
--
-- The operand is how much to increment by.
pattern Inc :: W.Word8 -> Instruction
pattern Inc w <- (unpack -> (2, _, w)) where Inc w = pack 2 0 w

-- | Decrement (with wrapping) the value under the data pointer.
--
-- The operand is how much to decrement by.
pattern Dec :: W.Word8 -> Instruction
pattern Dec w <- (unpack -> (3, _, w)) where Dec w = pack 3 0 w

-- | Set the value under the data pointer to a constant.
--
-- The operand is the value to set.
pattern Set :: W.Word8 -> Instruction
pattern Set w <- (unpack -> (4, _, w)) where Set w = pack 4 0 w

-- | Add the value of the current cell to another (given by dp offset
-- to the right) with a multiplier.
pattern CMulR :: W.Word16 -> W.Word8 -> Instruction
pattern CMulR a w <- (unpack -> (10, a, w)) where CMulR a w = pack 10 a w

-- | Add the value of the current cell to another (given by dp offset
-- to the left) with a multiplier.
pattern CMulL :: W.Word16 -> W.Word8 -> Instruction
pattern CMulL a w <- (unpack -> (11, a, w)) where CMulL a w = pack 11 a w

-- | Jump if the value under the data pointer is zero.
--
-- The operand is the address to jump to.
pattern JZ :: W.Word16 -> Instruction
pattern JZ a <- (unpack -> (5, a, _)) where JZ a = pack 5 a 0

-- | Jump if the value under the data pointer is nonzero.
--
-- The operand is the address to jump to.
pattern JNZ :: W.Word16 -> Instruction
pattern JNZ a <- (unpack -> (6, a, _)) where JNZ a = pack 6 a 0

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

      -- mem[dp+a] = mem[dp+a] + mem[dp] * i
      CMulR a w -> do
        let dp' = dp + fromIntegral a
        x <- VM.unsafeRead mem dp
        VM.unsafeModify mem (\y -> y + x * w) (if dp' >= memSize then memSize-1 else dp')
        go (ip+1) dp

      -- mem[dp-a] = mem[dp-a] + mem[dp] * i
      CMulL a w -> do
        let dp' = dp - fromIntegral a
        x <- VM.unsafeRead mem dp
        VM.unsafeModify mem (\y -> y + x * w) (if dp' < 0 then 0 else dp')
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
      instr -> error ("invalid opcode: " ++ show (instr .&. 255))

-- | JIT compile and execute an LLVM IR program.
jit :: AST.Module -> IO ()
jit =
    runLLVM True $ \_ ctx m ->
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
        CMulR a w -> prn ("CMulR @" ++ show a ++ " " ++ show w) >> pure lvl
        CMulL a w -> prn ("CMulL @" ++ show a ++ " " ++ show w) >> pure lvl
        JZ  a -> prn ("JZ  @" ++ show a) >> pure (lvl + 1)
        JNZ a -> prn ("JNZ @" ++ show a) >> pure (lvl - 1)
        PutCh -> prn "PutCh" >> pure lvl
        GetCh -> prn "GetCh" >> pure lvl
        Hlt   -> prn "Hlt" >> pure lvl
        _     -> error ("invalid opcode: " ++ show (instr .&. 255))

-- | Dump the LLVM IR to stdout or a file.
dumpllvm :: Maybe String -> AST.Module -> IO ()
dumpllvm (Just fname) = runLLVM True $ \_ _ m -> LLVM.writeLLVMAssemblyToFile (LLVM.File fname) m
dumpllvm Nothing      = runLLVM True $ \_ _ m -> LLVM.moduleLLVMAssembly m >>= BS.putStrLn

-- | Dump the LLVM-compiled assembly to stdout or a file.
dumpasm :: Maybe String -> AST.Module -> IO ()
dumpasm (Just fname) = runLLVM True $ \tgt _ m -> LLVM.writeTargetAssemblyToFile tgt (LLVM.File fname) m
dumpasm Nothing      = runLLVM True $ \tgt _ m -> LLVM.moduleTargetAssembly tgt m >>= BS.putStrLn

-- | Dump the LLVM-compiled object code to a file.
objcompile :: String -> AST.Module -> IO ()
objcompile fname = runLLVM True $ \tgt _ m -> LLVM.writeObjectToFile tgt (LLVM.File fname) m

-- | Run the LLVM verifier and print out the messages.
verifyllvm :: AST.Module -> IO ()
verifyllvm = runLLVM False $ \_ _ m -> try (LLVM.verify m) >>= \case
  Right () -> putStrLn "OK!"
  Left (LLVM.VerifyException err) -> putStr err


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
  go vcode ip sz stk cs | sz < 2 = do
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

      -- see if a loop body corresponds to a known pattern
      loop l0 = case l0 of
        -- "[-]" and "[+]" zero the cell
        ('-':']':rest) -> pushi' (Set 0) rest
        ('+':']':rest) -> pushi' (Set 0) rest
        -- "[-{>m}{+n}{<m}]" zeroes the cell and adds n * its value to
        -- the cell m to the right
        ('-':'>':rest) -> case first length (span (=='>') rest) of
          (m1, '+':rest') -> case first length (span (=='+') rest') of
            (n, '<':rest'') -> case first length (span (=='<') rest'') of
              (m2, ']':rest''') | m1 == m2 -> do
                VM.unsafeWrite vcode ip (CMulR (1 + fromIntegral m1) (1 + fromIntegral n))
                VM.unsafeWrite vcode (ip+1) (Set 0)
                go vcode (ip+2) (sz-2) stk rest'''
              _ -> defloop l0
            _ -> defloop l0
          _ -> defloop l0
        -- "[-{<m}{+n}{>m}]" zeroes the cell and adds n * its value to
        -- the cell m to the left
        ('-':'<':rest) -> case first length (span (=='<') rest) of
          (m1, '+':rest') -> case first length (span (=='+') rest') of
            (n, '>':rest'') -> case first length (span (=='>') rest'') of
              (m2, ']':rest''') | m1 == m2 -> do
                VM.unsafeWrite vcode ip (CMulL (1 + fromIntegral m1) (1 + fromIntegral n))
                VM.unsafeWrite vcode (ip+1) (Set 0)
                go vcode (ip+2) (sz-2) stk rest'''
              _ -> defloop l0
            _ -> defloop l0
          _ -> defloop l0
        _ -> defloop l0

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

-- | Compile a Quickie IR program to LLVM IR.
llcompile :: IR -> AST.Module
llcompile code = AST.defaultModule
    { AST.moduleDefinitions =
      [ -- the main function (name must match what the JIT calls)
        AST.GlobalDefinition AST.functionDefaults
        { AST.name        = bfmain
        , AST.parameters  = ([], False)
        , AST.returnType  = AST.void
        , AST.basicBlocks = blocks
        }

        -- the memory array, zero initialised
      , AST.GlobalDefinition AST.globalVariableDefaults
        { AST.name        = AST.mkName "mem"
        , AST.linkage     = AST.Internal
        , AST.isConstant  = False
        , AST.initializer = Just (ASTC.Array AST.i8 (replicate memSize (ASTC.Int 8 0)))
        , AST.type'       = AST.ArrayType (fromIntegral memSize) AST.i8
        }

        -- library functions
      , extern getchar []        AST.i32
      , extern putchar [AST.i32] AST.i32
      ]
    }
  where
    -- an LLVM function consists of a sequence of "basic blocks",
    -- where a basic block is a sequence of instructions followed by a
    -- single terminator.  jumping to or from the middle of a basic
    -- block is not possible.
    blocks =
      let dp0 = AST.mkName "dp0"
          -- we're going to construct the sequence of instructions of
          -- a basic block in reverse, as prepending to a list is
          -- efficient; but then the list must be reversed when a
          -- block is completed
          --
          -- LLVM does mutable state by pointers; local variables are
          -- immutable.  so we're going to store the data pointer
          -- behind a pointer (so a value of type **i8) and load/store
          -- it when necessary; but in the simple case that leads to a
          -- lot of loads and stores as every instruction uses the
          -- cell the data pointer points to.  we can reduce these
          -- loads and stores by keeping around the data pointer in an
          -- immutable variable, creating a fresh variable every time
          -- we do a 'GoL' or 'GoR'; then we just load it once at the
          -- start of a basic block and store it once (if it changed
          -- at all!) at the end.  this saves about 3000 loads/stores
          -- in the mandelbrot program, so it's a good optimisation to
          -- do.
          initialise =
            [ store dp (refm16 dp0)
            , AST.mkName "dp0" .= add (cint16 0) (cint16 (fromIntegral initialdp))
            , AST.mkName "dp"  .= AST.Alloca AST.i16 Nothing 0 []
            ]

          -- as long as the IR is well formed, the final block will
          -- end with a ret and there will be no leftover instructions
          (_, _, _, bs) = V.ifoldl' gen (AST.mkName "entry", initialise, Clean dp0, []) code
      in reverse bs

    -- generate code, the arguments are: 'n', the name of the current
    -- basic block; 'ops', the (reverse order) list of instructions in
    -- the current basic block; 'dpT', the name of the immutable
    -- variable currently holding the data pointer; 'bs', the (reverse
    -- order) list of previous blocks (with the instructions of each
    -- in the correct order).

    -- %dpT' = add %dpT, w
    gen (n, ops, dpT, bs) ip (GoR w) =
      let final = AST.mkName (show ip ++ ".F")
          op = final .= add (refm16 (tname dpT)) (cint16 w)
      in (n, op:ops, Dirty final, bs)

    -- %dpT' = sub %dpT, w
    gen (n, ops, dpT, bs) ip (GoL w) =
      let final = AST.mkName (show ip ++ ".F")
          op = final .= sub (refm16 (tname dpT)) (cint16 w)
      in (n, op:ops, Dirty final, bs)

    -- %tmpP = gep mem [0, %dpT]
    -- %tmp1 = load %tmpP
    -- %tmp2 = add %tmp1, w
    -- store %tmpP, %tmp2
    gen (n, ops, dpT, bs) ip (Inc w) = incdec n ops dpT bs ip w add

    -- %tmpP = gep mem [0, %dpT]
    -- %tmp1 = load %tmpP
    -- %tmp2 = sub %tmp1, w
    -- store %tmpP, %tmp2
    gen (n, ops, dpT, bs) ip (Dec w) = incdec n ops dpT bs ip w sub

    -- %tmpP = gep mem [0, %dpT]
    -- %tmp1 = load %tmpP
    -- %tmp2 = mul %tmp1, w
    -- %tmp3 = add %gpT, a
    -- %tmp4 = gep mem [0, %tmp3]
    -- %tmp5 = load %tmp4
    -- %tmp6 = add %tmp5, %tmp2
    -- store %tmp4, %tmp6
    gen (n, ops, dpT, bs) ip (CMulR a w) = cmul n ops dpT bs ip a w add

    -- %tmpP = gep mem [0, %dpT]
    -- %tmp1 = load %tmpP
    -- %tmp2 = mul %tmp1, w
    -- %tmp3 = add %gpT, a
    -- %tmp4 = gep mem [0, %tmp3]
    -- %tmp5 = load %tmp4
    -- %tmp6 = add %tmp5, %tmp2
    -- store %tmp4, %tmp6
    gen (n, ops, dpT, bs) ip (CMulL a w) = cmul n ops dpT bs ip a w sub

    -- %tmpP = gep mem [0, %dpT]
    -- store %tmpP, w
    gen (n, ops, dpT, bs) ip (Set w) =
      let tmpP = AST.mkName (show ip ++ ".P")
          ops' =
            [ store (refp tmpP) (cint8 w)
            , tmpP .= gep mem [cint8 0, refm16 (tname dpT)]
            ] ++ ops
      in (n, ops', dpT, bs)

    -- %tmpP = gep mem [0, %dpT]
    -- %tmp1 = load %tmpP
    -- %tmp2 = icmp eq 0, %tmp1
    -- cbr %tmp2, TRUE, FALSE
    gen (n, ops, dpT, bs) ip (JZ a) = jmp n ops dpT bs ip (show a) (show ip)

    -- %tmpP = gep mem [0, %dpT]
    -- %tmp1 = load %tmpP
    -- %tmp2 = icmp eq 0, %tmp1
    -- cbr %tmp2, FALSE, TRUE
    gen (n, ops, dpT, bs) ip (JNZ a) = jmp n ops dpT bs ip (show ip) (show a)

    -- %tmpP = gep mem [0, %dpT]
    -- %tmp1 = load %tmpP
    -- call "putchar" %tmp1
    gen (n, ops, dpT, bs) ip PutCh =
      let tmpP = AST.mkName (show ip ++ ".P")
          tmp1 = AST.mkName (show ip ++ ".T1")
          ops' =
            [ AST.Do (call (gname AST.i32 putchar) [refm tmp1])
            , tmp1 .= load (refp tmpP)
            , tmpP .= gep mem [cint8 0, refm16 (tname dpT)]
            ] ++ ops
      in (n, ops', dpT, bs)

    -- %tmpP = gep mem [0, %dpT]
    -- %tmp1 = call "getchar"
    -- store %tmpP, %tmp1
    gen (n, ops, dpT, bs) ip GetCh =
      let tmpP = AST.mkName (show ip ++ ".P")
          tmp1 = AST.mkName (show ip ++ ".T1")
          ops' =
            [ store (refp tmpP) (refm tmp1)
            , tmp1 .= call (gname AST.i32 getchar) []
            , tmpP .= gep mem [cint8 0, refm16 (tname dpT)]
            ] ++ ops
      in (n, ops', dpT, bs)

    -- ret
    gen (n, ops, dpT, bs) ip Hlt =
      let b = block n ops (AST.Ret Nothing [])
      in (AST.mkName (show ip), [], dpT, b : bs)

    -- unreachable if the IR is well-formed
    gen _ _ instr = error ("invalid opcode: " ++ show (instr .&. 255))

    -- reference to an external name
    gname ty = AST.ConstantOperand . ASTC.GlobalReference ty

    -- reference to an i8
    refm = AST.LocalReference AST.i8

    -- reference to an i16
    refm16 = AST.LocalReference AST.i16

    -- reference to a *i8
    refp = AST.LocalReference (ptr AST.i8)

    -- reference to a bool
    refb = AST.LocalReference AST.i1

    -- pointer type
    ptr ty = AST.PointerType ty (AST.AddrSpace 0)

    -- end a block
    block n ops = AST.BasicBlock n (reverse ops) . AST.Do

    -- store the result of an instruction
    (.=) = (AST.:=)

    -- constant ints
    cint8  = AST.ConstantOperand . ASTC.Int 8  . (fromIntegral :: W.Word8  -> Integer)
    cint16 = AST.ConstantOperand . ASTC.Int 16 . (fromIntegral :: W.Word16 -> Integer)

    -- the data pointer
    dp = AST.LocalReference (ptr AST.i16) (AST.mkName "dp")

    -- the global memory
    mem = AST.ConstantOperand $
      ASTC.GlobalReference (AST.ArrayType (fromIntegral memSize) AST.i8) (AST.mkName "mem")

    -- a helper for 'Inc' / 'Dec', as they use the same logic but
    -- differ in the arithmetic instruction used
    incdec n ops dpT bs ip w llop =
      let tmpP = AST.mkName (show ip ++ ".P")
          tmp1 = AST.mkName (show ip ++ ".T1")
          tmp2 = AST.mkName (show ip ++ ".T2")
          ops' =
            [ store (refp tmpP) (refm tmp2)
            , tmp2 .= llop (refm tmp1) (cint8 w)
            , tmp1 .= load (refp tmpP)
            , tmpP .= gep mem [cint8 0, refm16 (tname dpT)]
            ] ++ ops
      in (n, ops', dpT, bs)

    -- a helper for 'CMulR' / 'CMulL', as they use the same logic but
    -- differ in the direction of pointer movement
    cmul n ops dpT bs ip a w llop =
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
            , tmp4 .= gep mem [cint8 0, refm16 tmp3]
            , tmp3 .= llop (refm16 (tname dpT)) (cint16 a)
            , tmp2 .= mul (refm tmp1) (cint8 w)
            , tmp1 .= load (refp tmpP)
            , tmpP .= gep mem [cint8 0, refm16 (tname dpT)]
            ] ++ ops
      in (n, ops', dpT, bs)

    -- a helper for 'JZ' / 'JNZ', as they use the same comparison but
    -- just swap the true and false cases
    jmp n ops dpT bs ip true false =
      let tmpP = AST.mkName (show ip ++ ".P")
          tmp1 = AST.mkName (show ip ++ ".T1")
          tmp2 = AST.mkName (show ip ++ ".T2")
          dp0  = AST.mkName ("dp" ++ show ip)
          storedp = case dpT of
            Clean _ -> []
            Dirty _ -> [store dp (refm16 (tname dpT))]
          term = AST.CondBr (refb tmp2) (AST.mkName true) (AST.mkName false) []
          ops' =
            [ tmp2 .= AST.ICmp AST.EQ (cint8 0) (refm tmp1) []
            , tmp1 .= load (refp tmpP)
            , tmpP .= gep mem [cint8 0, refm16 (tname dpT)]
            ] ++ storedp ++ ops
          b = block n ops' term
      in (AST.mkName (show ip), [dp0 .= load dp], Clean dp0, b : bs)


-------------------------------------------------------------------------------
-- * Internal utilities

-- | Pack an instruction from its components.
--
-- You should not use this directly.
pack :: W.Word32 -> W.Word16 -> W.Word8 -> Instruction
pack op arg1 arg2 = op .|. unsafeShiftL (fromIntegral arg1) 4 .|. unsafeShiftL (fromIntegral arg2) 20

-- | Unpack an instruction which has two operands.
unpack :: Instruction -> (W.Word32, W.Word16, W.Word8)
unpack instr = (instr .&. 15, fromIntegral (unsafeShiftR instr 4 .&. 65535), fromIntegral (unsafeShiftR instr 20 .&. 255))

-- | Run an LLVM operation on a module.
runLLVM :: Bool -> (LLVM.TargetMachine -> LLVM.Context -> LLVM.Module -> IO ()) -> AST.Module -> IO ()
runLLVM optimise f ast =
    LLVM.withHostTargetMachine $ \tgt ->
    LLVM.withContext $ \ctx ->
    LLVM.withModuleFromAST ctx ast $ \m -> do
      when optimise (LLVM.withPassManager passes $ \pm -> void (LLVM.runPassManager pm m))
      f tgt ctx m
  where
    passes = LLVM.defaultPassSetSpec
      { LLVM.transforms =
        [ LLVM.PromoteMemoryToRegister
        , LLVM.GlobalValueNumbering True
        , LLVM.InstructionCombining
        , LLVM.SimplifyControlFlowGraph
        ]
      }

-- | The name of the brainfuck \"main\" function in the LLVM IR.
bfmain :: AST.Name
bfmain = AST.mkName "main"

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
load ptr = AST.Load False ptr Nothing 0 []

-- | Store a value to an address.
store :: AST.Operand -> AST.Operand -> AST.Named AST.Instruction
store ptr val = AST.Do $ AST.Store False ptr val Nothing 0 []

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

-- | Plumbing to call the JIT-compiled code.
foreign import ccall "dynamic" haskFun :: FunPtr (IO ()) -> IO ()
