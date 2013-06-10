--------------------------------------------------------------------------------
-- Compiler Construction 
-- TDA282
-- Niclas Tall

module CodeGeneration.LLVM where

import AbsJavalette as J
import CodeGeneration.AbsLLVM as L

import Control.Monad.Identity
import Control.Monad.State

import qualified Data.Map as M hiding (map, null)

type Code = [Instr]
data Env = Env  {
                  nextReg :: Reg 
                , scope   :: [M.Map Ident Ptr] 
                , nextLbl :: Int
                , globals :: [(Value, String)]
                , code    :: Code
                }

type LLVM a = State Env a

genLLVM :: Program -> Code
genLLVM = code . flip execState newEnv . gen

gen :: Program -> LLVM ()
gen (Program td) = do
  declareStdFunctions
  mapM_ genCodeDef td
  genCodeGlobals
  modify $ \e@Env{code = c} -> e{code = reverse c}

--------------------------------------------------------------------------------
-- Generation of LLVM code

genCodeDef :: TopDef -> LLVM ()
genCodeDef (FnDef t x args (Block stms)) = do
  newScope
  mapM_ (\(Arg t x) -> addVar t x) args
  genFunDeclaration (LLVMType t) x args
  putCode $ Label "entry"
  allocArgs args
  if null stms then putCode L.VRet else genCodeStmts stms 
  putCode EndDefinition
  pop

--------------------------------------------------------------------------------
-- Statements

genCodeStmts :: [Stmt] -> LLVM ()
genCodeStmts = mapM_ genCodeStmt

genCodeStmt :: Stmt -> LLVM ()
genCodeStmt Empty              = return ()
genCodeStmt (BStmt (Block ss)) = do
  newScope
  genCodeStmts ss
  pop

genCodeStmt (Decl t items)     = declare t items
  where
  declare :: Type -> [Item] -> LLVM ()
  declare t []    = return ()
  declare t (NoInit x:xs) = do
    ptr <- addVar t x 
    initDefault ptr
    declare t xs
  declare t (Init x e:xs) = do
    r   <- genCodeTExpr e
    ptr@(Ptr _ pr) <- addVar t x 
    putCode $ Alloc (Ref pr) (LLVMType t)
    putCode $ Store (LLVMType t) (Ref r) ptr
    declare t xs   

genCodeStmt (Ass x e)          = do
  reg <- genCodeTExpr e
  p@(Ptr (LLVMPtrType t) _) <- lookVar x
  putCode $ Store (LLVMType t) (Ref reg) p  

genCodeStmt (AAss x dim e)     = error "TODO"
genCodeStmt e@(Incr x)         = genCodeStmtIncDec e
genCodeStmt e@(Decr x)         = genCodeStmtIncDec e
genCodeStmt (J.Ret (TExpr Int  (ELitInt i)))  = putCode $ L.Ret (LLVMType Int)  (Const i)
genCodeStmt (J.Ret (TExpr Doub (ELitDoub i))) = putCode $ L.Ret (LLVMType Doub) (DConst i)
genCodeStmt (J.Ret (TExpr Bool ELitTrue))     = putCode $ L.Ret (LLVMType Bool) (Const 1)
genCodeStmt (J.Ret (TExpr Bool ELitFalse))    = putCode $ L.Ret (LLVMType Bool) (Const 0)
genCodeStmt (J.Ret (TExpr t e))= do
  r <- genCodeExpr (LLVMType t) e
  putCode $ L.Ret (LLVMType t) (Ref r)

genCodeStmt J.VRet             = putCode L.VRet
genCodeStmt (Cond e s)         = do
  re    <- genCodeTExpr e
  true  <- newLabel
  cont  <- newLabel  
  cond  <- newReg
  putCode $ Cmp (Ref cond) EQU (LLVMType Bool) (Ref re) (Const 1)
  putCode $ BrCond (Ref cond) true cont

  putCode $ Label true
  genCodeStmt s
  mapM_ putCode [Br cont, Label cont]

genCodeStmt (CondElse e s1 s2) = do
  re    <- genCodeTExpr e
  true  <- newLabel
  false <- newLabel
  comb  <- newLabel
  cond  <- newReg
  putCode $ Cmp (Ref cond) EQU (LLVMType Bool) (Ref re) (Const 1)
  putCode $ BrCond (Ref cond) true false
  
  putCode $ Label true
  genCodeStmt s1
  trueIsReturning <- liftM isReturn lastCode 
  unless trueIsReturning $ putCode $ Br comb

  putCode $ Label false
  genCodeStmt s2
  
  falseIsReturning <- liftM isReturn lastCode 
  unless falseIsReturning $ mapM_ putCode [Br comb, Label comb]

genCodeStmt (While e s)        = do
  test <- newLabel
  loop <- newLabel
  exit <- newLabel
  cond <- newReg
  putCode $ Br test
  
  putCode $ Label test
  re   <- genCodeTExpr e
  putCode $ Cmp (Ref cond) EQU (LLVMType Bool) (Ref re) (Const 1)
  putCode $ BrCond (Ref cond) loop exit
  
  putCode $ Label loop
  genCodeStmt s
  mapM_ putCode [Br test, Label exit]

genCodeStmt (Fore t x e s)     = error "TODO"
genCodeStmt (SExp e)           = do genCodeTExpr e; return ()

--------------------------------------------------------------------------------
-- Helper functions for statements

genCodeStmtIncDec :: Stmt -> LLVM ()
genCodeStmtIncDec e = do
  let (inc, x) = case e of
            (Incr var) -> (True,  var)
            (Decr var) -> (False, var)
  
  let i  = if inc then 1 else (-1)
  let id = if inc then 1.0 else (-1.0)

  ptr@(Ptr (LLVMPtrType t) _) <- lookVar x
  r                           <- newReg
  putCode $ Load (Ref r) ptr

  r1 <- case t of
          Int  -> genCodeExpr (LLVMType Int)  (ELitInt i)
          Doub -> genCodeExpr (LLVMType Doub) (ELitDoub id)

  result <- newReg
  putCode $ Add (Ref result) (LLVMType t) (Ref r) (Ref r1)
  putCode $ Store (LLVMType t) (Ref result) ptr
  
--------------------------------------------------------------------------------
-- Expressions

genCodeTExpr :: Expr -> LLVM Reg
genCodeTExpr (TExpr t e) = genCodeExpr (LLVMType t) e

genCodeExpr :: LLVMType -> Expr -> LLVM Reg
genCodeExpr t (EVar x)          = do
  ptr <- lookVar x
  r   <- newReg
  putCode $ Load (Ref r) ptr
  return r

genCodeExpr t e@(ELitInt i)     = genCodeCons t e
genCodeExpr t e@(ELitDoub i)    = genCodeCons t e
genCodeExpr t e@ELitTrue        = genCodeCons t e
genCodeExpr t e@ELitFalse       = genCodeCons t e

genCodeExpr t (EApp (Ident x) es)       = do
  rargs <- mapM (\(TExpr t e) -> genCodeExpr (LLVMType t) e) es
  let targs = map (\(TExpr t _) -> if t == Str then LLVMPtrType t else LLVMType t) es
  let args  = zipWith (\t r -> Argu t (Ref r)) targs rargs
  r <- newReg
  putCode $ Call (Ref r) t x args
  return r

genCodeExpr (LLVMType t) (EString s)       = do
  c <- newReg
  r <- newReg
  e@Env{globals = g} <- get
  put e{globals = (Glbl c,s):g}

  putCode $ Bitcast (Ref r) (LLVMType t) (length s + 1) (Glbl c) (LLVMPtrType t)
  return r

genCodeExpr t (EArrLen x)       = error "TODO"
genCodeExpr t (EArrMLen x dim)  = error "TODO"
genCodeExpr t (ENArr x sizes)   = error "TODO"
genCodeExpr t (EIArr x sizes)   = error "TODO"

genCodeExpr t (Neg (TExpr Int (ELitInt i))) = genCodeExpr (LLVMType Int) (ELitInt $ i * (-1))
genCodeExpr t (Neg (TExpr Doub (ELitDoub i))) = 
  genCodeExpr (LLVMType Doub) (ELitDoub $ i * (-1))

genCodeExpr t (Neg e)           = do
  op <- genCodeTExpr e
  r <- newReg
  case t of
    (LLVMType Int)  -> putCode $ Mul (Ref r) t (Ref op) (Const (-1))
    (LLVMType Doub) -> putCode $ Mul (Ref r) t (Ref op) (DConst (-1.0))
  return r

genCodeExpr t (Not (TExpr Bool ELitTrue))  = genCodeExpr (LLVMType Bool) $ ELitInt 0
genCodeExpr t (Not (TExpr Bool ELitFalse)) = genCodeExpr (LLVMType Bool) $ ELitInt 1
genCodeExpr t (Not e)           = do
  r       <- genCodeTExpr e
  cond    <- newReg
  resultR <- newReg
  true    <- newLabel
  false   <- newLabel
  result  <- newLabel

  putCode $ Cmp (Ref cond) EQU t (Ref r) (Const 1)
  putCode $ BrCond (Ref cond) true false  
  mapM_ putCode [Label true, Br result, Label false, Br result, Label result]
  putCode $ Phi (Ref resultR) t [(Const 0, true), (Const 1, false)]
  return resultR

genCodeExpr t (EMul e1 op e2)   = do
  r1 <- genCodeTExpr e1
  r2 <- genCodeTExpr e2
  r  <- newReg
  genCodeMulOp op (Ref r) t (Ref r1) (Ref r2)
  return r

genCodeExpr t (EAdd e1 op e2)   = do
  r1 <- genCodeTExpr e1
  r2 <- genCodeTExpr e2
  r  <- newReg
  genCodeAddOp op (Ref r) t (Ref r1) (Ref r2)
  return r

genCodeExpr t (ERel e1@(TExpr t' _) op e2)   = do
  r1 <- genCodeTExpr e1  
  r2 <- genCodeTExpr e2
  r  <- newReg
  putCode $ Cmp (Ref r) op (LLVMType t') (Ref r1) (Ref r2)  
  return r

genCodeExpr t e@(EAnd e1 e2)    = genCodeAndOr t e
genCodeExpr t e@(EOr e1 e2)     = genCodeAndOr t e
genCodeExpr _ (TExpr t e)       = genCodeExpr (LLVMType t) e

--------------------------------------------------------------------------------
-- Helper functions for expressions

genCodeCons :: LLVMType -> Expr -> LLVM Reg
genCodeCons t@(LLVMType t') e = do
  p <- newReg
  r <- newReg
  putCode $ Alloc (Ref p) t
  putCode $ Store t (value e) (Ptr (LLVMPtrType t') p)
  putCode $ Load (Ref r) (Ptr (LLVMPtrType t') p)
  return r

  where
  value :: Expr -> Value
  value (ELitInt i)   = Const i
  value (ELitDoub i)  = DConst i
  value (ELitTrue)    = Const 1
  value (ELitFalse)   = Const 0

genCodeMulOp :: MulOp -> Value -> LLVMType -> Value -> Value -> LLVM () 
genCodeMulOp J.Times r t v1 v2 = putCode (Mul r t v1 v2) 
genCodeMulOp J.Div   r t v1 v2 = putCode (L.Div r t v1 v2)
genCodeMulOp J.Mod   r t v1 v2 = putCode (Rem r t v1 v2) 

genCodeAddOp :: AddOp -> Value -> LLVMType -> Value -> Value -> LLVM ()
genCodeAddOp Plus  r t v1 v2 = putCode (Add r t v1 v2)
genCodeAddOp Minus r t v1 v2 = putCode (Sub r t v1 v2)

genCodeAndOr :: LLVMType -> Expr -> LLVM Reg
genCodeAndOr t e = do
  r1     <- genCodeTExpr $ e1 e
  e1T    <- newLabel
  e1F    <- newLabel
  e2T    <- newLabel
  e2F    <- newLabel
  ass    <- newLabel
  result <- newReg
  testR1 <- newReg
  testR2 <- newReg 
  putCode $ Cmp (Ref testR1) EQU t (Ref r1) (false e) 
  putCode $ BrCond (Ref testR1) e1T e1F

  mapM_ putCode [Label e1T, Br ass, Label e1F]
  r2     <- genCodeTExpr $ e2 e
  putCode $ Cmp (Ref testR2) EQU t (Ref r2) (false e)
  putCode $ BrCond (Ref testR2) e2T e2F
  
  mapM_ putCode [Label e2T, Br ass, Label e2F, Br ass, Label ass]
  putCode $ Phi (Ref result) t [(false e, e1T), (false e, e2T), (true e, e2F)]
  return result
  
  where
  e1 (EAnd a _)   = a
  e1 (EOr  a _)   = a
  e2 (EAnd _ b)   = b
  e2 (EOr _ b)    = b
  true (EAnd _ _) = Const 1
  true (EOr _ _)  = Const 0
  false (EAnd _ _)= Const 0
  false (EOr _ _) = Const 1
  
--------------------------------------------------------------------------------
-- Environment

newEnv :: Env
newEnv = Env 0 [] 0 [] []

newScope :: LLVM ()
newScope = modify $ \e@Env{scope = s} -> e{scope = M.empty : s}

pop :: LLVM ()
pop = modify $ \e@Env{scope = (s:ss)} -> e{scope = ss}

addVar :: Type -> Ident -> LLVM Ptr
addVar t x = do
  e@Env{nextReg = nreg, scope = (s:ss)} <- get
  let p = Ptr (LLVMPtrType t) nreg
  let s' = M.insert x p s
  put e{nextReg = nreg + 1, scope = s':ss}
  return p

lookVar :: Ident -> LLVM Ptr
lookVar x = do
  e@Env{scope = s} <- get
  case lookVar' x s of
    Nothing -> error $ "lookVar: variable " ++ show x ++ " not declared"
    Just n  -> return n
 
  where
  lookVar' :: Ident -> [M.Map Ident Ptr] -> Maybe Ptr
  lookVar' x []     = Nothing
  lookVar' x (s:ss) = case M.lookup x s of
                        Nothing -> lookVar' x ss
                        Just n  -> Just n 

initDefault :: Ptr -> LLVM ()
initDefault p@(Ptr t@(LLVMPtrType Int)  r) = 
  mapM_ putCode [Alloc (Ref r) (LLVMType Int), Store (LLVMType Int) (Const 0) p]
initDefault p@(Ptr t@(LLVMPtrType Doub) r) = 
  mapM_ putCode [Alloc (Ref r) (LLVMType Doub), Store (LLVMType Doub) (DConst 0.0) p]
initDefault _               = error "initDefault: Shouldnt reach here"

newReg :: LLVM Reg
newReg = do
  e@Env{nextReg = r} <- get
  put e{nextReg = r+1}
  return r

newLabel :: LLVM Lbl
newLabel = do
  e@Env{nextLbl = l} <- get
  put e{nextLbl = l + 1} 
  return $ 'L' : show l

--------------------------------------------------------------------------------
-- Code

putCode :: Instr -> LLVM ()
putCode s = modify $ \e@Env{code = c} -> e{code = s:c}

putCodeFirst :: Instr -> LLVM ()
putCodeFirst s = modify $ \e@Env{code = c} -> e{code = c ++ [s]}

lastCode :: LLVM Instr
lastCode = do
  e@Env{code = c:cs} <- get
  return c 

isReturn :: Instr -> Bool
isReturn (L.VRet)     = True
isReturn (L.Ret _ _)  = True
isReturn _            = False
--------------------------------------------------------------------------------
-- Helper functions

genCodeGlobals :: LLVM ()
genCodeGlobals = do
  e@Env{globals = g} <- get
  mapM_ (\(r,s) -> putCodeFirst (Global r (length s + 1) (LLVMType Str) (StrConst s))) g

genFunDeclaration :: LLVMType -> Ident -> [Arg] -> LLVM ()
genFunDeclaration t (Ident x) args = do
   sargs <- mapM (\(Arg _ x) -> do (Ptr (LLVMPtrType t) r) <- lookVar x
                                   return $ Argu (LLVMType t) (Ref r)) args
   putCode $ Define x t sargs

allocArgs :: [Arg] -> LLVM ()
allocArgs args = do
  ptrArgs <- mapM (\(Arg _ x) -> lookVar x) args
  newPtrs <- mapM (\(Arg t x) -> addVar t x) args -- overwrite the reference
  let on = zip ptrArgs newPtrs 

  mapM_ (\(o@(Ptr (LLVMPtrType ot) or), n@(Ptr nt nr)) -> 
            do putCode $ Alloc (Ref nr) (LLVMType ot) 
               putCode $ Store (LLVMType ot) (Ref or) n) on
                                                
declareStdFunctions :: LLVM ()
declareStdFunctions = do
  putCode $ Declare "printInt"    (LLVMType Void) [LLVMType Int]
  putCode $ Declare "printDouble" (LLVMType Void) [LLVMType Doub]
  putCode $ Declare "printString" (LLVMType Void) [LLVMPtrType Str]
  putCode $ Declare "readInt"     (LLVMType Int)  []
  putCode $ Declare "readDouble"  (LLVMType Doub) []
