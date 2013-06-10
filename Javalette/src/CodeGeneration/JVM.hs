--------------------------------------------------------------------------------
-- Compiler Construction 
-- TDA282
-- Niclas Tall

module CodeGeneration.JVM where

import CodeGeneration.AbsJVM
import AbsJavalette

import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.Writer
import Control.Monad.State

import Prelude hiding (EQ, LT, GT)
import qualified Data.Map as M hiding (map, null)

type Code = [Instr]
type CTR = Int
data Env = Env {nextPtr :: CTR,
                heap    :: [M.Map Ident (Int, JType)],
                nextLbl :: CTR,
                crntStk :: CTR,
                maxStk  :: CTR,
                locals  :: CTR,
                code    :: Code,
                file    :: String}
  deriving (Show)

type JVM a = ErrorT String (StateT Env (WriterT Code Identity)) a

genJVM :: String -> Program -> (Either String (), Code)
genJVM file p = 
  ( runIdentity
  . runWriterT
  . flip evalStateT (newEnv file)
  . runErrorT) (gen p)
  
gen :: Program -> JVM ()
gen (Program td) = do
  header 
  mapM_ genCodeDef td

-------------------------------------------------------------------------------
-- Generation of Jasmin code

genCodeDef :: TopDef -> JVM ()
genCodeDef (FnDef t (Ident x) args (Block stms)) = do
  newScope
  mapM_ (\(Arg t x) -> addVar x (jl2jvm t)) args
  
  if null stms -- Catch empty void functions void f() {}
    then putCode $ Return V
    else genCodeStms stms
  env <- get
   
  emit $ Header $ jvmName x t $ foldl (\acc (Arg t _) -> t : acc) [] args
  emit $ Header $ ".limit locals " ++ show (locals env)
  emit $ Header $ ".limit stack "  ++ show (maxStk env)
  emit $ Header "  entry:"
  storeCode
  emit $ Header ".end method\n"
  clearBook

genCodeStms :: [Stmt] -> JVM ()
genCodeStms = mapM_ genCodeStm

genCodeStm :: Stmt -> JVM ()
genCodeStm (Empty)              = return () 
genCodeStm (BStmt (Block stms)) = do
  newScope
  mapM_ genCodeStm stms 
  pop

genCodeStm (Decl t items)       = declare (jl2jvm t) items
  where
  declare :: JType -> [Item] -> JVM ()
  declare t []              = return ()
  declare t (NoInit x:xs) = do 
    ptr <- addVar x t
    initDefault t ptr
    declare t xs
  
  declare t (Init x e:xs) = do 
    genCodeTExpr e
    ptr <- addVar x t
    putCode $ Store t ptr
    incStk (-1)
    declare t xs

genCodeStm (Ass x e)            = do
  genCodeTExpr e
  (ptr, t) <- lookVar x
  putCode $ Store t ptr
  if t == D then incStk (-2) else incStk (-1)
  
genCodeStm (Incr x)             = do 
  (ptr, _) <- lookVar x
  putCode $ IInc ptr $ JInt 1

genCodeStm (Decr x)             = do 
  (ptr, _) <- lookVar x
  putCode $ IInc ptr $ JInt (-1)

genCodeStm (Ret (TExpr t e))    = do 
  let t' = jl2jvm t
  genCodeExpr t' e
  putCode $ Return t'

genCodeStm VRet                 = do 
  putCode $ Return V

genCodeStm (Cond e s)           = do 
  l1 <- newLabel 
  genCodeTExpr e
  putCode $ If EQ l1
  incStk (-1)
  genCodeStm s
  putCode $ Lbl l1
   
genCodeStm (CondElse e s1 s2)   = do 
  l1 <- newLabel
  l2 <- newLabel

  genCodeTExpr e
  putCode $ If EQ l1
  incStk (-1)
  genCodeStm s1 -- If true S1
  
  lc <- lastCode
 
  if isReturn lc -- If last intruction of s1 is a return, noneed for goto
    then do putCode $ Lbl l1; genCodeStm s2
    else do
          mapM_ putCode [Goto l2, Lbl l1]
          genCodeStm s2 -- If e is false
          putCode $ Lbl l2

genCodeStm (While e s)          = do 
  l1 <- newLabel
  l2 <- newLabel

  putCode $ Lbl l1                    -- Label for the test
  genCodeTExpr e                      -- code for the test
  putCode $ If EQ l2                  -- IF e == 0, goto l2 
  incStk (-1)
  genCodeStm s
  mapM_ putCode [Goto l1, Lbl l2]

genCodeStm (SExp e)             = do 
  genCodeTExpr e

-------------------------------------------------------------------------------
-- Genereate JVM code from expression

genCodeTExpr :: Expr -> JVM ()
genCodeTExpr (TExpr t e) = genCodeExpr (jl2jvm t) e
genCodeTExpr e           = throwError $ "genCodeTExpr " ++ show e

genCodeExpr :: JType -> Expr -> JVM ()
genCodeExpr t (EVar x)        = do 
  (ptr,t) <- lookVar x
  putCode $ Load t ptr 
  case t of
    D -> incStk 2
    _ -> incStk 1 

genCodeExpr t (ELitInt i)     = do putCode $ Push $ JInt  i; incStk 1
genCodeExpr t (ELitDoub d)    = do putCode $ Push $ JDoub d; incStk 2
genCodeExpr t (ELitTrue)      = do putCode $ Push $ JInt  1; incStk 1
genCodeExpr t (ELitFalse)     = do putCode $ Push $ JInt  0; incStk 1
genCodeExpr (JFun t targs) (EApp (Ident x) es) = do 
  f <- fileName 
  mapM_ genCodeTExpr es  
  case isBuiltIn x of 
    Just f  -> putCode $ Invoke "Runtime" f t targs
    Nothing -> putCode $ Invoke f x t targs
  case t of 
    D -> do incStk 2; incStk $ (-2) * length targs
    V -> incStk 0
    _ -> do incStk 1; incStk $ (-1) * length targs

genCodeExpr t (EString s)     = do putCode $ Push $ JString s; incStk 1

genCodeExpr t (Neg (TExpr Int  (ELitInt  i))) = genCodeExpr I $ ELitInt  $ i * (-1)
genCodeExpr t (Neg (TExpr Doub (ELitDoub d))) = genCodeExpr D $ ELitDoub $ d * (-1)
genCodeExpr t (Neg e)         = do
  genCodeTExpr e;
  case t of
    I -> do putCode $ Push $ JInt  (-1); incStk 1
    D -> do putCode $ Push $ JDoub (-1); incStk 2

  putCode $ Mult t
  if t == D then incStk (-2) else incStk (-1)

genCodeExpr t (Not (TExpr Bool ELitTrue))  = genCodeExpr I $ ELitInt 0
genCodeExpr t (Not (TExpr Bool ELitFalse)) = genCodeExpr I $ ELitInt 1
genCodeExpr t (Not e)         = do
  genCodeTExpr e;
  exit <- newLabel
  jump <- newLabel
  mapM_ putCode [If EQ jump, Push (JInt 0), Goto exit, 
                 Lbl jump, Push (JInt 1), Lbl exit] 
  mapM_ incStk [-1, 1, 1]

genCodeExpr t (EMul e1 op e2) = do
  genCodeTExpr e1
  genCodeTExpr e2
  genCodeMulOp t op
  incStk (-1) 

genCodeExpr t (EAdd e1 op e2) = do
  genCodeTExpr e1
  genCodeTExpr e2
  genCodeAddOp t op
  incStk (-1)

genCodeExpr t (ERel e1@(TExpr te1 _) op e2) = do
  l <- newLabel
  putCode $ Push (JInt 1)
  incStk 1
  genCodeTExpr e1
  genCodeTExpr e2

  if jl2jvm te1 == D
    then do mapM_ putCode [DCmp (negRel $ relOp2rel op), 
                          If (relOp2rel op) l, -- Jump if true, then its false
                          Pop, Push (JInt 0), Lbl l] 
            mapM_ incStk [-1, -1, -1, 1]

    else do mapM_ putCode [IfCmp (relOp2rel op) l, Pop, Push (JInt 0), Lbl l]
            mapM_ incStk [-2, -1, 1]

genCodeExpr t (EAnd e1 e2)    = do
  l <- newLabel
  genCodeTExpr e1
  mapM_ putCode [Dup, If EQ l, Pop]
  mapM_ incStk [1, -1, -1]
  genCodeTExpr e2               -- e1 is true, test e2
  putCode $ Lbl l  

genCodeExpr t (EOr e1 e2)     = do
  l <- newLabel
  genCodeTExpr e1
  mapM_ putCode [Dup, If NEQ l, Pop]
  mapM_ incStk [1, -1, -1]
  genCodeTExpr e2
  putCode $ Lbl l

genCodeExpr t (TExpr t' e)    = genCodeExpr (jl2jvm t') e 

genCodeMulOp :: JType -> MulOp -> JVM ()
genCodeMulOp t op | op == Times = putCode $ Mult t
                  | op == Div   = putCode $ Divi t
                  | op == Mod   = putCode Modu

genCodeAddOp :: JType -> AddOp -> JVM ()
genCodeAddOp t op | op == Plus  = putCode $ Addi t
                  | op == Minus = putCode $ Subs t

-------------------------------------------------------------------------------
-- Enivornment Functions

newEnv :: String -> Env
newEnv = Env 0 [M.empty] 0 0 0 0 [] 

-- This is just to support scope in javalette
newScope :: JVM ()
newScope = modify $ \e@Env{heap=heap} -> e{heap = M.empty : heap}

pop :: JVM ()
pop = modify $ \e@Env{heap=(h:hs)} -> e{heap = hs}

clearBook :: JVM ()
clearBook = modify $ \e@Env{file=f} -> newEnv f

addVar :: Ident -> JType -> JVM CTR
addVar x t = do 
  env@Env{nextPtr = ptr, heap = heap, locals = l} <- get
  let heap' = addVar' x ptr t heap
   
  let l' = if t == D then l + 2   else l + 1
  let p' = if t == D then ptr + 2 else ptr + 1
  put env{nextPtr = p', heap = heap', locals = l'}  
  return ptr

  where
  addVar' :: Ident -> CTR -> JType -> [M.Map Ident (CTR, JType)] -> [M.Map Ident (CTR, JType)]
  addVar' x ptr t []     = []   
  addVar' x ptr t (h:hs) = 
    case M.lookup x h of
     Nothing -> M.insert x (ptr, t) h : hs 
     Just _  -> error "Bail" -- throwError $ "Variable " ++ show x ++ " already declered"

lookVar :: Ident -> JVM (CTR, JType)
lookVar x = do
  Env{heap = heap} <- get
  let res = lookVar' x heap
  case res of
    Nothing -> throwError $ "Variable " ++ show x ++ " not found"
    Just r  -> return r

  where
  lookVar' x []     = Nothing 
  lookVar' x (h:hs) = 
    case M.lookup x h of
      Nothing -> lookVar' x hs
      Just v  -> Just v

-- Gets the current label and increments it   
newLabel :: JVM Label
newLabel = do
  env <- get
  let l = nextLbl env
  put $ env {nextLbl = l + 1}
  return $ 'L' : show l
 
incStk :: Int -> JVM ()
incStk i | i == 0    = return ()
         | otherwise = modify $ \e@Env{crntStk = c, maxStk = m} 
                                  -> e{crntStk = c + i, maxStk = max (c+i) m}

initDefault :: JType -> CTR -> JVM ()
initDefault t ptr = do
  case t of
    I -> putCode (Push (JInt 0))
    D -> putCode (Push (JDoub 0))
  putCode $ Store t ptr
  
fileName :: JVM String
fileName = do
  Env{file = f} <- get
  return f

-------------------------------------------------------------------------------
-- Code related

putCode :: Instr -> JVM ()
putCode inst = modify $ \e@Env{code = c} -> e{code = c ++ [inst]}

lastCode :: JVM Instr
lastCode = do
  Env{code = cs} <- get
  return $ last cs

storeCode :: JVM ()
storeCode = do 
  e@Env{code = cs} <- get
  mapM_ emit cs
  put $ e{code = []}

emit :: Instr -> JVM ()
emit c = tell [c]

-------------------------------------------------------------------------------
-- Helper function

jl2jvm :: Type -> JType
jl2jvm Int           = I
jl2jvm Doub          = D
jl2jvm Bool          = I
jl2jvm Void          = V
jl2jvm Str           = S
jl2jvm (Fun t targs) = JFun (jl2jvm t) $ foldr 
                                          (\t acc -> jl2jvm t : acc) [] targs 

b2int :: Bool -> Int
b2int True = 1
b2int False= 0

typeList :: [Type] -> String
typeList ts | null ts = f ts
            | True    = (tail . f) ts 
  where f = concatMap (("," ++ ) . fstUpper . show' . jl2jvm)

relOp2rel :: RelOp -> Rel 
relOp2rel LTH = LT
relOp2rel LE  = LEQ
relOp2rel GTH = GT
relOp2rel GE  = GEQ
relOp2rel EQU = EQ
relOp2rel NE  = NEQ

negRel :: Rel -> Rel
negRel LT  = GEQ 
negRel LEQ = GT
negRel GT  = LEQ
negRel GEQ = LT
negRel EQ  = NEQ
negRel NEQ = EQ

jvmName :: String -> Type -> [Type] -> String
jvmName n t args = ".method public static " ++ n ++ "(" ++ 
                   concatMap (fstUpper . show . jl2jvm) args ++ 
                   ")" ++ (fstUpper . show') (jl2jvm t)

isReturn :: Instr -> Bool
isReturn (Return _) = True
isReturn _          = False

-------------------------------------------------------------------------------
-- Header construction

header :: JVM ()
header = do
  Env{file=file} <- get
  emit $ Header $ ".class public " ++ file
  emit $ Header ".super java/lang/Object\n"
  emit $ Header ".method public <init>()V"
  emit $ Header "  aload_0"
  emit $ Header "  invokespecial java/lang/Object/<init>()V"
  emit $ Header "  return"
  emit $ Header ".end method\n"
  emit $ Header ".method public static main([Ljava/lang/String;)V ; standard type of main"
  emit $ Header ".limit locals 1"
  emit $ Header $ "  invokestatic " ++ file ++ "/main()I ; calls your main"
  emit $ Header "  pop"
  emit $ Header "  return"
  emit $ Header ".end method\n"


isBuiltIn :: String -> Maybe String
isBuiltIn x = case x of
  f@"printInt"    -> Just f    
  f@"printDouble" -> Just f
  f@"printString" -> Just f
  f@"readInt"     -> Just f
  f@"readDouble"  -> Just f
  otherwise       -> Nothing

