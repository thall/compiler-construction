--------------------------------------------------------------------------------
-- Compiler Construction 
-- TDA282
-- Niclas Tall

module TypeChecker (runTypeChecker) where

import AbsJavalette
import PrintJavalette
import ErrM
import qualified Data.Map as M
import Prelude hiding (lookup)

import Control.Monad.State
import Control.Monad

type Current      = Ident
type Env          = (Current, Sig, [Scope])
type Sig          = M.Map Ident Type    
type Scope        = M.Map Ident Type
type TypeCheck a  = StateT Env Err a

-------------------------------------------------------------------------------
-- Type Checker

runTypeChecker :: Program -> Err Program
runTypeChecker p = evalStateT (typecheck p) empty 
                                 
typecheck :: Program -> TypeCheck Program
typecheck p@(Program td) = do
  builtinDef
  addTopDefs td
  td' <- checkAllDefs td
  return $ Program td'

  where
  addTopDefs :: [TopDef] -> TypeCheck () 
  addTopDefs []                      = return ()
  addTopDefs ((FnDef t x args _):ds) = do addDef x t (map (\(Arg t _) -> t) args)
                                          addTopDefs ds

checkAllDefs :: [TopDef] -> TypeCheck [TopDef]
checkAllDefs ds = foldM 
  (\acc (FnDef t x args (Block stms)) -> 
    do 
      newScope
      crntDef x
      mapM_ (\(Arg t x) -> addVar x t) args
      stms' <- checkStms stms
      pop

      let isReturning = (not . null) stms' && returns (last stms')
      if t == Void || isReturning
      then return $ acc ++ [(FnDef t x args (Block stms'))]
      else fail $ "Function: " ++ show x ++ " must return "
  ) [] ds

--------------------------------------------------------------------------------
-- Check Statements

checkStms :: [Stmt] -> TypeCheck [Stmt]
checkStms [] = return []
checkStms ds = do
  case last ds of
    (Cond _ _) -> 
      do ok <- okIfBranching ds
         if ok
         then foldM (\acc s -> do s' <- checkStm s; return $ acc ++ [s']) [] ds
         else fail $ "If-branching that doesnt return"
    otherwise  -> foldM (\acc s -> do s' <- checkStm s; return $ acc ++ [s']) [] ds

checkStm :: Stmt -> TypeCheck Stmt
checkStm (Empty)             = return Empty
checkStm (BStmt (Block bs))  = do 
  newScope 
  bs' <- checkStms bs
  pop
  return $ BStmt (Block bs')

checkStm (Decl t is)         = do 
  is' <- addDecl t is
  return $ Decl t is'

checkStm (Ass x e)           = do
  tx <- lookupVar x
  (TExpr te e') <- infer e
  if tx == te then return $ Ass x (TExpr te e')
  else fail $ "Variable " ++ show x ++ " : " ++ show tx ++ 
              " but expression " ++ show e ++ " : " ++ show te

checkStm (AAss x dim e)      = do
  tx <- lookupVar x
  e'@(TExpr te _) <- infer e
  if tx == te then return $ AAss x dim e'
  else fail $ "Variable " ++ show x ++ " : " ++ show tx ++ 
              " but expression " ++ show e ++ " : " ++ show te

checkStm s@(Incr x)          = do
  t <- lookupVar x
  if t == Int then return $ s
  else fail $ "Only variable of type Int can use the suger ++"

checkStm s@(Decr x)          = do
  t <- lookupVar x
  if t == Int then return $ s
  else fail $ "Only variable of type Int can use the suger ++"

checkStm (Ret e)              = do 
  e'@(TExpr t ex ) <- infer e
  checkReturn t
  return $ Ret e'

checkStm (VRet)               = do 
  checkReturn Void
  return VRet

checkStm (Cond e s)           = do 
 case e of
  ELitTrue  -> do s' <- checkStm s; return s' -- One branch, remove if
  ELitFalse -> return $ Empty -- Removes the if statement, dead code
  otherwise -> do 
    e' <- checkCond e
    s' <- checkStm s
    return $ Cond e' s' 
  
checkStm (CondElse e s1 s2)   = do 
  case e of 
    ELitTrue  -> do s1' <- checkStm s1; return $ s1' -- One branch, remove if
    ELitFalse -> do s2' <- checkStm s2; return $ s2' -- One branch, remove if
    otherwise -> do 
      e'  <- checkCond e
      s1' <- checkStm s1
      s2' <- checkStm s2
      return $ CondElse e' s1' s2' 

checkStm (While e s)          = do 
  e' <- checkCond e
  s' <- checkStm s
  return $ While e' s'

checkStm (Fore t x e s)       = do
  newScope
  e' <- checkExp e t 
  addVar x t
  s' <- checkStm s
  pop  
  return $ Fore t x e' s'

checkStm (SExp e)             = do e' <- infer e; return $ SExp e'

---------------------------------------------------------------------------------
-- Helper functions for Statements

returns :: Stmt -> Bool
returns (Cond _ s)          = returns s
returns (CondElse _ s1 s2)  = returns s1 && returns s2
returns (BStmt (Block ss))  = (not . null) ss && returns (last ss)
returns (Ret _)             = True
returns (VRet)              = True
returns _                   = False

okIfBranching :: [Stmt] -> TypeCheck Bool
okIfBranching ds = do
  tdef <- typeCrntDef
  if tdef == Void
  then return True
  else do
    case last ds of
      (Cond ELitTrue s ) -> return True
      (Cond ELitFalse _) -> return False
      _                  -> return False 

checkCond :: Expr -> TypeCheck Expr
checkCond e = do
  e'@(TExpr te _) <- infer e
  if te == Bool then return e'
  else fail $ "Type of expression '" ++ printTree e ++ 
              "' is " ++ show te ++ " expected Bool."

checkExp :: Expr -> Type -> TypeCheck Expr 
checkExp e (Arr t _) = checkExp e t
checkExp e t = do
  e'@(TExpr te _) <- infer e

  if te == t then return e'
  else fail $ "Type of expression '" ++ printTree e ++ 
              "' is " ++ show te ++ " expected " ++ show t

checkReturn :: Type -> TypeCheck () 
checkReturn t = do
  tdef <- typeCrntDef
  if tdef == (ext t) then return ()
  else fail $ "Function expects type " ++ show tdef ++
              " back but returns " ++ show t

ext :: Type -> Type
ext (Fun t _) = t
ext t         = t

---------------------------------------------------------------------------------
-- Infer type of expression
-- Return a internal typed expression TExpr Type Expr 

infer :: Expr -> TypeCheck Expr
infer e@(EVar x)         = do t <- lookupVar x; return $ TExpr t e
infer e@(ELitInt _)      = return $ TExpr Int e
infer e@(ELitDoub _)     = return $ TExpr Doub e
infer e@(ELitTrue)       = return $ TExpr Bool e
infer e@(ELitFalse)      = return $ TExpr Bool e
infer e@(EApp x es)      = do
  td@(Fun t targs) <- lookupDef x
  texp <- mapM infer es
  let tes = foldr (\(TExpr te _) acc -> te : acc) [] texp
  let tes' = map ext tes
  if targs == tes' then return $ TExpr td $ EApp x texp
  else fail $ "Function " ++ show x ++ " expect input arg of type " ++ show targs ++
              " but got " ++ show tes 

infer e@(EString s)      = return $ TExpr Str e
infer e@(EArrLen x)      = return $ TExpr Int e
infer e@(EArrMLen x _)   = return $ TExpr Int e
infer e@(ENArr t is)     = do
  is' <- inferAIndex is
  return $ TExpr t (ENArr t is')

infer e@(EIArr x is)     = do
  is' <- inferAIndex is
  t   <- lookupVar x
  return $ TExpr t (EIArr x is')   

infer (Neg e)           = do 
  (e'@(TExpr t _), _) <- inferArith e e
  return $ TExpr t (Neg e')

infer (Not e)           = do
  (e'@(TExpr t _), _) <- inferBool e e
  return $ TExpr t (Not e')

infer (EMul e1 op e2)   = do 
  (ex1@(TExpr te1 e1'), ex2@(TExpr te2 e2')) <- inferArith e1 e2
  return $ TExpr te1 $ EMul ex1 op ex2

infer (EAdd e1 op e2)   = do
  (ex1@(TExpr te1 e1'), ex2@(TExpr te2 e2')) <- inferArith e1 e2
  return $ TExpr te1 $ EAdd ex1 op ex2

infer (ERel e1 op e2)   = do
  ex1@(TExpr te1 e1') <- infer e1
  ex2@(TExpr te2 e2') <- infer e2
  if te1 == te2 && (te1 == Int || te1 == Doub || te1 == Bool) 
  then return $ TExpr Bool $ ERel ex1 op ex2
  else fail $ "Must be either Int, Doub, Bool : '" ++ show te1 ++ " " ++ 
              show op ++ " " ++ show te2
 
infer (EAnd e1 e2)      = do 
  (e1', e2') <- inferBool e1 e2
  return $ TExpr Bool $ EAnd e1' e2'

infer (EOr e1 e2)       = do
  (e1', e2') <- inferBool e1 e2
  return $ TExpr Bool $ EOr e1' e2'

inferArith :: Expr -> Expr -> TypeCheck (Expr, Expr)
inferArith e1 e2 = do
  e1'@(TExpr te1 _) <- infer e1
  e2'@(TExpr te2 _) <- infer e2
  let te1' = ext te1
  let te2' = ext te2
 
  if te1' == te2' && (te1' == Int || te1' == Doub) then return (e1', e2')
  else fail $ "Arithmetic operations: " ++ printTree e1 ++ " and " ++ 
              printTree e2 ++ " must be either Int or Double"

inferBool :: Expr -> Expr -> TypeCheck (Expr, Expr)
inferBool e1 e2 = do
  e1'@(TExpr te1 _) <- infer e1
  e2'@(TExpr te2 _) <- infer e2
  let te1' = ext te1
  let te2' = ext te2
  if te1' == te2' && te1' == Bool then return (e1', e2')
  else fail $ "Condition: " ++ printTree e1 ++ " and " ++ 
              printTree e2 ++ " must be Bool"

inferAIndex :: [ASize] -> TypeCheck [ASize]
inferAIndex [] = return []
inferAIndex ((ArrSize e):is) = do
  e'@(TExpr te _) <- infer e
  rest <- inferAIndex is
  if te == Int then return $ (ArrSize e') : rest
  else fail $ "Expression " ++ show e ++ 
              " inside [] must be of type Int, but is " ++ show te

-------------------------------------------------------------------------------
-- Enviornment Functions

empty :: Env
empty = (Ident "", emptyScope, [emptyScope])

crntDef :: Ident -> TypeCheck ()
crntDef c = modify $ \(_,d,s) -> (c,d,s)

typeCrntDef :: TypeCheck Type
typeCrntDef = do
  (c,_,_) <- get 
  (Fun t _) <- lookupDef c
  return t

emptyScope :: Scope
emptyScope = M.empty

newScope :: TypeCheck ()
newScope = modify $ \(c,d,s) -> (c,d, emptyScope : s)

pop :: TypeCheck ()
pop = modify $ \(c,d,s:ss) -> (c,d,ss)

addDef :: Ident -> Type -> [Type] -> TypeCheck () 
addDef x t args = do
  (c,d,s) <- get
  case M.lookup x d of
    Nothing  -> modify $ \(c,d,s) -> (c, M.insert x (Fun t args) d, s)
    (Just _) -> fail $ "Function: " ++ show x ++ " already declared."

lookupDef :: Ident -> TypeCheck Type
lookupDef x = do
  (c,d,s) <- get
  case M.lookup x d of
    Nothing -> fail $ "Function: " ++ show x ++ " was not declared."
    Just t  -> return t

addVar :: Ident -> Type -> TypeCheck ()
addVar x t = do
  (c,d,s:ss) <- get
  case M.lookup x s of
    Nothing  -> put (c,d, M.insert x t s : ss) 
    (Just _) -> fail $ "Variable: " ++ show x ++ " already exist in the same scope."

lookupVar :: Ident -> TypeCheck Type
lookupVar x = do
  (c,d,s) <- get
  look' s
 
  where
  look' :: [Scope] -> TypeCheck Type
  look' []    = fail $ "Variable: " ++ show x ++ " is not declared."
  look' (s:ss)= case M.lookup x s of
                  Nothing -> look' ss
                  Just t  -> return t
 
addDecl :: Type -> [Item] -> TypeCheck [Item]
addDecl t []                = return [] --fail $ "addDecl : " ++ show t
addDecl t ((NoInit x):is)   = do 
  addVar x t
  is' <- addDecl t is
  return $ (NoInit x) : is'

addDecl t ((Init x e):is)   = do 
  e' <- checkExp e t 
  addVar x t
  is' <- addDecl t is
  return $ (Init x e') : is'

-----------------------------------------------------------------------------
-- Built-In Functions

builtinDef :: TypeCheck ()
builtinDef = do
  addDef (Ident "printInt")     Void [Int]
  addDef (Ident "printDouble")  Void [Doub]
  addDef (Ident "printString")  Void [Str]
  addDef (Ident "readInt")      Int  []
  addDef (Ident "readDouble")   Doub []
