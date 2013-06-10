--------------------------------------------------------------------------------
-- Compiler Construction 
-- TDA282
-- Niclas Tall

module CodeGeneration.AbsJVM where

import AbsJavalette
import Prelude hiding (EQ, LT, GT)
import Data.Char (toUpper)

type Index = Int
type Label = String
type Ref = Int

data Instr =
  -- Meta Instructions
    Header String
  | Invoke String String JType [JType]
  -- Load And Store
  | Load  JType Index
  | LoadR
  | Store JType Index
  | StoreR
  | Return JType 
  -- Arith
  | Nega JType
  | Addi JType
  | Subs JType
  | Mult JType
  | Divi JType
  | IInc Index Value
  | Modu  
  | And
  | Or
  | DCmp Rel      -- Only for doubles
  -- Stack Manipulation
  | Pop
  | Push Value
  | Dup
  -- Control Flow
  | Lbl Label
  | Goto Label
  | If Rel Label
  | IfCmp Rel Label
  -- Array
  | NArr JType
  deriving Eq

data Value = 
    JInt    Integer
  | JDoub   Double
  | JString String
  deriving (Show, Eq)
data Rel =
    EQ
  | NEQ
  | LT
  | GEQ
  | GT
  | LEQ     
  deriving (Show, Eq)  

data JType =
    I
  | D
  | V
  | S
  | JArr JType Int
  | JFun JType [JType]
  deriving Eq

instance Show JType where
  show I              = "i"
  show D              = "d"
  show V              = ""
  show S              = "Ljava/lang/String;"
  show (JArr t _)      = show t ++ "a"
  show (JFun t targs) = show t --"JFun " ++ show t ++ " " ++ show targs

sp2 = "  "
sp4 = "    "

instance Show Instr where
  -- Meta Instructions
  show (Header s) = s
  show (Invoke c f t targs) = sp4 ++ "invokestatic " ++ c ++ "/" ++ f ++ "(" ++
                              concatMap show' targs ++ ")" ++ 
                              show' t

  -- Load And Store
  show (Load t i) | i >= 0 && i < 4       = sp4 ++ show t ++ "load_" ++ show i
                  | otherwise             = sp4 ++ show t ++ "load " ++ show i 
  show (Store t i)| i >= 0 && i < 4       = sp4 ++ show t ++ "store_" ++ show i
                  | otherwise             = sp4 ++ show t ++ "store " ++ show i
  show (Return t)                         = sp4 ++ show t ++ "return"

  -- Arithmetic Instructions, only working for Int and Double
  show (Nega t)                           = sp4 ++ show t ++ "neg"
  show (Addi t)                           = sp4 ++ show t ++ "add"
  show (Subs t)                           = sp4 ++ show t ++ "sub"
  show (Mult t)                           = sp4 ++ show t ++ "mul"
  show (Divi t)                           = sp4 ++ show t ++ "div"
  show (IInc v (JInt i))                  = sp4 ++ "iinc " ++ show v ++ " " ++ show i
  show (Modu)                             = sp4 ++ "irem"
  show (And)                              = sp4 ++ "iand"
  show (Or)                               = sp4 ++ "ior"
  show (DCmp EQ)                          = sp4 ++ "dcmpg"
  show (DCmp NEQ)                         = sp4 ++ "dcmpg"
  show (DCmp LT)                          = sp4 ++ "dcmpl"
  show (DCmp GEQ)                         = sp4 ++ "dcmpg"
  show (DCmp GT)                          = sp4 ++ "dcmpg"
  show (DCmp LEQ)                         = sp4 ++ "dcmpl"

  -- Stack Manipulation
  show (Pop)                              = sp4 ++ "pop"
  show (Push (JInt i))  
                  | i == (-1)             = sp4 ++ "iconst_m1"
                  | i >= 0 && i < 6       = sp4 ++ "iconst_" ++ show i
                  | i > (-129) && i < 128 = sp4 ++ "bipush " ++ show i
              | i > (-32769) && i < 32767 = sp4 ++ "sipush " ++ show i  
                  | otherwise             = sp4 ++ "ldc " ++ show i
  show (Push (JDoub i)) 
                  | i == 0                = sp4 ++ "dconst_0"
                  | i == 1                = sp4 ++ "dconst_1"
                  | otherwise             = sp4 ++ "ldc2_w " ++ show i
  show (Push (JString s))                 = sp4 ++ "ldc \"" ++ s ++ "\""             
  show (Dup)                              = sp4 ++ "dup"

  -- Control Flow
  show (Lbl l)                            = sp2 ++ l ++ ":"
  show (Goto l)                           = sp4 ++ "goto " ++ l
  show (If EQ l)                          = sp4 ++ "ifeq " ++ l
  show (If NEQ l)                         = sp4 ++ "ifne " ++ l
  show (If LT l)                          = sp4 ++ "iflt " ++ l
  show (If GEQ l)                         = sp4 ++ "ifge " ++ l
  show (If GT l)                          = sp4 ++ "ifgt " ++ l
  show (If LEQ l)                         = sp4 ++ "ifle " ++ l
  show (IfCmp EQ l)                       = sp4 ++ "if_icmpeq " ++ l
  show (IfCmp NEQ l)                      = sp4 ++ "if_icmpne " ++ l
  show (IfCmp LT l)                       = sp4 ++ "if_icmplt " ++ l
  show (IfCmp GEQ l)                      = sp4 ++ "if_icmpge " ++ l
  show (IfCmp GT l)                       = sp4 ++ "if_icmpgt " ++ l
  show (IfCmp LEQ l)                      = sp4 ++ "if_icmple " ++ l

--------------------------------------------------------------------------------
-- Helper functions

fstUpper :: String -> String
fstUpper []     = []
fstUpper (x:xs) = toUpper x : xs

show' :: JType -> String
show' I              = "I"
show' D              = "D"
show' V              = "V"
show' S              = "Ljava/lang/String;"
show' (JFun t _)     = show t 
