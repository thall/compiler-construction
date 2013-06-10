--------------------------------------------------------------------------------
-- Compiler Construction 
-- TDA282
-- Niclas Tall

module CodeGeneration.AbsLLVM where

import AbsJavalette as J
import Data.Char

-------------------------------------------------------------------------------
--  Abstract datatypes for LLVM instructions

type Lbl = String
type Ref = Int
type Reg = Int

data Instr =
    -- Meta instructions
    Global Value Int LLVMType Value
  | Declare String LLVMType [LLVMType]
  | Define String LLVMType [Argu]
  | EndDefinition
  | Bitcast Value LLVMType Int Value LLVMType -- only for string constants
    -- Load and Store
  | Alloc Value LLVMType 
  | Load Value Ptr
  | Store LLVMType Value Ptr
    -- Arithmetic
  | Add Value LLVMType Value Value 
  | Sub Value LLVMType Value Value
  | Mul Value LLVMType Value Value
  | Div Value LLVMType Value Value 
  | Rem Value LLVMType Value Value 
    -- Control Flow
  | Call Value LLVMType String [Argu]
  | VRet
  | Ret LLVMType Value
  | BrCond Value Lbl Lbl 
  | Br Lbl
  | Phi Value LLVMType [(Value, Lbl)]
  | Label Lbl
    -- Comparison
  | Cmp Value RelOp LLVMType Value Value

data Argu   = Argu LLVMType Value

data Ptr = Ptr LLVMType Reg

data LLVMType = LLVMType Type
              | LLVMPtrType Type

data Value =
    Ref Reg             -- %r<i>
  | Glbl Reg            -- @C<i>
  | Const Integer       -- literal
  | DConst Double       -- literal
  | StrConst String     -- literal

-------------------------------------------------------------------------------
-- Show instances for the abstract LLVM instructions
sp = "    "
nl = "\n"

instance Show Instr where
  -- Meta instructions
  show (Global r n t s)    = show r ++ " = internal constant [" ++ show n ++ " x " ++
                             show t ++ "] c\"" ++ show s ++ "\\00\""

  show (Declare x t targs) = "declare " ++ show t ++ " @" ++ x ++ "(" ++  
                             ((if null targs then id else tail) . 
                                foldl (\acc a -> acc ++","++ show a) "") targs ++ ")" 
  
  show (Define  x t args)  = "define " ++ show t ++ " @" ++ x ++ "(" ++
                             ((if null args then id else tail) . foldl (\acc arg -> 
                                acc ++ "," ++ show arg) "") args ++ ") {" 
  
  show (EndDefinition)     = "}" 
  show (Bitcast r tf len s tt)   = sp ++ show r ++ " = bitcast [" ++ show len ++ " x " ++
                                   show tf ++ "]* "++ show s ++" to " ++ show tt 

  -- Load and Store
  show (Alloc r t)         = sp ++ show r ++ " = alloca " ++ show t 
  show (Load r p)          = sp ++ show r ++ " = load " ++ show p 
  show (Store t v p)       = sp ++ "store " ++ show t ++ " " ++ show v ++ ", " 
                             ++ show p 

  -- Arithmetic
  show (Add r t v1 v2)     = showArith "fadd" "add" r t v1 v2
  show (Sub r t v1 v2)     = showArith "fsub" "sub" r t v1 v2
  show (Mul r t v1 v2)     = showArith "fmul" "mul" r t v1 v2
  show (CodeGeneration.AbsLLVM.Div r t v1 v2)     = showArith "fdiv" "sdiv" r t v1 v2
  show (Rem r t v1 v2)     = showArith "frem" "srem" r t v1 v2

  -- Control Flow
  show (Call r t x args)   = (if t == LLVMType Void then sp else sp ++ show r ++ " = ") 
                             ++ "call " ++ show t ++ " @" ++ x ++
                             "(" ++ ((if null args then id else tail) . foldl (\acc arg -> 
                                      acc ++ "," ++ show arg) "") args ++ ")" 

  show (CodeGeneration.AbsLLVM.VRet)    = sp ++ "ret void" 
  show (CodeGeneration.AbsLLVM.Ret t v) = sp ++ "ret " ++ show t ++ " " ++ show v 
  show (BrCond v l1 l2)    = sp ++ "br i1 " ++show v++ ", label %" ++ l1 ++ ", label %" 
                             ++ l2 
  show (Br l)              = sp ++ "br label %" ++ l  
  show (Phi r t vl)        = sp ++ show r ++ " = phi " ++ show t ++ " " ++
                             ((if null vl then id else tail) . foldl 
                                (\a (v,l) -> a ++ ",[" ++ show v ++ ",%" ++ l ++ "]") "") vl

  show (Label l)           = "  " ++ l ++ ":" 
  show (Cmp r op t v1 v2)  = sp ++ show r ++ " = " ++ 
                             (if t == LLVMType Doub 
                             then "fcmp " ++ relOp2llvmf op 
                             else "icmp " ++ relOp2llvm op) ++ " " ++ show t ++ " " ++ 
                             show v1 ++ ", " ++ show v2  
 
instance Show Argu where
  show (Argu t r) = show t ++ " " ++ show r

instance Show LLVMType where
  show (LLVMType t)     = jl2llvm t
  show (LLVMPtrType t)  = jl2llvm t ++ "*"

instance Eq LLVMType where
  (LLVMType t1)    == (LLVMType t2)    = t1 == t2
  (LLVMType t1)    == (LLVMPtrType t2) = t1 == t2
  (LLVMPtrType t1) == (LLVMType t2)    = t1 == t2
  (LLVMPtrType t1) == (LLVMPtrType t2) = t1 == t2
  t1 /= t2                             = not (t1 == t2)

instance Show Value where
  show (Ref i)      = "%r" ++ show i
  show (Glbl i)     = "@C" ++ show i
  show (Const i)    = show i
  show (DConst i)   = show i
  show (StrConst s) = s

instance Show Ptr where
  show (Ptr t i)    = show t ++ " %r" ++ show i

-------------------------------------------------------------------------------
-- Helper functions

jl2llvm :: Type -> String
jl2llvm Int   = "i32"
jl2llvm Doub  = "double"
jl2llvm Bool  = "i1"
jl2llvm Void  = "void"
jl2llvm (Arr t _) = error "jl2llvm: Array"
jl2llvm (Fun t _) = jl2llvm t 
jl2llvm Str   = "i8"

relOp2llvm :: RelOp -> String
relOp2llvm LTH = "slt"
relOp2llvm LE  = "sle"
relOp2llvm GTH = "sgt"
relOp2llvm GE  = "sge"
relOp2llvm EQU = "eq"
relOp2llvm NE  = "ne"

relOp2llvmf :: RelOp -> String
relOp2llvmf LTH = "olt"
relOp2llvmf LE  = "ole"
relOp2llvmf GTH = "ogt"
relOp2llvmf GE  = "oge"
relOp2llvmf EQU = "oeq"
relOp2llvmf NE  = "one"

showArith :: String -> String -> Value -> LLVMType -> Value -> Value -> String
showArith f1 f2 r t v1 v2 = sp ++ show r ++ " = " ++
                            (if t == LLVMType Doub then f1 else f2) ++ " " ++ show t ++ 
                            " " ++ show v1 ++ ", " ++ show v2 
