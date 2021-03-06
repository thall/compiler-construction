module AbsJavalette where

-- Haskell module generated by the BNF converter

newtype Ident = Ident String deriving (Eq,Ord,Show)
data Program =
   Program [TopDef]
  deriving (Eq,Ord,Show)

data TopDef =
   FnDef Type Ident [Arg] Block
  deriving (Eq,Ord,Show)

data Arg =
   Arg Type Ident
  deriving (Eq,Ord,Show)

data Block =
   Block [Stmt]
  deriving (Eq,Ord,Show)

data Stmt =
   Empty
 | BStmt Block
 | Decl Type [Item]
 | Ass Ident Expr
 | AAss Ident [ASize] Expr
 | Incr Ident
 | Decr Ident
 | Ret Expr
 | VRet
 | Cond Expr Stmt
 | CondElse Expr Stmt Stmt
 | While Expr Stmt
 | Fore Type Ident Expr Stmt
 | SExp Expr
  deriving (Eq,Ord,Show)

data Item =
   NoInit Ident
 | Init Ident Expr
  deriving (Eq,Ord,Show)

data Type =
   Int
 | Doub
 | Bool
 | Void
 | Arr Type [ADim]
 | Fun Type [Type]
 | Str
  deriving (Ord,Show)

instance Eq Type where
  Int   == Int       = True
  Int   == (Arr t _) = Int == t
  Int   == (Fun t _) = Int == t
  Int   == _        = False

  Doub  == Doub     = True
  Doub  == (Arr t _) = Doub == t 
  Doub  == (Fun t _) = Doub == t
  Doub  == _        = False

  Bool  == Bool     = True
  Bool  == (Arr t _) = Bool == t
  Bool  == (Fun t _) = Bool == t
  Bool  == _        = False 

  Void  == Void     = True
  Void  == (Arr t _) = Void == t
  Void  == (Fun t _) = Void == t
  Void  == _        = False

  (Arr t1 _) == t2  = t1 == t2
  (Fun t1 _) == t2  = t1 == t2
  Str   == Str      = True
  Str   == _        = False
  t1 /= t2          = not (t1 == t2)


data ADim =
   ArrDim
  deriving (Eq,Ord,Show)

data ASize =
   ArrSize Expr
  deriving (Eq,Ord,Show)

data Expr =
   EVar Ident
 | ELitInt Integer
 | ELitDoub Double
 | ELitTrue
 | ELitFalse
 | EApp Ident [Expr]
 | EString String
 | EArrLen Ident
 | EArrMLen Ident [ASize]
 | ENArr Type [ASize]
 | EIArr Ident [ASize]
 | Neg Expr
 | Not Expr
 | EMul Expr MulOp Expr
 | EAdd Expr AddOp Expr
 | ERel Expr RelOp Expr
 | EAnd Expr Expr
 | EOr Expr Expr
 | TExpr Type Expr
  deriving (Eq,Ord,Show)

data AddOp =
   Plus
 | Minus
  deriving (Eq,Ord,Show)

data MulOp =
   Times
 | Div
 | Mod
  deriving (Eq,Ord,Show)

data RelOp =
   LTH
 | LE
 | GTH
 | GE
 | EQU
 | NE
  deriving (Eq,Ord,Show)

