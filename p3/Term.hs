module Term (Term (..), BinaryOp (..), UnaryOp (..), ErrorKind (..), ErrorKindOrAny (..)) where

data BinaryOp = Add | Sub | Mul | Div | Mod | Lt | Gt | Lte | Gte | Eq | Neq | And | Or
  deriving (Eq, Show)

data UnaryOp = Neg | Not
  deriving (Eq, Show)

data ErrorKind = Arithmetic | Type | Input | VariableNotFound | Arguments 
  deriving (Eq, Show)

data ErrorKindOrAny = Specific ErrorKind | Any deriving (Eq, Show)

data Term
  = If Term Term Term
  | Let String Term
  | Literal Integer
  | StringLiteral String
  | Read String
  | Seq Term Term
  | Skip
  | BinaryOps BinaryOp Term Term
  | UnaryOps UnaryOp Term
  | Var String
  | While Term Term
  | Write Term
  | BoolLit Bool          
  | Fun [String] Term -- params, body (currently no return value)
  | FunCall Term [Term] -- name, args 
  | NewTuple [Term]
  | GetTuple Term Term -- object, idx -- you can access a tuple that is a result of an expression OR by name
  | SetTuple String Term Term -- name, idx, value -- only set a tuple by name
  | TryCatch Term ErrorKindOrAny Term
  deriving (Eq, Show)
