-- 9/16/2025
import qualified Data.Map as M

data Term = Literal Integer
            | Function [String] Term
            | Add Term Term
            | Negate Term
            | If Term Term (Maybe Term)
            | Let String Term
            | VarDecl String (Maybe Term)
            | Var String
            | Call Striing [Term]
            | Block [Term]
            | TryCatch Term Term

data FunType = Value Integer
            | Function Term
            | Missing -- reading a missing entry is an error

-- type defines an alias for a function type
-- type SymbolTable a = Map String a -- basically a type parameter, so now SymbolTable is a type constructor
-- type SymbolTable = Map String Term -- now SymbolTable is a type constructor that takes a type parameter (lazy because we don't evaluate term immediately)
data SymbolTableEntry = LiteralEntry Integer
                        | Function [String] Term
                        | Missing

type SymbolTable = M.Map String SymbolTableEntry


-- type Stack = [SymbolTable] -- array representation
data Stack = Stack (M.Map String SymbolTableEntry) (Maybe SymbolTableEntry) -- each entry has a parent, linked list representation
