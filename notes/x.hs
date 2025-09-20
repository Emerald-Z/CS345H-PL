import Data.Map
import qualified Data.Map as M

data Expression = Var String
                | Literal Integer
                | Add Expression Expression
                | Read 

data Statement = Assignment String Expression
                | If Expression Statement Statement 
                | While Expression Statement
                | Sequence [Statement]
                | Write Expression 

newtype Program = Program Statement

data Env = Env (M String Integer) [Integer] [Integer]





-- This code was before we had to implement Read 
-- meaningExp :: Expression -> Env -> Integer

-- data Maybe a = Nothing | Just a

-- meaningExp (Literal n) = \env -> n 
-- meaningExp (Add e1 e2) = meaningExp e1 + meaningExp e2
-- meaningExp (Read) = 42  -- Placeholder for reading input
-- meaningExp (Var x) (Env symbolTable input output) = case M.lookup x symbolTable of 
--     Just v -> v
--     Nothing -> error "Variable not found"  



meaningExp :: Expression -> (Env -> Maybe Integer)

data Maybe a = Nothing | Just a

meaningExp (Literal n) = Just n 
-- meaningExp (Add e1 e2) env = case (meaningExp e1 env, meaningExp e2 env) of 
--     (Just v1, Just v2) -> Just (v1 + v2)
--     _ -> Nothing
meaningExp (Add e1 e2) = [a + b | a <- meaningExp e1 env, b <- meaningExp e2 env]

meaningExp (Read) = 42  -- Placeholder for reading input
meaningExp (Var x) (Env symbolTable input output) = case M.lookup x symbolTable




-- Abstract syntax tree depth meaning 

-- meaningExp (Literal n) = 1
-- meaningExp (Add e1 e2) = 1 + max (meaningExp e1) (meaningExp e2)


main :: IO ()
main = putStrLn "Hello, world!"