module ParseTest where

import System.IO
import System.Environment (getArgs)
import FunSyntax (parse, prog)
import ParserCombinators (eof)
import Term (Term(..))

-- Test runner that can handle both file input and piped input
main :: IO ()
main = do
    args <- getArgs
    case args of
        [] -> do
            -- No arguments, read from stdin
            text <- getContents
            testParse text
        [filename] -> do
            -- One argument, read from file
            text <- readFile filename
            testParse text
        _ -> do
            putStrLn "Usage: ParseTest [filename]"
            putStrLn "  No arguments: read from stdin"
            putStrLn "  One argument: read from file"

testParse :: String -> IO ()
testParse text = do
    let result = parse text $ do
            t <- prog
            _ <- eof
            return t
    case result of
        Left err -> do
            putStrLn $ "Parse error: " ++ err
            exitFailure
        Right (ast, _) -> do
            putStrLn "Parse successful!"
            putStrLn "AST:"
            print ast
            putStrLn "AST type:"
            putStrLn $ show $ getTermType ast

-- Helper to get the type of a term
getTermType :: Term -> String
getTermType (Literal _) = "Literal"
getTermType (StringLiteral _) = "StringLiteral"
getTermType (BoolLit _) = "BoolLit"
getTermType (Var _) = "Var"
getTermType (Let _ _) = "Let"
getTermType (Seq _ _) = "Seq"
getTermType (If _ _ _) = "If"
getTermType (While _ _) = "While"
getTermType (BinaryOps _ _ _) = "BinaryOps"
getTermType (UnaryOps _ _) = "UnaryOps"
getTermType (Fun _ _) = "Fun"
getTermType (ApplyFun _ _) = "ApplyFun"
getTermType (TupleTerm _) = "TupleTerm"
getTermType (AccessTuple _ _) = "AccessTuple"
getTermType (SetTuple _ _ _) = "SetTuple"
getTermType (Write _) = "Write"
getTermType (Read _) = "Read"
getTermType Skip = "Skip"
