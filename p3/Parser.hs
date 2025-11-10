{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MonadComprehensions #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use <$>" #-}

module Parser (parse, prog, term, Term (..), BinaryOp (..), UnaryOp (..)) where

import qualified Control.Monad as M
import Control.Monad.State.Lazy (runStateT)
import Data.Maybe (fromMaybe)
-- import Debug.Trace (trace)

import qualified Data.Set as S
import FunLexer (Token (Ident, Keyword, Num, StringLiteralLex, Symbol), lexer)
import ParserCombinators (Parser, Result, oneof, opt, rpt, rptDropSep, satisfy, token)
import Term (Term (..), BinaryOp (..), UnaryOp (..), ErrorKind (..), ErrorKindOrAny (..))

-- succeed if the next token is the given symbol
symbol :: String -> Parser Token ()
-- using explicit bind
symbol s = M.void (token (Symbol s))

-- succeed if the next token is the given keyword
keyword :: String -> Parser Token ()
-- using do notation (syntactic sugar for >>=)
keyword k = do
  _ <- token $ Keyword k
  return ()

-- identifier
ident :: Parser Token String
ident = satisfy $ \case
  Ident name -> Just name
  _ -> Nothing

-- symbol
checkSymbol :: (String -> Bool) -> Parser Token String
checkSymbol predicate = satisfy $ \case
  Symbol s | predicate s -> Just s
  _ -> Nothing

----------
-- term --
----------

term :: Parser Token Term
term = binaryExp precedence

------------------- binary operators (left associative) -------------------

-- precedence levels, from lowest to highest
precedence :: [S.Set String]
precedence = [S.fromList ["||"], S.fromList ["&&"], S.fromList ["==", "!="], S.fromList ["<", ">", "<=", ">="], S.fromList ["+", "-"], S.fromList ["*", "/", "%"]]

binaryExp :: [S.Set String] -> Parser Token Term
binaryExp [] = unaryExp
binaryExp (ops : rest) = do
  -- lhs
  lhs <- binaryExp rest

  -- find the longest sequence of (op, subexpression) at this precedence level
  -- then combine them left to right
  rhss <- rpt $ do
    op <- checkSymbol (`S.member` ops)
    rhs <- term
    return (op, rhs)

  -- combine results left to right
  return $ foldl (\acc (op, rhs) -> BinaryOps (stringToBinaryOp op) acc rhs) lhs rhss

stringToBinaryOp :: String -> BinaryOp
stringToBinaryOp "+" = Add
stringToBinaryOp "-" = Sub
stringToBinaryOp "*" = Mul
stringToBinaryOp "/" = Div
stringToBinaryOp "%" = Mod
stringToBinaryOp "<" = Lt
stringToBinaryOp ">" = Gt
stringToBinaryOp "<=" = Lte
stringToBinaryOp ">=" = Gte
stringToBinaryOp "==" = Eq
stringToBinaryOp "!=" = Neq
stringToBinaryOp "&&" = And
stringToBinaryOp "||" = Or
stringToBinaryOp _ = error "Unknown binary operator"

------------------- unary operators  -------------------

assign :: Parser Token Term
assign = [Let name expr | name <- ident, _ <- symbol "=", expr <- term]

-- We can use monad comprehensions (GHC extension) to make parsers more concise
minus :: Parser Token Term
minus = [UnaryOps Neg e | _ <- symbol "-", e <- unaryExp]

num :: Parser Token Term
num = do
  n <- satisfy $ \case
    Num n -> Just n
    _ -> Nothing
  return $ Literal n

string :: Parser Token Term
string = do
  s <- satisfy $ \case
    StringLiteralLex s -> Just s
    _ -> Nothing
  return $ StringLiteral s

bool :: Parser Token Term
bool = do
  b <- satisfy $ \case
    Keyword "true" -> Just True
    Keyword "false" -> Just False
    _ -> Nothing
  return $ BoolLit b

tuple :: Parser Token Term
tuple = do
  _ <- symbol "["
  elems <- rptDropSep term (symbol ",")
  _ <- symbol "]"
  return $ NewTuple elems

parens :: Parser Token Term
parens = [t | _ <- symbol "(", t <- term, _ <- symbol ")"]

funDef :: Parser Token Term
funDef = do
  _ <- keyword "fun"
  name <- ident
  _ <- symbol "("
  params <- rptDropSep ident (symbol ",")
  _ <- symbol ")"
  body <- term
  return $ Let name (Fun params body)

varRef :: Parser Token Term
varRef = Var <$> ident

block :: Parser Token Term
block = do
  _ <- token $ Symbol "{"
  ts <- rpt term
  _ <- token $ Symbol "}"
  return $ case ts of
    [] -> Skip
    [t] -> t
    _ -> foldl1 Seq ts

ifExpr :: Parser Token Term
ifExpr = do
  _ <- keyword "if"
  cond <- term
  thenTerm <- term
  elseTerm <- opt $ keyword "else" >> term
  return $ If cond thenTerm (fromMaybe Skip elseTerm)

varDef :: Parser Token Term
varDef = do
  _ <- keyword "var"
  name <- ident
  expr <- opt $ symbol "=" >> term
  return $ case expr of
    Nothing -> Let name (Literal 0)
    Just e -> Let name e

whileTerm :: Parser Token Term
whileTerm = do
  _ <- keyword "while"
  cond <- term
  body <- term
  return $ While cond body

tupleSet :: Parser Token Term
tupleSet = do
  name <- ident
  _ <- symbol "["
  index <- term
  _ <- symbol "]"
  _ <- symbol "="
  value <- term
  return $ SetTuple name index value

tupleAccess :: Parser Token Term
tupleAccess = do
  tuple <- varRef
  _ <- symbol "["
  index <- term
  _ <- symbol "]"
  return $ GetTuple tuple index

funCall :: Parser Token Term
funCall = do
  name <- ident
  _ <- symbol "("
  args <- rptDropSep term (symbol ",")
  _ <- symbol ")"
  return $ FunCall (Var name) args

-- Parser for ErrorKindOrAny
errorKindOrAny :: Parser Token ErrorKindOrAny
errorKindOrAny = do
  keyword <- satisfy $ \case
    Keyword "any" -> Just "any"
    Keyword "arithmetic" -> Just "arithmetic"
    Keyword "type" -> Just "type"
    Keyword "input" -> Just "input"
    Keyword "variable" -> Just "variable"
    Keyword "arguments" -> Just "arguments"
    _ -> Nothing
  case keyword of
    "any" -> return Any
    "arithmetic" -> return $ Specific Arithmetic
    "type" -> return $ Specific Type
    "input" -> return $ Specific Input
    "variable" -> return $ Specific VariableNotFound
    "arguments" -> return $ Specific Arguments
    _ -> error "Unknown error kind"

tryCatch :: Parser Token Term
tryCatch = do
  _ <- keyword "try"
  _ <- symbol "{"
  try <- term
  _ <- symbol "}"
  _ <- keyword "catch"
  errorKind <- errorKindOrAny
  _ <- symbol "{"
  catch <- term
  _ <- symbol "}"
  return $ TryCatch try errorKind catch

printStmt :: Parser Token Term
printStmt = do
  _ <- keyword "print"
  expr <- term
  return $ Write expr

unaryExp :: Parser Token Term
unaryExp = oneof [assign, ifExpr, block, funDef, minus, num, string, bool, tuple, tupleSet, tupleAccess, parens, varDef, funCall, varRef, whileTerm, printStmt, tryCatch]

----------- prog ----------

prog :: Parser Token Term
prog = do
  ts <- rpt term
  return $ case ts of
    [] -> Skip
    [t] -> t
    _ -> foldl1 Seq ts

----------- parse ----------

parse :: [Char] -> Parser Token a -> Result (a, [Token])
parse input p =
  let tokens = lexer input
   in runStateT p tokens
