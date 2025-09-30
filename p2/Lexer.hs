module Lexer(lexer, Token(Num, Ident, Keyword, Symbol)) where

import Data.List (unfoldr)
import Data.Char (isNumber, isSpace, isSymbol, isAlpha, isAlphaNum) -- guards --
import Data.Set (fromList, member)

data Token = Num Integer
        | Ident String
        | Keyword String
        | Symbol String
        | Error String
        deriving (Show, Eq)

other = fromList "[],"

keywords = fromList [
    "fun", "var", "val", "if", "else", "while", "print", "try", "catch"]


lexer :: [Char] -> [Token]
lexer  = unfoldr step where
    step [] = Nothing
    -- skip spaces and new lines
    step (c : rest) | isSpace c = step rest
    -- numbers
    -- the @ keyword is called "as-pattern" to pattern match on a value AND give it a name
    step s@(c : _) | isNumber c =
        let (num, rest) = span isNumber s -- span is a function that takes a predicate and a list and returns a tuple of the list that satisfies the predicate and the rest of the list
        in Just (Num $ read num, rest)
    -- identifiers and keywords
    step s@(c : _) | isAlphaNum c || c == '_' =
        let (var, rest) = span (\ch -> isAlphaNum ch || ch == '_') s
        in Just (if member var keywords then Keyword var else Ident var, rest)
    -- symbols
    step s@(c : _) | isSymbol c =
        let (var, rest) = span isSymbol s
        in Just (Symbol var, rest)
    -- minus sign (handled separately to prevent combinations like "(-")
    step ('-' : rest) = Just (Symbol "-", rest)
    -- other operators
    step ('(' : ')' : rest) = Just (Symbol "()", rest)
    step ('(' : rest) = Just (Symbol "(", rest)
    step (')' : rest) = Just (Symbol ")", rest)
    step ('{' : '}' : rest) = Just (Symbol "{}", rest)
    step ('{' : rest) = Just (Symbol "{", rest)
    step ('}' : rest) = Just (Symbol "}", rest)
    step s@(c: _) | member c other =
        let (var, rest) = span (`member` other) s
        in Just (Symbol var, rest)

    step s = Just (Error ("Unexpected character: " ++ take 20 s), "")