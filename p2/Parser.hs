module Parser where

import Lexer (lexer, Token(Ident, Num, Keyword, Symbol))
import GHC.Conc (par)

data Term =
    Call String [Term]            -- calls a function with arguments
    -- | more term constructors
    | Literal Integer           -- returns its value
    | Add Term Term             -- returns the sum of its arguments
    | Negate Term               -- returns the negation of its argument
    | Assignment String Term    -- returns the value of the term
    | If Term Term Term         -- returns the value of the selected branch
    | While Term Term           -- returns the value of the last body execution or 0
    | Sequence [Term]           -- returns the value of the last statement or 0
    | Try Term Term             -- returns the value of the try block or the value of the catch block
    | Print Term                -- returns the value printed
    | Fun String [String] Term  -- defines a function with parameters and body (can have no parameters)
    | Block [Term]              -- returns the value of the last statement or 0
    | Var String                -- variable reference
    | Instantiate String Term   -- instantiates a variable
    | Declare String            -- declares a variable as Nothing
    | Comment [Term]            -- ignores everything until the next $
    deriving (Show, Eq)


missing s = error ("Missing case in parser: " ++ s)

-----------------
-- parseParams --
-----------------

extractParams :: [Token] -> ([String], [Token])
extractParams (Ident param : Symbol "," : rest) = -- pattern matching for list that starts with Ident param and Symbol "," and then the rest of the list
    let (more, rest') = extractParams rest -- recursive call to extractParams
    in (param : more, rest')
extractParams (Ident param : Symbol ")" : rest) = ([param], rest)
extractParams (Symbol ")" : rest) = ([], rest)
extractParams tokens = ([], tokens)

parseParams :: [Token] -> ([String], [Token])
parseParams (Symbol "(" : rest) =
    extractParams rest
parseParams (Symbol "()" : rest) = ([], rest)
parseParams tokens = ([], tokens)

-----------------
-- expressions --
-----------------

parseExpr0 :: [Token] -> (Term, [Token]) -- parse 'Add' expression
parseExpr0 tokens = 
    let (term, rest) = parseExpr1 tokens in
    case rest of
        (Symbol "+" : rest') ->
            let (term', rest'') = parseExpr0 rest' in
            (Add term term', rest'')
        _ -> (term, rest)

parseExpr1 :: [Token] -> (Term, [Token]) -- parse 'Negate' expression
parseExpr1 (Symbol "-" : rest) =
    let (term, rest') = parseExpr2 rest in
    (Negate term, rest')
parseExpr1 tokens = parseExpr2 tokens

parseExpr2 :: [Token] -> (Term, [Token]) 
parseExpr2 (Num n : rest) = (Literal n, rest)
parseExpr2 (Ident name : Symbol "(" : rest) = 
    let (args, rest') = parseArgs rest in
    (Call name args, rest')
parseExpr2 (Ident name : Symbol "()" : rest) = 
    (Call name [], rest)
parseExpr2 (Symbol "(" : Symbol "{}" : rest) = 
    let (term, rest') = parseExpr0 (Symbol "{}" : rest) in
    case rest' of
        (Symbol ")" : rest'') -> (term, rest'')
        _ -> error ("Expected closing parenthesis, but got: " ++ show (take 10 rest'))

parseExpr2 (Symbol "{" : rest) =
    let (terms, rest') = parseTerms (Just (Symbol "}")) rest in
    (Block terms, rest')
parseExpr2 (Symbol "{}" : rest) = (Block [], rest)

parseExpr2 (Symbol "(" : rest) =
    let (term, rest') = parseTerm rest in
    case rest' of
        (Symbol ")" : rest'') -> (term, rest'')
        _ -> error ("Expected closing parenthesis, but got: " ++ show (take 10 rest'))
parseExpr2 (Ident name : rest) = (Var name, rest)
parseExpr2 tokens = error ("Unexpected tokens in expression: " ++ show (take 10 tokens))

---------------
-- ParseArgs --
---------------

parseArgs :: [Token] -> ([Term], [Token])
parseArgs (Symbol ")" : rest) = ([], rest) -- no args
parseArgs tokens = 
    let (arg, rest) = parseTerm tokens in
    case rest of
        (Symbol "," : rest') ->
            let (otherArgs, rest'') = parseArgs rest' in
            (arg : otherArgs, rest'')
        (Symbol ")" : rest') -> ([arg], rest')
        _ -> error ("Expected closing parenthesis, but got: " ++ show (take 10 rest))


---------------
-- ParseTerm --
---------------

parseTerm :: [Token] -> (Term, [Token])

-- fun
parseTerm (Keyword "fun" : Ident name : rest) =
    let (params, rest') = parseParams rest in
    let (body, rest'') = parseTerm rest' in
    (Fun name params body, rest'')

-- block
-- parseTerm (Symbol "{" : rest) =
--     let (terms, rest') = parseTerms (Just (Symbol "}")) rest in
--     (Block terms, rest')

-- parseTerm (Symbol "{}" : rest) = (Block [], rest)

-- comment - ignore everything until the next $
parseTerm (Symbol "$" : rest) = 
    let (terms, rest') = parseTerms (Just (Symbol "$")) rest in
    (Block terms, rest')

parseTerm (Keyword "print" : rest) =
    let (arg, rest') = parseTerm rest in
    (Print arg, rest')

parseTerm (Keyword "if" : rest) =
    let (cond, rest') = parseTerm rest in
    let (thenBranch, rest'') = parseTerm rest' in
    case rest'' of
        (Keyword "else" : rest''') ->
            let (elseBranch, rest'''') = parseTerm rest''' in
            (If cond thenBranch elseBranch, rest'''')
        _ -> (If cond thenBranch (Block []), rest'')

-- while
parseTerm (Keyword "while" : rest) =
    let (cond, rest') = parseTerm rest in
    let (body, rest'') = parseTerm rest' in
    (While cond body, rest'')

-- val declaration
parseTerm (Keyword "var" : Ident name : rest) =
    case rest of
        (Symbol "=" : rest') ->
            let (initExpr, rest'') = parseTerm rest' in
            (Instantiate name initExpr, rest'')
        _ -> (Declare name, rest)
        -- _ -> error ("Expected assignment, but got: " ++ show rest)  -- Default to 0 for uninitialized variables

parseTerm (Keyword "try" : rest) =
    let (tryBlock, rest') = parseTerm rest in
    case rest' of
        (Keyword "catch" : rest'') ->
            let (catchBlock, rest''') = parseTerm rest'' in
            (Try tryBlock catchBlock, rest''')
        _ -> error ("Expected catch block, but got: " ++ show rest')

parseTerm (Ident name : Symbol "=" : rest) =    
    let (initExpr, rest') = parseTerm rest in
    (Assignment name initExpr, rest')

-- expression
parseTerm tokens = parseExpr0 tokens

----------------
-- parseTerms --
----------------

parseTerms :: Maybe Token -> [Token] -> ([Term], [Token])
parseTerms Nothing [] = ([], [])
parseTerms (Just x) [] = error ("Expected closing token: " ++ show x ++ ", but got end of input")
parseTerms (Just x) (c:rest) | c == x = ([], rest) 
parseTerms end tokens =
    let (term, rest) = parseTerm tokens in
    let (terms, rest') = parseTerms end rest in
    (term : terms, rest')


parse :: String -> (Term, [Token])
parse s = let tokens = lexer s in
    let (terms, rest) = parseTerms Nothing tokens
    in (Sequence terms, rest)