import Parser (parse, Term(..))

eval :: Term -> (IO (), Maybe Integer)
eval = undefined

-- Pretty print function for better readability
prettyPrint :: Term -> String
prettyPrint (Literal n) = show n
prettyPrint (Add t1 t2) = "(" ++ prettyPrint t1 ++ " + " ++ prettyPrint t2 ++ ")"
prettyPrint (Negate t) = "(-" ++ prettyPrint t ++ ")"
prettyPrint (Var name) = name
prettyPrint (Assignment name t) = name ++ " = " ++ prettyPrint t
prettyPrint (If cond thenBranch elseBranch) = 
    "if " ++ prettyPrint cond ++ " then " ++ prettyPrint thenBranch ++ " else " ++ prettyPrint elseBranch
prettyPrint (While cond body) = "while " ++ prettyPrint cond ++ " do " ++ prettyPrint body
prettyPrint (Sequence terms) = "{\n" ++ unlines (map ("  " ++) (map prettyPrint terms)) ++ "}"
prettyPrint (Print t) = "print " ++ prettyPrint t
prettyPrint (Fun name params body) = 
    "fun " ++ name ++ "(" ++ unwords params ++ ") " ++ prettyPrint body
prettyPrint (Block terms) = "{\n" ++ unlines (map ("  " ++) (map prettyPrint terms)) ++ "}"
prettyPrint (Call func args) = func ++ "(" ++ unwords (map prettyPrint args) ++ ")"
prettyPrint (Try t1 t2) = "try " ++ prettyPrint t1 ++ " catch " ++ prettyPrint t2
prettyPrint (Instantiate name t) = "var " ++ name ++ " = " ++ prettyPrint t

main = do
    prog <- getContents
    let (ast, rest) = parse prog
    if not (null rest) then
        error ("Unconsumed input: " ++ show rest)
    else do
        -- Print the parsed AST in a readable format
        putStrLn "Parsed AST:"
        putStrLn (prettyPrint ast)
