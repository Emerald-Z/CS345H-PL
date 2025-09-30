{-# LANGUAGE MonadComprehensions #-}

import Parser (parse, Term(..))
import qualified Data.Map as M
import qualified Control.Monad.State.Lazy as SM
import Data.Maybe (mapMaybe)

-------- Environment ---------
-- TODO: combine the maps into one with different types
data Env = Env { symbolTable :: M.Map String (Maybe Integer) -- maps variable names to values
               , functionTable :: M.Map String ([String], Term) -- maps function names to (parameters, body)
               , input :: [Integer] -- input stream (used by read)
               , output :: [Integer] -- output stream (used by write)
               } deriving Show

-- TODO: error handling with ExceptT monad, which gives you catchError and throwError functions
type Stack = [Env]
getTopEnv :: Stack -> Maybe Env
getTopEnv [] = Nothing
getTopEnv (env:_) = Just env

varExists :: String -> SM.StateT Stack IO Bool
varExists name = do
    stack <- SM.get
    case getTopEnv stack of
        Just env -> case M.lookup name (symbolTable env) of
            Just (Just _) -> return True
            Just Nothing -> return True
            Nothing -> return False
        Nothing -> return False

updateTopEnv :: (Env -> Env) -> Stack -> Stack
updateTopEnv f [] = []
updateTopEnv f (env:rest) = f env : rest

isBlock :: Term -> Bool
isBlock (Block _) = True
isBlock _ = False

eval :: Term -> SM.StateT Stack IO (Either String (Maybe Integer))

eval (Literal n) =
    return (Right (Just n))

eval (Add e1 e2) = do
    v1 <- eval e1
    v2 <- eval e2
    case (v1, v2) of
        (Right (Just n1), Right (Just n2)) -> return (Right (Just (n1 + n2)))
        (Left e, _) -> return (Left e)
        (_, Left e) -> return (Left e)
        _ -> return (Left "Undefined variable - add Nothing")

eval (Var name) = do -- look through all environments in the stack
    stack <- SM.get
    let loop :: Stack -> SM.StateT Stack IO (Either String (Maybe Integer))
        loop [] = return (Left "Undefined variable - var Nothing")
        loop (env:rest) = do
            case M.lookup name (symbolTable env) of
                Just Nothing -> return (Left "Uninitialized variable")
                Just (Just val) -> return (Right (Just val))
                Nothing -> loop rest
    loop stack

eval (Assignment name rhs) = do
    v <- eval rhs
    case v of
        Right (Just n) -> do
            stack <- SM.get
            let loop :: Stack -> Int -> SM.StateT Stack IO (Either String (Maybe Integer))
                loop [] _ = return (Left "Undefined variable - assigning Nothing")
                loop (env:rest) idx = do
                    case M.lookup name (symbolTable env) of
                        Just _ -> do
                            -- Update the specific environment at index idx
                            _ <- SM.modify (\st -> 
                                let (before, target:after) = splitAt idx st
                                    updatedTarget = target { symbolTable = M.insert name (Just n) (symbolTable target) }
                                in before ++ (updatedTarget : after))
                            return (Right (Just n))
                        Nothing -> loop rest (idx + 1)
            loop stack 0
        Right Nothing -> return (Left "Undefined variable - assigning Nothing")
        Left e -> return (Left e)

eval (Instantiate name n) = do
    v <- eval n
    case v of
        Right (Just n) -> do
            stack <- SM.get
            let deleteFunctionFromStack :: Stack -> Stack
                deleteFunctionFromStack = (\st -> 
                    updateTopEnv (\env -> env { functionTable = M.delete name (functionTable env) }) st)
            _ <- SM.put (deleteFunctionFromStack stack)
            
            _ <- SM.modify (\st -> 
                updateTopEnv ( \env -> env { symbolTable = M.insert name (Just n) (symbolTable env) }) st)
            return (Right (Just n))
        Right Nothing -> return (Left "Undefined variable - instantiating Nothing")
        Left e -> return (Left e)   

eval (Declare name) = do
    -- delete function from stack
    stack <- SM.get
    let deleteFunctionFromStack :: Stack -> Stack
        deleteFunctionFromStack = (\st -> 
            updateTopEnv (\env -> env { functionTable = M.delete name (functionTable env) }) st)
    _ <- SM.put (deleteFunctionFromStack stack)

    -- add to symbol table
    _ <- SM.modify (\st -> 
        updateTopEnv ( \env -> env { symbolTable = M.insert name Nothing (symbolTable env) }) st)
    return (Right Nothing)

eval (If cond thenStmt elseStmt)  = do
    v <- eval cond
    thenStmt' <- if isBlock thenStmt then return thenStmt else return (Block [thenStmt])
    elseStmt' <- if isBlock elseStmt then return elseStmt else return (Block [elseStmt])
    case v of
        Right (Just n) -> if n /= 0 then eval thenStmt' else eval elseStmt'
        Right Nothing -> return (Left "Undefined variable - if Nothing")
        Left e -> return (Left e)

eval (While cond body) = loop (Right (Nothing)) where
    loop last = do
        v <- eval cond    
        case v of
            Right (Just n) -> if n == 0 then
                return last
            else do
                x <- eval body
                case x of
                    Right (Just n) -> loop (Right (Just n))
                    Right Nothing -> loop (Right Nothing)
                    Left e -> return (Left e)
            Right Nothing -> return (Left "Undefined variable - while Nothing")
            Left e -> return (Left e)

eval (Sequence ss) = loop (Right (Just 0)) ss where
    loop last [] = return last
    loop _ (s:ss) = do
        x <- eval s
        case x of
            Right (Just n) -> loop (Right (Just n)) ss
            Right Nothing -> loop (Right Nothing) ss -- TODO: is this correct?
            Left e -> return (Left e)

-- Handle additional Term constructors from Parser.hs
eval (Negate e) = do
    v <- eval e
    case v of
        Right (Just n) -> return (Right (Just (-n)))
        Right Nothing -> return (Left "Undefined variable - negate Nothing")
        Left e -> return (Left e)

eval (Print e) = do
    v <- eval e
    case v of
        Right (Just n) -> do
            -- _ <- SM.modify $ \stack -> 
            --     updateTopEnv ( \env -> env { output = output env ++ [n] }) stack
            SM.lift $ putStrLn (show n)
            return (Right (Just n))
        Right Nothing -> return (Left "Undefined variable - print Nothing")
        Left e -> return (Left e)

eval (Try e1 e2) = do
    result <- eval e1
    case result of
        Left _ -> do
            eval e2
        Right v -> do
            return (Right v)

eval (Fun name params body) = do
    -- check if var exists and delete if it does
    exists <- varExists name
    if exists then do
        _ <- SM.modify (\st -> 
            updateTopEnv ( \env -> env { symbolTable = M.delete name (symbolTable env) }) st)
        return ()
    else
        return ()
    -- return 0 and store in function table
    _ <- SM.modify (\st -> 
        updateTopEnv ( \env -> env { functionTable = M.insert name (params, body) (functionTable env) }) st)
    return (Right Nothing)

eval (Block terms) = do
    -- Create new scope, evaluate all terms in sequence, return last value
    case terms of
        [] -> return (Right Nothing)
        _ -> do
            let env' = Env {symbolTable = M.empty, functionTable = M.empty, input = [], output = []}
            -- add to stack
            _ <- SM.modify (\st -> env' : st) -- append to end of stack/front of array
            -- evaluate sequence
            result <- eval (Sequence terms)
            -- remove from stack
            _ <- SM.modify (\st -> tail st)
            return result

eval (Call func args) = do
    -- find function in symbol table
    stack <- SM.get
    -- check if it is a var - TODO: without this 004 fails but seems sus
    exists <- varExists func

    case exists of
        True -> return (Left "Variable is not a function")
        False -> do
            let loop :: Stack -> SM.StateT Stack IO (Either String (Maybe Integer))
                loop [] = return (Left "Function not found") -- TODO: error and catch
                loop (env:rest) = do
                    case M.lookup func (functionTable env) of
                        Nothing -> loop rest
                        Just (params, body) -> do
                            if length args /= length params then
                                return (Left "Invalid number of arguments")
                            else do
                                -- locally instantiate parameters
                                if length params == 0 
                                then do
                                    let env' = env { symbolTable = M.empty }
                                    _ <- SM.modify (\st -> env' : st) -- append to end of stack/front of array
                                    -- evaluate body
                                    result <- eval body
                                    -- remove from stack
                                    _ <- SM.modify (\st -> tail st)
                                    return result
                                else do
                                    --                           args' <- mapM eval args
                                    -- -- Check if all arguments evaluated successfully
                                    if length args /= length params then
                                        return (Left "Invalid number of arguments")
                                    else do
                                    -- -- Check if any arguments failed to evaluate
                                    --     let hasError = any (\arg -> case arg of Left _ -> True; Right _ -> False) args'
                                    --     if hasError then
                                    --         return (Left "Invalid arguments")
                                    --     else do
                                    --         -- Extract values from successful evaluations
                                    --         let values = [v | Right v <- args']
                                    -- Evaluate arguments sequentially, stopping on first failure
                                        let evalArgs :: [Term] -> SM.StateT Stack IO (Either String [Maybe Integer])
                                            evalArgs [] = return (Right [])
                                            evalArgs (arg:rest) = do
                                                result <- eval arg
                                                case result of
                                                    Left err -> return (Left err)
                                                    Right Nothing -> return (Left "Undefined variable - eval Args Nothing")
                                                    Right val -> do
                                                        restResults <- evalArgs rest
                                                        case restResults of
                                                            Left err -> return (Left err)
                                                            Right vals -> return (Right (val : vals))
                                        argsResult <- evalArgs args
                                        case argsResult of
                                            Left err -> return (Left err)
                                            Right values -> do
                                                let env' = env { symbolTable = M.fromList (zip params values) }
                                                -- add to stack
                                                _ <- SM.modify (\st -> env' : st) -- append to end of stack/front of array
                                                -- evaluate body
                                                result <- eval body
                                                -- remove from stack
                                                _ <- SM.modify (\st -> tail st)   
                                                return result
            loop stack

eval (Comment terms) = do
    return (Right Nothing)


-- eval :: Term -> (IO (), Maybe Integer)

-------- Programs ---------
newtype Program = Program Term

run :: Program -> [Integer] -> IO (Either String (Maybe Integer), Stack)
run (Program stmt) stdin =
    let env = Env { symbolTable = M.empty, functionTable = M.empty, input = stdin, output = [] }
    in SM.runStateT (eval stmt) [env]

main = do
    prog <- getContents
    let (ast, rest) = parse prog
    if not (null rest) then
        error ("Unconsumed input: " ++ show rest)
    else do
        -- Wrap the AST in a Program to run it
        let program = Program ast
        (result, finalEnv) <- run program []
        case result of
            Left _ -> putStrLn "Nothing"
            Right value -> print value

