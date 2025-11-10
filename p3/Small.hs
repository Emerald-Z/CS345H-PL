{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Small (reduceFully, Machine (..), Result (..), Env, Error) where

import qualified Control.Monad.State as S
import Data.Either
import Debug.Trace (trace)
import Term (BinaryOp (..), Term (..), UnaryOp (..), ErrorKind (..), ErrorKindOrAny (..))
import Value (Value (..), valueToInt, valueToTuple)

----- The Machine type class -----

-- The micro-ops that a machine must support
-- Allow an implementation to define its own semantics

class Machine m where
  type V m -- The value type for this machine
  -- Uses associated an associated type family for the value type
  -- This requires the TypeFamilies extension
  -- The way you read the type signature is:
  --    for any type m that is an instance of Machine, there is an associated type (V m)

  -- Get and set variables
  getVar :: String -> Env m
  setVar :: String -> V m -> Env m

  -- I/O
  inputVal :: Env m
  outputVal :: V m -> Env m

  -- Arithmetic and control
  addVal :: V m -> V m -> Env m
  subVal :: V m -> V m -> Env m
  mulVal :: V m -> V m -> Env m
  divVal :: V m -> V m -> Env m
  modVal :: V m -> V m -> Env m
  negVal :: V m -> Env m

  -- Comparison operations (operate on integers, return booleans)
  ltVal :: V m -> V m -> Env m
  gtVal :: V m -> V m -> Env m
  lteVal :: V m -> V m -> Env m
  gteVal :: V m -> V m -> Env m
  eqVal :: V m -> V m -> Env m
  neqVal :: V m -> V m -> Env m

  -- Logical operations (operate on booleans)
  andVal :: V m -> V m -> Env m
  orVal :: V m -> V m -> Env m
  notVal :: V m -> Env m

  -- Control flow - selectValue uses boolean semantics
  selectValue :: V m -> Env m -> Env m -> Env m

  -- Scoping
  getScope :: m -> [(String, Value)] -- gets the scope for a variable
  addScope :: [(String, Value)] -> Env m
  deleteScope :: Env m -- exiting scope

  -- Tuples
  getValueAtIndex :: V m -> V m -> Env m
  setValueAtIndex :: String -> Integer -> V m -> Env m -- tuple, idx, value

-- Errors
type Error = (ErrorKind, String)
shouldCatchError :: ErrorKind -> ErrorKindOrAny -> Bool
shouldCatchError _ Any = True
shouldCatchError resultErrorKind (Specific catchableErrorKind) = resultErrorKind == catchableErrorKind

----- The Result type -----

data Result a
  = Happy a -- produced an answer
  | Continue Term -- need to keep going
  | Sad Error -- error
  deriving (Eq, Show)

----- The Env monad -----

-- abstract semantics that glue micro-ops together
type Env m = S.State m (Result (V m))

premise :: Env m -> (Term -> Term) -> (V m -> Env m) -> Env m
premise e l r = do
  v <- e
  case v of
    Continue t' -> return $ Continue (l t')
    Happy n -> r n
    Sad _ -> return v

------ Small-step reduction ------

reduce_ :: (Machine m, Show m, V m ~ Value) => Term -> Env m
reduce_ (Literal n) =
  return $ Happy $ IntVal n
reduce_ (StringLiteral s) =
  return $ Happy $ StringVal s
reduce_ (Var x) =
  getVar x
reduce_ (Let x t) = do
  premise
    (reduce t)
    (Let x)
    (setVar x)
reduce_ (Seq t1 t2) = do
  premise
    (reduce t1)
    (`Seq` t2)
    (\_ -> return $ Continue t2)
reduce_ (If cond tThen tElse) = do
  premise
    (reduce cond)
    (\cond' -> If cond' tThen tElse)
    (\v -> selectValue v (return $ Continue tThen) (return $ Continue tElse))
reduce_ w@(While cond body) =
  return $ Continue (If cond (Seq body w) Skip)
reduce_ (Read x) =
  premise
    inputVal
    id
    (setVar x)
reduce_ (Write t) = do
  premise
    (reduce t)
    Write
    outputVal
reduce_ Skip =
  return $ Happy (IntVal 0)
reduce_ (BinaryOps op t1 t2) =
  premise
    (reduce t1)
    (\t1' -> BinaryOps op t1' t2)
    ( \v1 ->
        premise
          (reduce t2)
          (BinaryOps op (Literal $ fromRight (-1) (valueToInt v1)))
          (applyBinaryOp op v1)
    )
  where
    applyBinaryOp Add = addVal
    applyBinaryOp Sub = subVal
    applyBinaryOp Mul = mulVal
    applyBinaryOp Div = divVal
    applyBinaryOp Mod = modVal
    applyBinaryOp Lt = ltVal
    applyBinaryOp Gt = gtVal
    applyBinaryOp Lte = lteVal
    applyBinaryOp Gte = gteVal
    applyBinaryOp Eq = eqVal
    applyBinaryOp Neq = neqVal
    applyBinaryOp And = andVal
    applyBinaryOp Or = orVal
reduce_ (BoolLit b) =
  return $ Happy $ BoolVal b
reduce_ (UnaryOps op t) =
  premise
    (reduce t)
    (UnaryOps op)
    (applyUnaryOp op)
  where
    applyUnaryOp Neg = negVal
    applyUnaryOp Not = notVal

-- tuples
reduce_ (NewTuple terms) = 
  case terms of
      (t : rest) ->
        -- process t
        premise
          (reduce t)
          (\t' -> NewTuple $ t' : rest)
          (\v1 -> premise
            (reduce $ NewTuple rest)
            (\term' -> 
                case term' of
                  NewTuple ts' -> NewTuple (t : ts')
                  _ -> error "NewTuple resulted in non-NewTuple continuation"
            )
            (\v2 -> return $ Happy $ TupleVal (v1 : (fromRight [] $ valueToTuple v2)))
          )
      [] -> return $ Happy $ TupleVal []

reduce_ (GetTuple tuple idx) = 
  premise
    (reduce tuple)
    (\tuple' -> GetTuple tuple' idx)
    (\v1 -> 
      premise
        (reduce idx)
        (GetTuple tuple)
        (getValueAtIndex v1)
    )
-- specify an index to set in the tuple
reduce_ (SetTuple name idx value) = 
  premise
    (reduce idx)
    (SetTuple name value)
    (\v2 -> 
      case v2 of 
        IntVal intv2 ->
          premise
            (reduce value)
            (\value' -> SetTuple name idx value')
            (\v3 -> setValueAtIndex name intv2 v3)
        _ -> return $ Sad (Type, "Type error in SetTuple")
    )

-- try-catch statement
reduce_ (TryCatch try errorKind catch) = do
  value <- reduce try
  case value of 
    Continue try' -> return $ Continue (TryCatch try' errorKind catch)
    Happy n -> return $ Happy n
    Sad (resultErrorKind, _) | shouldCatchError resultErrorKind errorKind -> return $ Continue catch
    Sad _ -> return value

-- functions
reduce_ (Fun params body) = do
  env <- S.get
  let scope = getScope env
  return $ Happy (ClosureVal params body scope)

reduce_ (FunCall name args) =
  premise
      (reduce name)
      (`FunCall` args)
      (reduceArgs args)

reduceArgs :: (Machine m, Show m, V m ~ Value) => [Term] -> Value -> Env m
reduceArgs args fun = do 
  case args of
    [] -> applyNoArgs fun
    (a : rest) ->
      premise
        (reduce a)
        ( \a' -> FunCall funTerm (a' : rest))
        (checkArgs rest fun)
  where
    funTerm = case fun of
      ClosureVal {} -> Fun [] (Literal 0) -- placeholder, not used
      _ -> Fun [] (Literal 0)

checkArgs :: (Machine m, Show m, V m ~ Value) => [Term] -> Value -> Value -> Env m
checkArgs args fun argVal = do
    res <- applyArgs fun argVal
    case res of 
        Happy v -> case args of 
            [] -> return $ Happy v
            _ -> reduceArgs args v 
        Sad msg -> return $ Sad msg

applyNoArgs :: (Machine m, Show m, V m ~ Value) => Value -> Env m
applyNoArgs (ClosureVal [] body _) = runFunBody body []
applyNoArgs (ClosureVal (_ : _) _ _) = return $ Sad (Arguments, "missing arguments: no arg function requires parameters")
applyNoArgs _ = return $ Sad (Arguments, "attempt to call a non-function")

applyArgs :: (Machine m, Show m, V m ~ Value) => Value -> Value -> Env m
applyArgs (ClosureVal [] _ _) _ = return $ Sad (Arguments, "missing arguments: function requires parameters")
applyArgs (ClosureVal (x : xs) body caps) arg = do
  let newCaps = caps ++ [(x, arg)]
  if null xs
    then runFunBody body newCaps    
    else do
      return $ Happy (ClosureVal xs body newCaps)
applyArgs _ _ = return $ Sad (Type, "attempt to call a non-function")

runFunBody :: (Machine m, Show m, V m ~ Value) => Term -> [(String, Value)] -> Env m
runFunBody body caps = do
    m0 <- S.get -- save the current machine state
    let(_, newScope) = S.runState (addScope []) m0
    case bindMany caps newScope of
        Left msg -> return (Sad msg)
        Right m1 -> do
          let (res, m2) = reduceFully body m1
          let (_, oldScope) = S.runState (deleteScope) m2
          S.put oldScope -- pop the function scope
          case res of
            Left msg -> return $ Sad (Arguments, msg)
            Right v -> return $ Happy v

bindMany :: (Machine m, V m ~ Value) => [(String, Value)] -> m -> Either Error m
bindMany [] m = Right m
bindMany ((k, v) : rest) m =
  case S.runState (setVar k v) m of
    (Sad msg, _m') -> Left msg
    (Continue _, _m') -> Left (Arguments, "internal: setVar requested Continue")
    (Happy _, m') -> bindMany rest m'

reduce :: (Machine m, Show m, V m ~ Value) => Term -> Env m
reduce t = do
  e <- S.get
  trace ("Simulating: " ++ show t) () `seq`
    trace ("     Machine: " ++ show e) () `seq`
      reduce_ t

reduceFully :: (Machine m, Show m, V m ~ Value) => Term -> m -> (Either String (V m), m)
reduceFully term machine =
  case S.runState (reduce term) machine of
    (Sad (_, msg), m) -> (Left msg, m)
    (Continue t, m) -> reduceFully t m
    (Happy n, m) -> (Right n, m)
