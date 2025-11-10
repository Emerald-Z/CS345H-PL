{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Main (main) where
-- module Simulate (Simulator(..), emptyScopeList, getFullScope, insertVar, lookupVar) where

import qualified Control.Monad.State as S
import Control.Monad (forM_)
import qualified Data.Map as M
import qualified Progs
import Small (Env, Error, Machine (..), Result (..), reduceFully)
import Term (Term (..), ErrorKind (..))
import Value (Value (..))
import ScopeList (ScopeList(..), emptyScopeList, getFullScope, insertVar, lookupVar)

data Simulator = Simulator ScopeList [Value] [Value] deriving (Eq, Show)

instance Machine Simulator where
  type V Simulator = Value
  getVar :: String -> Env Simulator
  getVar name = do
    (Simulator m _ _) <- S.get
    case lookupVar name m of
      Just v -> return $ Happy v
      Nothing -> return $ Sad (VariableNotFound, "get: " ++ name ++ " not found")

  setVar :: String -> Value -> Env Simulator
  setVar name val = do
    (Simulator m inp out) <- S.get
    let m' = insertVar name val m
    S.put (Simulator m' inp out)
    return $ Happy val

  -- scoping operations
  getScope :: Simulator -> [(String, Value)]
  getScope (Simulator scope _ _) = getFullScope scope

  addScope :: [(String, Value)] -> Env Simulator
  addScope vars = do
    (Simulator scope input output) <- S.get
    let newScope = ScopeList (M.fromList vars) (Just scope)
    S.put (Simulator newScope input output)
    return $ Happy (IntVal 0)

  deleteScope :: Env Simulator
  deleteScope = do
    (Simulator scope input output) <- S.get
    let parent = case scope of
          ScopeList _ (Just p) -> p
          ScopeList _ Nothing -> emptyScopeList
    S.put (Simulator parent input output)
    return $ Happy (IntVal 0)

  -- tuples
  getValueAtIndex :: Value -> Value -> Env Simulator
  getValueAtIndex (TupleVal ts) (IntVal idx) = 
    let idxInt = fromInteger idx
        tupleLength = length ts
    in if idxInt < 0 || idxInt >= tupleLength
       then return $ Sad (Type, "Index out of bounds: index " ++ show idxInt ++ " is not in range [0, " ++ show (tupleLength - 1) ++ "]")
       else return $ Happy (ts !! idxInt)
  getValueAtIndex _ _ = return $ Sad (Type, "Type error in getValueAtIndex")

  setValueAtIndex :: String -> Integer -> Value -> Env Simulator
  setValueAtIndex name idx v = do
    (Simulator m input output) <- S.get
    case lookupVar name m of 
      Just (TupleVal ts) -> 
        let idxInt = fromInteger idx
            tupleLength = length ts
        in if idxInt < 0 || idxInt >= tupleLength
           then return $ Sad (Type, "Index out of bounds: index " ++ show idxInt ++ " is not in range [0, " ++ show (tupleLength - 1) ++ "]")
           else do
             -- update tuple and insert into scope/map
             case updateTuple (TupleVal ts) idxInt v of
               Just newTuple' -> do
                 let m' = insertVar name newTuple' m
                 S.put (Simulator m' input output)
                 return $ Happy v
               Nothing -> return $ Sad (Type, "Something went wrong while trying to update Tuple value")
      Just _ -> return $ Sad (Type, "Type error in setValueAtIndex")
      Nothing -> return $ Sad (VariableNotFound, "Tuple not found")
    where 
      updateTuple :: Value -> Int -> Value -> Maybe Value
      updateTuple (TupleVal (_ : xs)) 0 val = Just (TupleVal (val : xs))
      updateTuple (TupleVal (x : xs)) idx val = case updateTuple (TupleVal xs) (idx - 1) val of
        Just xs' -> 
          case xs' of
            TupleVal xs'' -> Just (TupleVal (x : xs''))
            _ -> Nothing
        Nothing -> Nothing
      updateTuple (TupleVal []) _ _ = Nothing
      updateTuple _ _ _ = Nothing

  -- setValueAtIndex _ _ _ = return $ Sad "Type error in setValueAtIndex"

  inputVal :: Env Simulator
  inputVal = do
    (Simulator m inp out) <- S.get
    case inp of
      (x : xs) -> do
        S.put (Simulator m xs out)
        return $ Happy x
      [] -> return $ Sad (Input, "Input stream is empty")

  outputVal :: Value -> Env Simulator
  outputVal val = do
    (Simulator m inp out) <- S.get
    let out' = out ++ [val]
    S.put (Simulator m inp out')
    return $ Happy val

  subVal :: Value -> Value -> Env Simulator
  subVal (IntVal v1) (IntVal v2) = return $ Happy (IntVal (v1 - v2))
  subVal _ _ = return $ Sad (Type, "Type error in subtraction")

  addVal :: Value -> Value -> Env Simulator
  addVal (IntVal v1) (IntVal v2) = return $ Happy (IntVal (v1 + v2))
  addVal _ _ = return $ Sad (Type, "Type error in addition")

  mulVal :: Value -> Value -> Env Simulator
  mulVal (IntVal v1) (IntVal v2) = return $ Happy (IntVal (v1 * v2))
  mulVal _ _ = return $ Sad (Type, "Type error in multiplication")

  divVal :: Value -> Value -> Env Simulator
  divVal (IntVal v1) (IntVal v2) =
    if v2 == 0
      then return $ Sad (Arithmetic, "Cannot divide by 0")
      else return $ Happy (IntVal (v1 `div` v2)) -- I don't want the actual interpreter to crash
  divVal _ _ = return $ Sad (Type, "Type error in division")

  modVal :: Value -> Value -> Env Simulator
  modVal (IntVal v1) (IntVal v2) =
    if v2 == 0
      then return $ Sad (Arithmetic, "Cannot mod by 0")
      else return $ Happy (IntVal (v1 `mod` v2)) -- I don't want the actual interpreter to crash
  modVal _ _ = return $ Sad (Type, "Type error in modulus")

  negVal (IntVal v) = return $ Happy (IntVal (-v))
  negVal _ = return $ Sad (Type, "Type error in neg")

  selectValue :: Value -> Env Simulator -> Env Simulator -> Env Simulator
  selectValue (BoolVal True) e1 _ = e1
  selectValue (BoolVal False) _ e2 = e2
  selectValue (IntVal n) e1 e2 = if n /= 0 then e1 else e2 -- backward compat
  selectValue (StringVal s) e1 e2 = if not (null s) then e1 else e2
  selectValue (ClosureVal {}) _ _ = return $ Sad (Type, "Type error in select")

  ltVal :: Value -> Value -> Env Simulator
  ltVal (IntVal v1) (IntVal v2) = return $ Happy (BoolVal (v1 < v2))
  ltVal _ _ = return $ Sad (Type, "Type error in <")

  gtVal :: Value -> Value -> Env Simulator
  gtVal (IntVal v1) (IntVal v2) = return $ Happy (BoolVal (v1 > v2))
  gtVal _ _ = return $ Sad (Type, "Type error in >")

  lteVal :: Value -> Value -> Env Simulator
  lteVal (IntVal v1) (IntVal v2) = return $ Happy (BoolVal (v1 <= v2))
  lteVal _ _ = return $ Sad (Type, "Type error in <=")

  gteVal :: Value -> Value -> Env Simulator
  gteVal (IntVal v1) (IntVal v2) = return $ Happy (BoolVal (v1 >= v2))
  gteVal _ _ = return $ Sad (Type, "Type error in >=")    

  eqVal :: Value -> Value -> Env Simulator
  eqVal (IntVal v1) (IntVal v2) = return $ Happy (BoolVal (v1 == v2))
  eqVal (BoolVal v1) (BoolVal v2) = return $ Happy (BoolVal (v1 == v2))
  eqVal (StringVal v1) (StringVal v2) = return $ Happy (BoolVal (v1 == v2))
  eqVal v1 v2 = return $ Sad (Type, "Type error in ==: cannot compare " ++ show v1 ++ " and " ++ show v2)

  neqVal :: Value -> Value -> Env Simulator
  neqVal (IntVal v1) (IntVal v2) = return $ Happy (BoolVal (v1 /= v2))
  neqVal (BoolVal v1) (BoolVal v2) = return $ Happy (BoolVal (v1 /= v2))
  neqVal (StringVal v1) (StringVal v2) = return $ Happy (BoolVal (v1 /= v2))
  neqVal v1 v2 = return $ Sad (Type, "Type error in !=: cannot compare " ++ show v1 ++ " and " ++ show v2)

  andVal :: Value -> Value -> Env Simulator
  andVal (BoolVal v1) (BoolVal v2) = return $ Happy (BoolVal (v1 && v2))
  andVal _ _ = return $ Sad (Type, "Type error in &&")

  orVal :: Value -> Value -> Env Simulator
  orVal (BoolVal v1) (BoolVal v2) = return $ Happy (BoolVal (v1 || v2))
  orVal _ _ = return $ Sad (Type, "Type error in ||")

  notVal :: Value -> Env Simulator
  notVal (BoolVal v) = return $ Happy (BoolVal (not v))
  notVal _ = return $ Sad (Type, "Type error in !")

infixl 1 ~

(~) :: Term -> Term -> Term
(~) = Seq

infixl 9 <=>

(<=>) :: String -> Term -> Term
(<=>) = Let

prog :: Term
prog =
  "x" <=> Literal 10
    ~ "y" <=> Literal 29
    ~ "z" <=> Literal 3

main :: IO ()
main = do
  let out = reduceFully prog (Simulator emptyScopeList [] [])
  print out
  putStrLn "-----------------------------"
  let out2 = reduceFully Progs.prog2 (Simulator emptyScopeList [] [])
  print out2
  putStrLn "-----------------------------"
  putStrLn "Testing booleans and comparisons:"
  let out3 = reduceFully Progs.prog3 (Simulator emptyScopeList [] [])
  print out3
  putStrLn "-----------------------------"
  putStrLn "Testing tuples:"
  forM_ Progs.tupleTests (\(name, tupleProg) -> do
    putStrLn $ "Testing " ++ name
    let out = reduceFully tupleProg (Simulator emptyScopeList [] [])
    print out
    )
  putStrLn "-----------------------------"
  putStrLn "Testing try-catch:"
  forM_ Progs.tryCatchTests (\(name, tryCatchProg) -> do
    putStrLn $ "Testing " ++ name
    let out = reduceFully tryCatchProg (Simulator emptyScopeList [] [])
    print out
    )
