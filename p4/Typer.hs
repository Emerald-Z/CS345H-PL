{-# LANGUAGE DataKinds #-}

module Typer (typer) where

import Data.Functor.Foldable (para)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M
-- import Debug.Trace (trace)
import Sprintf (sprintf)
import System.IO (Handle, hPutStrLn)
import Term (BinaryOp (..), Term (..), TermF (..), UnaryOp (..))
import TypeSignature (TypeSignature (..))

-- Type context maps variable names to their types
type TypeContext = M.Map String TypeSignature
-- TypeReader: a function that takes an environment and returns either an error or a type
type TypeReader = TypeContext -> Either String TypeSignature -- TODO: replace string with error types

-- Union type vs. Sum type
combine :: TypeSignature -> TypeSignature -> TypeSignature
combine TUnknown _ = TUnknown
combine _ TUnknown = TUnknown
combine t1 t2 | t1 == t2 = t1 -- this makes a union type, Python semantics
combine t1 t2 = TSum [t1, t2]

-- Normalize sum types by removing placeholder Poly "unknown_ret" when concrete types are present
normalizeSumType :: TypeSignature -> TypeSignature
normalizeSumType (TSum types) =
  let
      concreteTypes = filter (\t -> case t of Poly "unknown_ret" -> False; _ -> True) types
      hasConcreteTypes = not (null concreteTypes)
      normalizedTypes = if hasConcreteTypes then concreteTypes else types
      -- If all types are the same after normalization, collapse to a single type
      uniqueTypes = foldr (\t acc -> if t `elem` acc then acc else t : acc) [] normalizedTypes
  in case uniqueTypes of
       [singleType] -> singleType
       _ -> TSum normalizedTypes
normalizeSumType (TFun paramTypes retType) = TFun paramTypes (normalizeSumType retType)
normalizeSumType (TTuple types) = TTuple (map normalizeSumType types)
normalizeSumType (TDictionary valType) = TDictionary (normalizeSumType valType)
normalizeSumType t = t

-- Substitute type variables in a type signature
substituteType :: String -> TypeSignature -> TypeSignature -> TypeSignature
substituteType varName replacement = go
  where
    go (Poly name) | name == varName = replacement
    go (Poly name) = Poly name
    go (TFun paramTypes retType) = TFun (map go paramTypes) (go retType)
    go (TSum types) = TSum (map go types)
    go (TTuple types) = TTuple (map go types)
    go (TDictionary valType) = TDictionary (go valType)
    go t = t

-- Type compatibility helpers (shared across binary ops, unary ops, and function application)
isIntCompatible :: TypeSignature -> Bool
isIntCompatible TInt = True
isIntCompatible (TLiteralInt _) = True
isIntCompatible (TSum ts) = all (\t -> case t of TInt -> True; TLiteralInt _ -> True; _ -> False) ts
isIntCompatible _ = False

isStringCompatible :: TypeSignature -> Bool
isStringCompatible TString = True
isStringCompatible (TLiteralString _) = True
isStringCompatible (TSum ts) = all (\t -> case t of TString -> True; TLiteralString _ -> True; _ -> False) ts
isStringCompatible _ = False

isBoolCompatible :: TypeSignature -> Bool
isBoolCompatible TBool = True
isBoolCompatible (TLiteralBool _) = True
isBoolCompatible (TSum ts) = all (\t -> case t of TBool -> True; TLiteralBool _ -> True; _ -> False) ts
isBoolCompatible _ = False

-- Bool compatible that also allows ints (for binary operations where ints can be truthy/falsy)
isBoolCompatibleWithInt :: TypeSignature -> Bool
isBoolCompatibleWithInt t = isBoolCompatible t || isIntCompatible t

-- (-->) :: Bool -> TypeSignature -> TypeSignature
-- (-->) True t = t
-- (-->) False _ = TUnknown

-- Pure type checker using TypeReader pattern
typerPure :: Term -> Either String TypeSignature
typerPure term = (para go term) M.empty
  where
    go :: TermF (Term, TypeReader) -> TypeReader
    -- Literals don't need environment
    go (LiteralF _) = \_ -> Right TInt
    go (BoolLitF _) = \_ -> Right TBool
    go (StringLiteralF _) = \_ -> Right TString

    -- Variables look up in environment, fallback to annotation
    go (OnlyStrF (name, annotatedType)) = \env ->
      Right $ if annotatedType == TUnknown
        then fromMaybe TUnknown (M.lookup name env)
        else annotatedType
    go (VarF (_, innerReader)) = innerReader

    -- Let bindings: type the RHS and check it matches the LHS annotation
    -- variable isn't needed yet so just type the rhs
    go (LetF (varTerm, varReader) (rhsTerm, rhsReader)) = \env -> do
      -- original annotation if exists
      let originalAnnotation = case varTerm of
            OnlyStr (_, annot) -> annot
            _ -> TUnknown
      -- Get the variable's type (annotation if present, otherwise from environment)
      varType <- varReader env
      rhsType <- rhsReader env

      if originalAnnotation == TUnknown
        then Right rhsType
        else
          if varType == rhsType
            then Right rhsType
            else 
            case (varType, rhsType) of
              (TLiteralInt _, TInt) -> Right rhsType
              (TLiteralString _, TString) -> Right rhsType
              (TLiteralBool _, TBool) -> Right rhsType
              (Poly "string", TString) -> Right rhsType
              (TSum ts1, TSum ts2) -> --TODO: is this robust?
                -- Both are sum types: check if they contain the same set of types (order-independent)
                let -- Check if every type in ts1 is in ts2 and vice versa
                    allIn ts1' ts2' = all (\t1 -> any (== t1) ts2') ts1'
                in if allIn ts1 ts2 && allIn ts2 ts1
                  then Right rhsType
                  else Left (sprintf "Let binding type mismatch (sum type): %s vs %s" [show varType, show rhsType])
              (TSum ts, _) -> 
                -- Check if RHS type matches any type in the sum
                -- first check equality
                if any (== rhsType) ts 
                  then Right rhsType
                  else
                    -- Check if RHS is a literal and varType is a sum of literal types
                    case rhsTerm of
                      StringLiteral s -> 
                        if any (\t -> case t of 
                              TLiteralString s' -> s == s'
                              Poly "string" -> True
                              TString -> True
                              _ -> False) ts
                          then Right rhsType
                          else Left (sprintf "Let binding type mismatch (sum type): %s vs %s" [show varType, show rhsType])
                      Literal n ->
                        if any (\t -> case t of 
                              TLiteralInt n' -> n == n'
                              Poly _ -> True
                              TInt -> True
                              _ -> False) ts
                          then Right rhsType
                          else Left (sprintf "Let binding type mismatch (sum type): %s vs %s" [show varType, show rhsType])
                      BoolLit b ->
                        if any (\t -> case t of 
                              TLiteralBool b' -> b == b'
                              Poly "bool" -> True
                              TBool -> True
                              _ -> False) ts
                          then Right rhsType
                          else Left (sprintf "Let binding type mismatch (sum type): %s vs %s" [show varType, show rhsType])
                      _ -> Left (sprintf "Let binding type mismatch (sum type): %s vs %s" [show varType, show rhsType])
              -- TODO: Function type compatibility: check parameter types match, return type can be TUnknown in annotation
              (TFun paramTypes1 retType1, TFun paramTypes2 retType2)
                | paramTypes1 == paramTypes2 ->
                    if retType1 == TUnknown || retType1 == retType2
                      then Right rhsType
                      else Left (sprintf "Let binding type mismatch (function type): return type %s vs %s" [show retType1, show retType2])
                | otherwise -> Left (sprintf "Let binding type mismatch (function type): parameter types %s vs %s" [show paramTypes1, show paramTypes2])
              (lhsType, Poly _) -> Right lhsType -- TODO: should it still be rhstype if you are assigning type poly to a strict variable
              _ ->
                if varType == TUnknown || varType == rhsType
                  then Right rhsType
                  else Left (sprintf "Let binding type mismatch: %s vs %s" [show varType, show rhsType])

    -- Binary operations
    go (BinaryOpsF op (t1Term, t1Reader) (t2Term, t2Reader)) = \env -> do
      t1Type <- t1Reader env
      t2Type <- t2Reader env
      let both t = t1Type == t && t2Type == t
          -- Check if a type is a type variable (Poly) or TUnknown
          isTypeVar (Poly _) = True
          isTypeVar TUnknown = True
          isTypeVar _ = False
          -- If either operand is a type variable, allow the operation (type checking happens at call site)
          hasTypeVar = isTypeVar t1Type || isTypeVar t2Type
          -- Check if both operands are int-compatible
          bothInt = isIntCompatible t1Type && isIntCompatible t2Type
          -- check if both operands are boolean-compatible (including ints for truthy/falsy)
          bothBool = isBoolCompatibleWithInt t1Type && isBoolCompatibleWithInt t2Type
          -- Check if both operands are string-compatible
          bothString = isStringCompatible t1Type && isStringCompatible t2Type
          -- Check if one operand is string and the other is int
          stringAndInt = (isStringCompatible t1Type && isIntCompatible t2Type) || 
                        (isIntCompatible t1Type && isStringCompatible t2Type)
      case op of
        -- Addition: int + int = int, string + string = string
        Add | both TInt -> Right TInt
        Add | bothInt -> Right TInt
        Add | both TString -> Right TString
        Add | bothString -> Right TString
        Add | hasTypeVar -> Right TInt  -- Allow if type variable present, assume int at call site
        Sub | both TInt -> Right TInt
        Sub | bothInt -> Right TInt
        Sub | hasTypeVar -> Right TInt
        -- Multiplication: int * int = int, string * int = string, int * string = string
        Mul | both TInt -> Right TInt
        Mul | bothInt -> Right TInt
        Mul | stringAndInt -> Right TString  -- String * Int or Int * String = String (repetition)
        Mul | hasTypeVar -> Right TInt
        Div | both TInt -> Right TInt
        Div | bothInt -> Right TInt
        Div | hasTypeVar -> Right TInt
        Div | bothBool -> Right TBool
        Mod | both TInt -> Right TInt
        Mod | bothInt -> Right TInt
        Mod | hasTypeVar -> Right TInt
        Lt | both TInt -> Right TBool
        Lt | bothInt -> Right TBool
        Lt | hasTypeVar -> Right TBool
        Lt -> case (t1Term, t2Term) of
          (Literal _, Literal _) -> Right TBool  -- Constant folding: will be evaluated at runtime
          _ -> Right TBool
        Gt | both TInt -> Right TBool
        Gt | bothInt -> Right TBool
        Gt | hasTypeVar -> Right TBool
        Gt -> case (t1Term, t2Term) of
          (Literal _, Literal _) -> Right TBool  -- Constant folding: will be evaluated at runtime
          _ -> Right TBool
        Lte | both TInt -> Right TBool
        Lte | bothInt -> Right TBool
        Lte | hasTypeVar -> Right TBool
        Lte -> case (t1Term, t2Term) of
          (Literal _, Literal _) -> Right TBool
          _ -> Right TBool
        Gte | both TInt -> Right TBool
        Gte | bothInt -> Right TBool
        Gte | hasTypeVar -> Right TBool
        Gte -> case (t1Term, t2Term) of
          (Literal _, Literal _) -> Right TBool
          _ -> Right TBool
        Eq | t1Type == t2Type -> Right TBool
        Eq | hasTypeVar -> Right TBool  -- Allow equality with type variables
        Neq | t1Type == t2Type -> Right TBool
        Neq | hasTypeVar -> Right TBool
        And | both TBool -> Right TBool
        And | hasTypeVar -> Right TBool
        Or | both TBool -> Right TBool
        Or | hasTypeVar -> Right TBool
        Pow | both TInt -> Right TInt
        Pow | bothInt -> Right TInt
        Pow | hasTypeVar -> Right TInt
        Xor | both TBool -> Right TBool
        Xor | hasTypeVar -> Right TBool
        _ -> Left (sprintf "Type error in binary operation %s: %s vs %s" [show op, show t1Type, show t2Type])
    
    -- Unary operations
    go (UnaryOpsF op (_, tReader)) = \env -> do
      tType <- tReader env
      let isTypeVar (Poly _) = True
          isTypeVar TUnknown = True
          isTypeVar _ = False
          hasTypeVar = isTypeVar tType
      case op of
        Not | tType == TBool -> Right TBool
        Not | hasTypeVar -> Right TBool  -- Allow if type variable present
        Neg | tType == TInt -> Right TInt
        Neg | isIntCompatible tType -> Right TInt
        Neg | hasTypeVar -> Right TInt
        BitNot | tType == TInt -> Right TInt
        BitNot | isIntCompatible tType -> Right TInt
        BitNot | hasTypeVar -> Right TInt
        _ -> Left (sprintf "Type error in unary operation %s: %s" [show op, show tType])
  
      -- go (SeqF (t1, t1Reader) (_, t2Reader)) = \env -> do
      -- -- First, type check t1 to ensure it's valid and get its type
      -- t1Type <- t1Reader env
      -- -- Then extract the binding if it's a Let
      -- -- The type of a Let binding is the type of its RHS
          --     Let (OnlyStr (name, _)) _ ->
          -- M.insert name t1Type env
    -- TODO: is this right
    go (SeqF (t1, t1Reader) (_, t2Reader)) = \env -> do
      t1Type <- t1Reader env
      let env' = case t1 of
            Let (OnlyStr (name, _)) _ ->
              M.insert name t1Type env
            _ -> env
      t2Reader env'

    go (IfF (condTerm, condReader) (_, thenReader) (_, elseReader)) = \env -> do
      condType <- condReader env
      thenType <- thenReader env
      elseType <- elseReader env
      let isPoly (Poly _) = True
          isPoly _ = False
          -- Allow bool, int (0 = false, non-zero = true), and poly types as conditions
          isAllowedCondition TBool = True
          isAllowedCondition TInt = True
          isAllowedCondition (TLiteralInt _) = True
          isAllowedCondition t = isPoly t
      if isAllowedCondition condType
        then
          -- Constant folding: if condition is a constant boolean or integer, return only that branch
          case condTerm of
            BoolLit True -> Right thenType  -- Condition is always true
            BoolLit False -> Right elseType -- Condition is always false
            Literal 0 -> Right elseType     -- 0 is falsy
            Literal _ -> Right thenType     -- Non-zero integer is truthy
            -- condition is a variable - check if it exists in the environment
            Var varName -> 
              case varName of
                OnlyStr (name, _) -> case M.lookup name env of
                  Just varType -> if varType == TBool
                    then Right thenType
                    else Right elseType
                  Nothing -> Right (combine thenType elseType)
                _ -> Right (combine thenType elseType)
            _ -> Right (combine thenType elseType) -- Unknown condition, combine both types
        else Left (sprintf "Condition must be bool or int, got %s" [show condType])
  
    go (WriteF (_, tReader)) = tReader
    go (WhileF (_, condReader) (_, bodyReader) _ _) = \env -> do
      condType <- condReader env
      bodyType <- bodyReader env
      let isPoly (Poly _) = True
          isPoly _ = False
          -- Allow bool, int (0 = false, non-zero = true), and poly types as conditions
          isAllowedCondition TBool = True
          isAllowedCondition TInt = True
          isAllowedCondition (TLiteralInt _) = True
          isAllowedCondition t = isPoly t
      if isAllowedCondition condType
        then Right (combine TUnit bodyType)
        else Left (sprintf "While condition must be bool or int, got %s" [show condType])

    -- Tuple creation: type each element and return TTuple
    go (TupleTermF elemReaders) = \env -> do
      elemTypes <- traverse (\(_, reader) -> reader env) elemReaders
      Right (TTuple elemTypes)
    
    -- Tuple/indexing: type the base and index, return the element type at that index
    go (BracketF (_, baseReader) (indexTerm, indexReader)) = \env -> do
      baseType <- baseReader env
      indexType <- indexReader env
      -- Check that index is an integer
      let isIntType TInt = True
          isIntType (TLiteralInt _) = True
          isIntType _ = False
      if isIntType indexType
        then
          case baseType of
            TTuple types -> 
              if null types
                then Left "Cannot index empty tuple"
                else
                  -- Try to get constant index if possible
                  case indexTerm of
                    Literal n ->
                      -- Constant index: return the specific type at that index
                      if n >= 0 && n < fromIntegral (length types)
                        then Right (types !! fromIntegral n)
                        else Left (sprintf "Tuple index %s out of bounds (tuple has %s elements)" [show n, show (length types)])
                    _ ->
                      -- Non-constant index: return sum of all possible types
                      Right (TSum types)
            TSum types ->
              -- Indexing into a sum type: index each type in the sum and combine results
              let indexEachType t = case t of
                    TTuple tupleTypes ->
                      case indexTerm of
                        Literal n ->
                          if n >= 0 && n < fromIntegral (length tupleTypes)
                            then Right (tupleTypes !! fromIntegral n)
                            else Left (sprintf "Tuple index %s out of bounds" [show n])
                        _ ->
                          Right (TSum tupleTypes)
                    TDictionary _ -> Right TUnknown
                    TUnknown -> Right TUnknown
                    Poly _ -> Right TUnknown
                    _ -> Left (sprintf "Cannot index type %s in sum type" [show t])
              in do
                indexedTypes <- traverse indexEachType types
                -- Combine all indexed types into a sum
                Right (foldr combine TUnknown indexedTypes)
            TDictionary _ -> Right TUnknown -- Dictionary indexing returns unknown type
            TUnknown -> Right TUnknown -- Unknown base type
            Poly _ -> Right TUnknown -- Polymorphic base type
            _ -> Left (sprintf "Cannot index type %s" [show baseType])
        else Left (sprintf "Index must be int, got %s" [show indexType])
    -- TODO: do those need to be AST nodes? Why a string?
    go (PreIncrementF _) = \_ -> Right TInt
    go (PreDecrementF _) = \_ -> Right TInt
    go (PostIncrementF _) = \_ -> Right TInt
    go (PostDecrementF _) = \_ -> Right TInt
    -- TODO: exception types
    go (TryF (_, tryReader) _ (_, catchReader)) = \env -> do
      tryType <- tryReader env
      catchType <- catchReader env
      Right (combine tryType catchType)
    -- TODO: why int?
    go (ReadF _) = \_ -> Right TInt
    -- TODO: handle arg count and types
    go (FunF args (_, bodyReader)) = \env -> do
      let paramTypes = snd <$> args
          paramBindings = M.fromList args
          env' = M.union paramBindings env
      bodyType <- bodyReader env'
      -- Normalize the body type to remove placeholder Poly "unknown_ret" from sum types
      let normalizedBodyType = normalizeSumType bodyType
      Right (TFun paramTypes normalizedBodyType)

    -- Function application: type check arguments against parameter types
    -- Handle type variable instantiation at call site
    -- Support partial application: if fewer args than params, return a function type
    go (ApplyFunF (firstTerm, funReader) argReaders) = \env -> do
      funType <- funReader env
      argTypes <- traverse (\(_, reader) -> reader env) argReaders
      let argTerms = fst <$> argReaders
          -- Helper functions for type checking (shared between partial and full application)
          isTypeVar (Poly _) = True
          isTypeVar TUnknown = True
          isTypeVar _ = False
          -- Check argument type against parameter type
          checkArgType ((paramType, argType), argTerm) =
            if paramType == argType || isTypeVar paramType
              then Right ()
              else
                -- Check if paramType is a sum of literal types and argType is the base type
                case (paramType, argTerm) of
                  (TSum ts, StringLiteral s) ->
                    -- Check if any literal string in the sum matches
                    if any (\t -> case t of TLiteralString s' -> s == s'; _ -> False) ts
                      then Right ()
                      else Left (sprintf "Type mismatch: expected %s, got %s" [show paramType, show argType])
                  (TSum ts, Literal n) ->
                    -- Check if any literal int in the sum matches
                    if any (\t -> case t of TLiteralInt n' -> n == n'; _ -> False) ts
                      then Right ()
                      else Left (sprintf "Type mismatch: expected %s, got %s" [show paramType, show argType])
                  (TSum ts, BoolLit b) ->
                    -- Check if any literal bool in the sum matches
                    if any (\t -> case t of TLiteralBool b' -> b == b'; _ -> False) ts
                      then Right ()
                      else Left (sprintf "Type mismatch: expected %s, got %s" [show paramType, show argType])
                  (TLiteralInt n, _) ->
                    -- Parameter is literal int n: check if argument matches
                    case argTerm of
                      Literal m ->
                        -- Argument is a literal: check if values match
                        if n == m
                          then Right ()
                          else Left (sprintf "Type mismatch: expected literal %s, got literal %s" [show n, show m])
                      _ ->
                        -- Argument is not a literal: only allow if it's TInt and we can't verify the value
                        if argType == TInt
                          then Right ()  -- Allow TInt to be passed to literal parameter (runtime check)
                          else Left (sprintf "Type mismatch: expected literal %s, got %s" [show n, show argType])
                  (TLiteralString s, _) ->
                    -- Parameter is literal string s: check if argument matches
                    case argTerm of
                      StringLiteral t ->
                        -- Argument is a literal: check if values match
                        if s == t
                          then Right ()
                          else Left (sprintf "Type mismatch: expected literal string %s, got literal string %s" [show s, show t])
                      _ ->
                        -- Argument is not a literal: only allow if it's TString
                        if argType == TString
                          then Right ()  -- Allow TString to be passed to literal parameter (runtime check)
                          else Left (sprintf "Type mismatch: expected literal string %s, got %s" [show s, show argType])
                  (TLiteralBool b, _) ->
                    -- Parameter is literal bool b: check if argument matches
                    case argTerm of
                      BoolLit c ->
                        -- Argument is a literal: check if values match
                        if b == c
                          then Right ()
                          else Left (sprintf "Type mismatch: expected literal bool %s, got literal bool %s" [show b, show c])
                      _ ->
                        -- Argument is not a literal: only allow if it's TBool
                        if argType == TBool
                          then Right ()  -- Allow TBool to be passed to literal parameter (runtime check)
                          else Left (sprintf "Type mismatch: expected literal bool %s, got %s" [show b, show argType])
                  (TInt, _) ->
                    -- Parameter is TInt: allow int-compatible types (including literal ints)
                    if isIntCompatible argType
                      then Right ()
                      else Left (sprintf "Type mismatch: expected %s, got %s" [show paramType, show argType])
                  (TString, _) ->
                    -- Parameter is TString: allow string-compatible types (including literal strings)
                    if isStringCompatible argType
                      then Right ()
                      else Left (sprintf "Type mismatch: expected %s, got %s" [show paramType, show argType])
                  (TBool, _) ->
                    -- Parameter is TBool: allow bool-compatible types (including literal bools)
                    if isBoolCompatible argType
                      then Right ()
                      else Left (sprintf "Type mismatch: expected %s, got %s" [show paramType, show argType])
                  _ -> Left (sprintf "Type mismatch: expected %s, got %s" [show paramType, show argType])
      case funType of
        TFun paramTypes retType
          | length argTypes > length paramTypes -> Left (sprintf "Arity mismatch (%s): expected %s args, got %s" [show firstTerm, show (length paramTypes), show (length argTypes)])
          | length argTypes < length paramTypes -> do
              -- Partial application: check provided args and return function with remaining params
              -- check arg types
              _ <- traverse checkArgType (zip (zip paramTypes argTypes) argTerms)
              
              -- Instantiate polymorphic return type with argument types (for remaining params)
              let instantiatedRetType = foldl (\ret (paramType, argType) ->
                    case paramType of
                      Poly varName -> substituteType varName argType ret
                      _ -> ret) retType (zip paramTypes argTypes)
              
              -- Return function type with remaining parameters
              let remainingParams = drop (length argTypes) paramTypes
              Right (TFun remainingParams instantiatedRetType)
          | otherwise -> do
              -- Full application: check all arg types and return result type
              -- check arg types (using shared checkArgType function defined above)
              _ <- traverse checkArgType (zip (zip paramTypes argTypes) argTerms)
              
              -- Instantiate polymorphic return type with argument types
              let instantiatedRetType = foldl (\ret (paramType, argType) ->
                    case paramType of
                      Poly varName -> substituteType varName argType ret
                      _ -> ret) retType (zip paramTypes argTypes)
              
              Right instantiatedRetType
        -- TODO: this has to be checked Allow polymorphic parameters to be called as functions
        -- don't know the function signature, we can't check argument types
        -- return a fresh Poly type variable for the return type to preserve type information
        Poly name -> Right (Poly (name ++ "_ret"))
        -- Also allow TUnknown to be called???
        TUnknown -> Right (Poly "unknown_ret")
        _ -> Left (sprintf "Not a function: %s, got %s" [show funType, show firstTerm])
    -- Block just returns the type of its inner term
    go (BlockF (_, bodyReader)) = bodyReader
    -- TODO: The issue was that literals were wrapped in Block nodes, and there was no BlockF case, so it fell through to the catch-all and returned TUnknown. Adding the BlockF case fixed it.
    -- Skip represents no-op statements
    go SkipF = \_ -> Right TUnit
    -- TODO: complete other cases
    go _ = \_ -> Right TUnknown

-- Wrapper with debug output
typer :: Handle -> Term -> IO (Either String TypeSignature)
typer debugFile term = do
  _ <- hPutStrLn debugFile "Starting typer"
  let result = typerPure term
  case result of
    Left err -> do
      _ <- hPutStrLn debugFile ("Type error: " ++ err)
      return result
    Right tSig -> do
      _ <- hPutStrLn debugFile ("Type: " ++ show tSig)
      return result
