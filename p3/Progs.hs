module Progs (prog, prog2, prog3, prog4, 
              -- Basic arithmetic tests
              arithmeticTests,
              -- Boolean logic tests  
              booleanTests,
              -- String tests
              stringTests,
              -- Control flow tests
              controlFlowTests,
              -- Function tests
              functionTests,
              -- Error handling tests
              errorTests,
              -- Complex integration tests
              integrationTests,
              -- Tuple tests
              tupleTests,
              -- Try-catch tests
              tryCatchTests
              
              ) where

import qualified Term as T

-- ============================================================================
-- ORIGINAL TESTS (keeping for backward compatibility)
-- ============================================================================

prog :: T.Term
prog = T.Seq (T.Let "x" (T.Literal 10))
             (T.While (T.BinaryOps T.Gt (T.Var "x") (T.Literal 0))
                      (T.Seq (T.Write (T.Var "x"))
                             (T.Let "x" (T.BinaryOps T.Sub (T.Var "x") (T.Literal 1)))))

prog2 :: T.Term
prog2 = T.Seq (T.Let "inc" (T.Fun ["x"] (T.BinaryOps T.Add (T.Var "x") (T.Literal 1))))
              (T.FunCall (T.Var "inc") [T.Literal 41])

prog3 :: T.Term
prog3 = T.Seq (T.Let "noArgs" (T.Fun [] (T.Write (T.Literal 42))))
              (T.FunCall (T.Var "noArgs") [])

prog4 :: T.Term
prog4 = T.Seq (T.Let "multiArgs" (T.Fun ["x", "y"] (T.BinaryOps T.Mul (T.Var "x") (T.Var "y"))))
              (T.FunCall (T.Var "multiArgs") [T.Literal 3, T.Literal 4])

-- ============================================================================
-- COMPREHENSIVE TEST SUITES
-- ============================================================================

-- Test all arithmetic operations
arithmeticTests :: [(String, T.Term)]
arithmeticTests = 
  [ ("addition", T.BinaryOps T.Add (T.Literal 5) (T.Literal 3))
  , ("subtraction", T.BinaryOps T.Sub (T.Literal 10) (T.Literal 4))
  , ("multiplication", T.BinaryOps T.Mul (T.Literal 6) (T.Literal 7))
  , ("division", T.BinaryOps T.Div (T.Literal 20) (T.Literal 4))
  , ("modulus", T.BinaryOps T.Mod (T.Literal 17) (T.Literal 5))
  , ("negation", T.UnaryOps T.Neg (T.Literal 8))
  , ("complex_expr", T.BinaryOps T.Add 
                     (T.BinaryOps T.Mul (T.Literal 2) (T.Literal 3))
                     (T.BinaryOps T.Div (T.Literal 10) (T.Literal 2)))
  ]

-- Test all boolean operations
booleanTests :: [(String, T.Term)]
booleanTests =
  [ ("and_true", T.BinaryOps T.And (T.BoolLit True) (T.BoolLit True))
  , ("and_false", T.BinaryOps T.And (T.BoolLit True) (T.BoolLit False))
  , ("or_true", T.BinaryOps T.Or (T.BoolLit False) (T.BoolLit True))
  , ("or_false", T.BinaryOps T.Or (T.BoolLit False) (T.BoolLit False))
  , ("not_true", T.UnaryOps T.Not (T.BoolLit True))
  , ("not_false", T.UnaryOps T.Not (T.BoolLit False))
  , ("complex_boolean", T.BinaryOps T.And
                        (T.BinaryOps T.Or (T.BoolLit True) (T.BoolLit False))
                        (T.UnaryOps T.Not (T.BoolLit False)))
  ]

-- Test string operations
stringTests :: [(String, T.Term)]
stringTests =
  [ ("string_literal", T.StringLiteral "hello")
  , ("string_equality", T.BinaryOps T.Eq (T.StringLiteral "hello") (T.StringLiteral "hello"))
  , ("string_inequality", T.BinaryOps T.Neq (T.StringLiteral "hello") (T.StringLiteral "world"))
  , ("string_truthiness", T.If (T.StringLiteral "non-empty") 
                              (T.Write (T.Literal 1)) 
                              (T.Write (T.Literal 0)))
  ]

-- Test control flow
controlFlowTests :: [(String, T.Term)]
controlFlowTests =
  [ ("if_true", T.If (T.BoolLit True) (T.Write (T.Literal 1)) (T.Write (T.Literal 0)))
  , ("if_false", T.If (T.BoolLit False) (T.Write (T.Literal 1)) (T.Write (T.Literal 0)))
  , ("if_numeric", T.If (T.Literal 5) (T.Write (T.Literal 1)) (T.Write (T.Literal 0)))
  , ("while_countdown", T.Seq (T.Let "x" (T.Literal 3))
                              (T.While (T.BinaryOps T.Gt (T.Var "x") (T.Literal 0))
                                       (T.Seq (T.Write (T.Var "x"))
                                              (T.Let "x" (T.BinaryOps T.Sub (T.Var "x") (T.Literal 1))))))
  , ("nested_conditionals", T.If (T.BinaryOps T.Lt (T.Literal 5) (T.Literal 10))
                                 (T.If (T.BinaryOps T.Eq (T.Literal 5) (T.Literal 5))
                                       (T.Write (T.Literal 1))
                                       (T.Write (T.Literal 0)))
                                 (T.Write (T.Literal 2)))
  ]

-- Test function features
functionTests :: [(String, T.Term)]
functionTests =
  [ ("no_args", T.Seq (T.Let "f" (T.Fun [] (T.Write (T.Literal 42))))
                      (T.FunCall (T.Var "f") []))
  , ("single_arg", T.Seq (T.Let "square" (T.Fun ["x"] (T.BinaryOps T.Mul (T.Var "x") (T.Var "x"))))
                          (T.FunCall (T.Var "square") [T.Literal 4]))
  , ("multiple_args", T.Seq (T.Let "add" (T.Fun ["x", "y"] (T.BinaryOps T.Add (T.Var "x") (T.Var "y"))))
                             (T.FunCall (T.Var "add") [T.Literal 3, T.Literal 4]))
  , ("nested_functions", T.Seq (T.Let "outer" (T.Fun ["x"] 
                                               (T.Seq (T.Let "inner" (T.Fun ["y"] (T.BinaryOps T.Add (T.Var "x") (T.Var "y"))))
                                                      (T.FunCall (T.Var "inner") [T.Literal 1]))))
                                (T.FunCall (T.Var "outer") [T.Literal 5]))
  , ("function_composition", T.Seq (T.Let "inc" (T.Fun ["x"] (T.BinaryOps T.Add (T.Var "x") (T.Literal 1))))
                                    (T.Seq (T.Let "double" (T.Fun ["x"] (T.BinaryOps T.Mul (T.Var "x") (T.Literal 2))))
                                           (T.FunCall (T.Var "double") 
                                                     [T.FunCall (T.Var "inc") [T.Literal 3]])))
  ]

-- Test error conditions
errorTests :: [(String, T.Term)]
errorTests =
  [ ("division_by_zero", T.BinaryOps T.Div (T.Literal 10) (T.Literal 0))
  , ("mod_by_zero", T.BinaryOps T.Mod (T.Literal 10) (T.Literal 0))
  , ("type_mismatch_add", T.BinaryOps T.Add (T.Literal 5) (T.BoolLit True))
  , ("type_mismatch_compare", T.BinaryOps T.Lt (T.StringLiteral "hello") (T.Literal 5))
  , ("undefined_variable", T.Var "undefinedVar")
  , ("wrong_arg_count", T.Seq (T.Let "f" (T.Fun ["x"] (T.Var "x")))
                               (T.FunCall (T.Var "f") [T.Literal 1, T.Literal 2]))
  ]

-- Complex integration tests
integrationTests :: [(String, T.Term)]
integrationTests =
  [ ("factorial", T.Seq (T.Let "factorial" (T.Fun ["n"] 
                                            (T.If (T.BinaryOps T.Lte (T.Var "n") (T.Literal 1))
                                                  (T.Literal 1)
                                                  (T.BinaryOps T.Mul (T.Var "n") 
                                                                    (T.FunCall (T.Var "factorial") 
                                                                              [T.BinaryOps T.Sub (T.Var "n") (T.Literal 1)])))))
                        (T.FunCall (T.Var "factorial") [T.Literal 5]))
  , ("fibonacci", T.Seq (T.Let "fib" (T.Fun ["n"]
                                        (T.If (T.BinaryOps T.Lte (T.Var "n") (T.Literal 1))
                                              (T.Var "n")
                                              (T.BinaryOps T.Add 
                                                          (T.FunCall (T.Var "fib") [T.BinaryOps T.Sub (T.Var "n") (T.Literal 1)])
                                                          (T.FunCall (T.Var "fib") [T.BinaryOps T.Sub (T.Var "n") (T.Literal 2)])))))
                        (T.FunCall (T.Var "fib") [T.Literal 6]))
  , ("scope_test", T.Seq (T.Let "x" (T.Literal 10))
                          (T.Seq (T.Let "f" (T.Fun ["x"] (T.BinaryOps T.Mul (T.Var "x") (T.Literal 2))))
                                 (T.Seq (T.Let "x" (T.Literal 5))
                                        (T.FunCall (T.Var "f") [T.Literal 3]))))
  , ("complex_math", T.Seq (T.Let "quadratic" (T.Fun ["a", "b", "c", "x"]
                                                (T.BinaryOps T.Add 
                                                            (T.BinaryOps T.Add 
                                                                        (T.BinaryOps T.Mul (T.Var "a") 
                                                                                          (T.BinaryOps T.Mul (T.Var "x") (T.Var "x")))
                                                                        (T.BinaryOps T.Mul (T.Var "b") (T.Var "x")))
                                                            (T.Var "c"))))
                            (T.FunCall (T.Var "quadratic") [T.Literal 1, T.Literal 2, T.Literal 1, T.Literal 3]))
  ]

-- Tuple tests
tupleTests :: [(String, T.Term)]
tupleTests =
  [ ("new_tuple", T.Let "myTuple" (T.NewTuple [T.Literal 1, T.Literal 2, T.Literal 3]))
  , ("get_tuple", T.GetTuple (T.Var "myTuple") (T.Literal 1))
  , ("set_tuple", T.Seq (T.Let "myTuple" (T.NewTuple [T.Literal 1, T.Literal 2, T.Literal 3])) 
                        (T.SetTuple ("myTuple") (T.Literal 1) (T.Literal 4)))
  , ("set_tuple_out_of_bounds", T.Seq (T.Let "myTuple" (T.NewTuple [T.Literal 1, T.Literal 2, T.Literal 3])) 
                        (T.SetTuple ("myTuple") (T.Literal 4) (T.Literal 4)))
  ]

-- try-catch statement
tryCatchTests :: [(String, T.Term)]
tryCatchTests =
  [ ("try_catch", T.TryCatch (T.Literal 1) (T.Specific T.Arithmetic) (T.Literal 2))
  , ("try_catch_any", T.TryCatch (T.BinaryOps T.Add (T.Literal 1) (T.BoolLit False)) (T.Any) (T.Literal 2))
  , ("try_catch_specific", T.TryCatch (T.Literal 1) (T.Specific T.Type) (T.Literal 2))
  , ("try_catch_specific", T.TryCatch (T.Var "x") (T.Specific T.VariableNotFound) (T.Literal 2))
  ]

-- (Seq 
--   (Seq 
--     (Seq 
--       (Seq 
--         (Seq 
--           (Seq 
--             (Let "x" (Literal 10)) (Write (Var "x"))
--           ) 
--           (Fun [] (Seq (Let "y" (BinaryOps Add (Literal 10) (Literal 5))) (Write (Var "y"))))
--         ) 
--         (FunCall (Var "f") [])
--       ) 
--       (Fun ["a","b","c"] (Write (BinaryOps Add (Var "a") (BinaryOps Add (Var "b") (Var "c")))))
--     ) 
--     (FunCall (Var "multiArgs") [Literal 1,Literal 2,Literal 3])
--   ) (If (BinaryOps Gt (Var "x") (Literal 0)) (Write (Literal 10)) (Write (Literal 20))),[])