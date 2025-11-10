module Main where

import Parser (parse, prog)
import ParserCombinators (eof)
import Small (reduceFully)
-- import Simulate (Simulator(..), emptyScopeList)

main :: IO ()
main = do
    text <- getContents
    let r = parse text $ do
            t <- prog
            _ <- eof
            return t
    print r
--     case r of
--         Left err -> putStrLn $ "Parse error: " ++ err
--         Right (term, _) -> do
--             putStrLn "Parsed AST:"
--             print term
--             putStrLn "\nRunning simulation:"
--             let (result, finalState) = reduceFully term (Simulator emptyScopeList [] [])
--             case result of
--                 Left err -> putStrLn $ "Runtime error: " ++ err
--                 Right val -> do
--                     putStrLn $ "Result: " ++ show val
--                     putStrLn $ "Output: " ++ show (output finalState)
--   where
--     output (Simulator _ _ out) = out
            
