module ScopeList (ScopeList(..), emptyScopeList, getFullScope, insertVar, lookupVar) where

import qualified Data.Map as M
import Value (Value)

-- current scope, parent scope
data ScopeList = ScopeList (M.Map String Value) (Maybe ScopeList) deriving (Eq, Show)

lookupVar :: String -> ScopeList -> Maybe Value -- pass in parent pointer
lookupVar name (ScopeList m parent) = 
    case M.lookup name m of 
        Just v -> Just v
        Nothing -> case parent of
            Just p -> lookupVar name p
            Nothing -> Nothing

insertVar :: String -> Value -> ScopeList -> ScopeList
insertVar name val (ScopeList m parent) = ScopeList (M.insert name val m) parent

getFullScope :: ScopeList -> [(String, Value)]
getFullScope (ScopeList m parent) = 
    case parent of
        Just p -> getFullScope p ++ M.toList m
        Nothing -> M.toList m

emptyScopeList :: ScopeList
emptyScopeList = ScopeList M.empty Nothing