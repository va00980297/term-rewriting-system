module Term where

import Data.List (intercalate)

------------------------------------------------------------
-- Term in first-order logic.
--
-- Variables are represented by strings.
-- Function terms consist of:
--   * a function symbol name
--   * its arity
--   * a list of argument terms
--
-- Constants are represented as functions with zero arguments.
-- For example, the constant `a` is:
--
--   Func { funcName = "a", funcArity = 0, funcArgs = [] }
------------------------------------------------------------

data Term
  = Var String
  | Func
      { funcName :: String,
        funcArity :: Int,
        funcArgs :: [Term]
      }
  deriving (Eq, Ord, Read)

------------------------------------------------------------
-- A set of equations to be unified.
--
-- Used in module Unify
--
-- Each pair represents an equation:
--
--   t1 ≐ t2
------------------------------------------------------------

type EqSet = [(Term, Term)]

------------------------------------------------------------
-- A set of substitutions found.
--
-- Used in module Match
--
-- Each pair represents an Matching:
--
-- p matches t
------------------------------------------------------------
type Sub = [(Term, Term)]

type Context = Term -> Term

------------------------------------------------------------
-- Smart constructor for function terms.
--
-- Ensures that the declared arity matches the number of
-- provided arguments.
--
-- External modules should construct function terms using
-- `mkFunc` instead of directly creating invalid Func values.
------------------------------------------------------------

mkFunc :: String -> Int -> [Term] -> Term
mkFunc name arity args
  | arity == length args =
      Func
        { funcName = name,
          funcArity = arity,
          funcArgs = args
        }
  | otherwise =
      error $
        "Function "
          ++ name
          ++ " expects "
          ++ show arity
          ++ " arguments, but got "
          ++ show (length args)

------------------------------------------------------------
-- Pretty printing for terms.
--
-- Variables are printed directly:
--   x
--
-- Function terms are printed in the form:
--   f(t1,t2,...,tn)
--
-- Constants (functions with no arguments) are printed as:
--   a
------------------------------------------------------------

instance Show Term where
  show (Var x) = x
  show (Func {funcName = name, funcArgs = args})
    | null args = name
    | otherwise =
        name ++ "(" ++ intercalate "," (map show args) ++ ")"
