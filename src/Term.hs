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

------------------------------------------------------------
-- UNIFY
------------------------------------------------------------

------------------------------------------------------------
-- A set of equations to be unified.
--
-- Each pair (s, t) represents an equation:
--
--   s ≐ t
------------------------------------------------------------
type EqSet = [(Term, Term)]

------------------------------------------------------------
-- MATCH, REWRITE
------------------------------------------------------------

------------------------------------------------------------
-- A substitution: a list of variable-to-term bindings.
--
-- Each pair (Var x, t) represents:
--
--   x ↦ t
--
-- Exception: results of matchTerm may also contain
-- pseudo-bindings (c, c) for constants c. Since [] denotes
-- match failure, (c, c) serves as a non-empty success
-- marker. subTerm only replaces variables, so such pairs
-- have no effect when the substitution is applied.
------------------------------------------------------------
type Sub = [(Term, Term)]

------------------------------------------------------------
-- A context: a term with a single hole.
--
-- Represented as a function Term -> Term.
-- Applying a context C to a term t fills the hole:
--
--   C[t]
------------------------------------------------------------
type Context = Term -> Term

------------------------------------------------------------
-- A rewrite rule l -> r.
--
-- By convention, a well-formed rule satisfies:
--   * l is not a variable
--   * vars(r) ⊆ vars(l)
--
-- These conditions are NOT enforced. The test suite uses
-- rules with a bare variable on the left (e.g. x -> b):
-- such a rule matches every subterm, which is convenient
-- for testing position enumeration in rewrite.
------------------------------------------------------------
type Rule = (Term, Term)

------------------------------------------------------------
-- A rewrite system: a set of rewrite rules.
------------------------------------------------------------
type RewriteSystem = [Rule]