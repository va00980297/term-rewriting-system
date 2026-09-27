{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Used otherwise as a pattern" #-}
module Match where

import Term (Sub, Term (Func, Var, funcArgs, funcArity, funcName))
import Debug.Trace ( trace )

------------------------------------------------------------
-- Matching
--
-- Given a pattern p and a target t, find a substitution σ
-- such that pσ = t.
--
-- Unlike unification:
--   * σ is only applied to the pattern, never the target
--   * variables in the target are treated as constants
--
-- Returns:
--   Sub  : the substitution σ on success
--   []   : failure (no such σ exists)
------------------------------------------------------------
matchTerm :: Term -> Term -> Sub
matchTerm (Var x) t = [(Var x, t)]
matchTerm
  Func {funcName = f, funcArity = n, funcArgs = args1}
  Func {funcName = g, funcArity = m, funcArgs = args2}
    | f == g && n == m = matchList args1 args2
    | otherwise = trace "match: incompatible terms" []
matchTerm _ _ = trace "match: incompatible terms" []

------------------------------------------------------------
-- Match argument lists of two function terms pairwise.
--
-- After each successful argument match, the resulting
-- substitution is applied to the remaining pattern arguments
-- before continuing. This ensures that if the same variable
-- appears multiple times in the pattern, later occurrences
-- are already instantiated and can be checked for consistency.
--
-- Returns [] if any argument pair fails to match.
------------------------------------------------------------
matchList :: [Term] -> [Term] -> Sub
matchList [] _ = []
matchList _ [] = []
matchList (x : xs) (y : ys) =
  case matchTerm x y of
    [] -> []
    sigma ->
      sigma
        ++ matchList (subList sigma xs) (subList sigma ys)

------------------------------------------------------------
-- Apply a substitution to a single term, recursively.
--
-- Variables are replaced if they appear in the substitution.
-- Function arguments are substituted element-wise.
-- Unbound variables are left unchanged.
------------------------------------------------------------
subTerm :: Sub -> Term -> Term
subTerm [] t = t
subTerm ((lhs, rhs) : rest) (Var x)
  | lhs == Var x = rhs
  | otherwise = subTerm rest (Var x)
subTerm ((lhs, rhs) : rest) func@(Func {funcArgs = args}) =
  func
    { funcArgs = subList ((lhs, rhs) : rest) args
    }

------------------------------------------------------------
-- Apply a substitution to a list of terms.
--
-- Each term in the list is substituted independently
-- using subTerm.
------------------------------------------------------------
subList :: Sub -> [Term] -> [Term]
subList [] ts = ts
subList sigma [] = []
subList sigma (x : xs) =
  subTerm sigma x : subList sigma xs