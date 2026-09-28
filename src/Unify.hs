module Unify where

import Term (EqSet, Term (Func, Var, funcArgs, funcArity, funcName))

------------------------------------------------------------
-- Syntactic unification (Martelli & Montanari 1982).
--
-- Each round applies, in order:
--
--   check → Swap → Decompose → check → Delete → check → Eliminate
--
-- where check fails on Conflict or Occurs Check.
-- Rounds repeat until the equation set no longer changes.
--
-- It stops when:
--   * the equation set is fully simplified (success)
--   * a conflict or occurs-check failure is detected (failure)
--
-- Returns:
--   Just EqSet  : unification succeeds; the result is in
--                 solved form x₁ ≐ t₁, …, xₖ ≐ tₖ, read as
--                 the unifier {x₁ ↦ t₁, …, xₖ ↦ tₖ}
--   Nothing     : unification fails
------------------------------------------------------------
unify :: EqSet -> Maybe EqSet
unify set = do
  result <- applyRules set
  if result == set
    then Just result
    else unify result

------------------------------------------------------------
-- One round of rule applications (see unify).
------------------------------------------------------------
applyRules :: EqSet -> Maybe EqSet
applyRules set =
  check set
    >>= (Just . simplify)
    >>= check
    >>= (Just . delete)
    >>= check
    >>= (Just . eliminate)

------------------------------------------------------------
-- Fail if the equation set contains a conflict or
-- violates the occurs check.
------------------------------------------------------------
check :: EqSet -> Maybe EqSet
check set
  | conflict set || not (occursCheck set) = Nothing
  | otherwise = Just set

------------------------------------------------------------
-- Swap, then Decompose.
------------------------------------------------------------
simplify :: EqSet -> EqSet
simplify set = decompose (swap set)

------------------------------------------------------------
-- Rule: Delete
--
-- s ≐ s  →  remove the equation.
--
-- Two identical terms are already unified, so the equation
-- contributes nothing and can be discarded.
------------------------------------------------------------
delete :: EqSet -> EqSet
delete [] = []
delete ((s, t) : xs)
  | s == t = delete xs
  | otherwise = (s, t) : delete xs

------------------------------------------------------------
-- Rule: Decompose
--
-- f(s1,...,sn) ≐ f(t1,...,tn)
--      ↓
-- s1 ≐ t1, ..., sn ≐ tn
--
-- Replace an equation between two function terms with equations
-- between their corresponding arguments.
--
-- Equations involving constants are left unchanged; they are
-- handled by Delete (a ≐ a) or Conflict (a ≐ b).
------------------------------------------------------------
decompose :: EqSet -> EqSet
decompose [] = []
decompose ((f@(Func {funcArgs = args1}), g@(Func {funcArgs = args2})) : xs)
  | null args1 || null args2 =
      (f, g) : decompose xs
  | otherwise = zipTerms args1 args2 ++ decompose xs
decompose (eq : xs) = eq : decompose xs

------------------------------------------------------------
-- Pair corresponding arguments of two function terms.
------------------------------------------------------------
zipTerms :: [Term] -> [Term] -> EqSet
zipTerms [] [] = []
zipTerms (s : xs) (t : ys) = (s, t) : zipTerms xs ys
zipTerms _ _ = []

------------------------------------------------------------
-- Rule: Conflict
--
-- f(...) ≐ g(...)
--
-- Fail if:
--   * function symbols are different, or
--   * arities are different.
------------------------------------------------------------
conflict :: EqSet -> Bool
conflict [] = False
conflict ((Func {funcName = f, funcArity = n}, Func {funcName = g, funcArity = m}) : xs)
  | f == g && n == m = conflict xs
  | otherwise = True
conflict (_ : xs) = conflict xs

------------------------------------------------------------
-- Rule: Swap
--
-- t ≐ x   (t not a variable)
--      ↓
-- x ≐ t
--
-- Ensure that variables always appear on the left-hand side.
------------------------------------------------------------
swap :: EqSet -> EqSet
swap [] = []
swap (eq : xs) =
  case eq of
    (func@(Func {}), Var x) -> (Var x, func) : swap xs
    _ -> eq : swap xs

------------------------------------------------------------
-- Rule: Eliminate
--
-- x ≐ t
--
-- Generate the substitution {x ↦ t}, apply it to all other
-- equations (both already processed and remaining), and keep
-- the binding x ≐ t in the result.
--
-- The condition x ∉ vars(t) is ensured by the occurs check
-- that runs before Eliminate in each round.
------------------------------------------------------------
eliminate :: EqSet -> EqSet
eliminate set = go set []
  where
    go [] processed = processed
    go ((Var x, t) : xs) processed =
      go (substitute xs (Var x) t) (substitute processed (Var x) t ++ [(Var x, t)])
    go (eq : xs) processed = go xs (processed ++ [eq])

------------------------------------------------------------
-- Rule: Occurs Check
--
-- x ≐ t   (t not a variable)
--
-- Fail if x occurs anywhere inside t.
--
-- Returns True if the check passes (no occurrence found).
------------------------------------------------------------
occursCheck :: EqSet -> Bool
occursCheck [] = True
occursCheck ((Var x, Func {funcArgs = args}) : xs)
  | notOccursIn (Var x) args = occursCheck xs
  | otherwise = False
occursCheck (_ : xs) = occursCheck xs

------------------------------------------------------------
-- Check whether a variable does not occur in a list of terms.
------------------------------------------------------------
notOccursIn :: Term -> [Term] -> Bool
notOccursIn _ [] = True
notOccursIn (Var x) (Var y : ys)
  | x /= y = notOccursIn (Var x) ys
  | otherwise = False
notOccursIn (Var x) (Func {funcArgs = args} : ys)
  | notOccursIn (Var x) args = notOccursIn (Var x) ys
  | otherwise = False

------------------------------------------------------------
-- Apply a single binding {x ↦ t} to every equation in the
-- equation set.
------------------------------------------------------------
substitute :: EqSet -> Term -> Term -> EqSet
substitute [] _ _ = []
substitute ((lhs, rhs) : xs) (Var x) t =
  (replaceVar lhs (Var x) t, replaceVar rhs (Var x) t)
    : substitute xs (Var x) t

------------------------------------------------------------
-- Apply a single binding {x ↦ t} to a term, recursively.
--
-- replaceVar s x t  =  s{x ↦ t}
--
-- Not to be confused with Match.subTerm, which applies a
-- whole substitution (a list of bindings).
------------------------------------------------------------
replaceVar :: Term -> Term -> Term -> Term
replaceVar (Var v) (Var x) t
  | v == x = t
  | otherwise = Var v
replaceVar func@(Func {funcArgs = args}) (Var x) t =
  func
    { funcArgs =
        map (\s -> replaceVar s (Var x) t) args
    }