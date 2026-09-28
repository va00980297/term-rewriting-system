module Match where

import Term (Sub, Term (Func, Var, funcArgs, funcArity, funcName))

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
-- Since [] denotes failure, a successful match that binds
-- no variable (e.g. a ~ a) cannot return the empty
-- substitution. It returns the pseudo-binding (a, a) as a
-- non-empty success marker instead. This is harmless under
-- subTerm, which only ever replaces variables.
--
-- Returns:
--   Sub  : the substitution σ on success
--   []   : failure (no such σ exists)
------------------------------------------------------------
matchTerm :: Term -> Term -> Sub
matchTerm (Var x) t = [(Var x, t)]
matchTerm
  func1@(Func {funcName = f, funcArity = n, funcArgs = args1})
  func2@(Func {funcName = g, funcArity = m, funcArgs = args2})
    | f /= g || n /= m = []
    | n == 0 = [(func1, func2)]
    | otherwise = matchList args1 args2
matchTerm _ _ = []

------------------------------------------------------------
-- Match argument lists of two function terms pairwise.
--
-- Each argument pair is matched independently, and the
-- resulting substitutions are combined with merge. If the
-- same variable appears more than once in the pattern,
-- merge checks that all occurrences are bound to the
-- same term.
--
-- Nothing is substituted into the remaining arguments:
-- applying σ to the target would break "target variables
-- are constants", and applying σ to the pattern would turn
-- target variables into pattern variables.
--
-- Precondition: both lists are non-empty and of equal
-- length (guaranteed by the arity check in matchTerm).
--
-- Returns [] if any argument pair fails to match, or if
-- the per-argument substitutions are inconsistent.
------------------------------------------------------------
matchList :: [Term] -> [Term] -> Sub
matchList [p] [t] = matchTerm p t
matchList (p : ps) (t : ts) =
  case matchTerm p t of
    [] -> []
    sigma ->
      case matchList ps ts of
        [] -> []
        rest -> merge rest sigma
matchList _ _ = []

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
subTerm sigma func@(Func {funcArgs = args}) =
  func {funcArgs = subList sigma args}

------------------------------------------------------------
-- Apply a substitution to a list of terms.
--
-- Each term in the list is substituted independently
-- using subTerm.
------------------------------------------------------------
subList :: Sub -> [Term] -> [Term]
subList sigma = map (subTerm sigma)

------------------------------------------------------------
-- Merge two substitutions.
--
-- merge τ σ adds every binding of τ to σ, one at a time,
-- using mergeSingle. Bindings of σ keep their order;
-- new bindings are appended at the end.
--
-- Two substitutions are compatible if every variable bound
-- in both is mapped to the same term:
--
--   {x ↦ a} ∪ {x ↦ a, y ↦ b}  =  {x ↦ a, y ↦ b}
--   {x ↦ a} ∪ {x ↦ b}          =  failure
--
-- Precondition: σ is non-empty (a successful match result),
-- since an empty result is read as failure.
--
-- Returns:
--   Sub  : σ ∪ τ on success
--   []   : failure (some variable is bound inconsistently)
------------------------------------------------------------
merge :: Sub -> Sub -> Sub
merge [] sigma = sigma
merge (b : bs) sigma =
  case mergeSingle b sigma of
    [] -> []
    tau -> merge bs tau

------------------------------------------------------------
-- Add a single binding p ↦ t to a substitution σ.
--
--   * p is not a variable     → pseudo-binding (a, a) from a
--                               constant match; carries no
--                               information, σ is unchanged
--   * p ↦ t already in σ      → σ is unchanged
--   * p ↦ s in σ with s ≠ t   → conflict, failure
--   * p is unbound in σ       → append p ↦ t
--
-- Note: x ↦ x is a real binding and must not be dropped,
-- otherwise f(x, x) ~ f(a, x) would wrongly succeed.
--
-- Returns [] on conflict.
------------------------------------------------------------
mergeSingle :: (Term, Term) -> Sub -> Sub
mergeSingle (Func {}, _) sigma = sigma
mergeSingle (p, t) [] = [(p, t)]
mergeSingle (p, t) ((q, s) : ys)
  | p /= q =
      case mergeSingle (p, t) ys of
        [] -> []
        rest -> (q, s) : rest
  | t == s = (q, s) : ys
  | otherwise = []