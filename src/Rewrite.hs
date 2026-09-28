module Rewrite where

import Match (matchTerm, subTerm)
import Term
  ( Context,
    Rule,
    RewriteSystem,
    Sub,
    Term (Func, Var),
    funcArgs,
    funcArity,
    funcName,
  )

------------------------------------------------------------
-- Apply a rewrite system (a list of rules) to a term u.
--
-- Tries each rule in order and collects all one-step reducts.
-- Returns [] if no rule applies anywhere in u.
------------------------------------------------------------
rewriteSystem :: Term -> RewriteSystem -> [Term]
rewriteSystem u rest = foldr ((++) . rewrite u) [] rest

------------------------------------------------------------
-- Apply a single rewrite rule l -> r to a term u.
--
-- Enumerates all subterm positions of u (as context/subterm pairs),
-- and for each position where l matches the subterm, returns the
-- result of filling the context with r instantiated by the match.
--
-- Returns [] if no subterm of u matches l.
------------------------------------------------------------
rewrite :: Term -> Rule -> [Term]
rewrite u (l, r) = tryContexts u (findContexts u) (l, r)

------------------------------------------------------------
-- Try applying a rewrite rule at each (context, subterm) pair.
--
-- For each pair (C[_], u'):
--   - Attempt match(l, u') to get substitution sigma.
--   - Failure ([]): skip this position.
--   - Success sigma: yield C[r * sigma] as a reduct.
------------------------------------------------------------
tryContexts :: Term -> [(Context, Term)] -> Rule -> [Term]
tryContexts _ [] _ = []
tryContexts u ((c, v) : rest) (l, r) =
  case matchTerm l v of
    [] -> tryContexts u rest (l, r)
    sigma -> c (subTerm sigma r) : tryContexts u rest (l, r)

------------------------------------------------------------
-- Enumerate all (context, subterm) pairs of a term,
-- in breadth-first order.
--
-- Each pair (C[_], u') satisfies: C[u'] = u.
--
-- Layer 0 : (id, u)              — the whole term
-- Layer n+1: direct children of each Func in layer n,
--            with contexts composed to reach the top.
--
-- Variables / constants appear as leaves and are not expanded further.
------------------------------------------------------------
findContexts :: Term -> [(Context, Term)]
findContexts (Var x) = [(\hole -> hole, Var x)]
findContexts func@(Func {funcArgs = args}) =
  go [(\hole -> hole, func)]
  where
    -- Iteratively expand layers until no Func subterms remain.
    go [] = []
    go layer = layer ++ go (nextLayer layer)

------------------------------------------------------------
-- Expand one BFS layer into the next.
--
-- For each (C[_], subterm) in the current layer:
--   - Var / constant (arity 0): no children, skip.
--   - Func: expand into its direct argument positions
--           and lift those contexts through C.
------------------------------------------------------------
nextLayer :: [(Context, Term)] -> [(Context, Term)]
nextLayer [] = []
nextLayer ((c, Var x) : rest) = nextLayer rest
nextLayer ((c, func@(Func {funcArgs = args})) : rest) =
  liftContext c (contextsArgs func [] args) ++ nextLayer rest

------------------------------------------------------------
-- Enumerate direct-child (context, subterm) pairs of a Func term.
--
-- For each argument t at position i:
--   C[_] = func { funcArgs = [a₀, …, aᵢ₋₁, _, aᵢ₊₁, …] }
--
-- 'prev' accumulates left siblings already processed;
-- 'rest' is the suffix of arguments yet to be visited.
------------------------------------------------------------
contextsArgs :: Term -> [Term] -> [Term] -> [(Context, Term)]
contextsArgs _ _ [] = []
contextsArgs func prev (t : rest) =
  (\hole -> func {funcArgs = prev ++ [hole] ++ rest}, t)
    : contextsArgs func (prev ++ [t]) rest

------------------------------------------------------------
-- Lift a list of (context, subterm) pairs through an outer context c.
--
-- Replaces each inner context c' with (\hole -> c (c' hole)),
-- so the composed context places the hole at the correct position
-- in the original top-level term.
------------------------------------------------------------
liftContext :: Context -> [(Context, Term)] -> [(Context, Term)]
liftContext _ [] = []
liftContext c ((c', t) : rest) =
  (\hole -> c (c' hole), t) : liftContext c rest