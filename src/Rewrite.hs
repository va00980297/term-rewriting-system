module Rewrite where

import Match (matchTerm, subTerm)
import Term
  ( Context,
    Sub,
    Term (Func, Var, funcArgs, funcArity, funcName),
  )

------------------------------------------------------------
-- Apply a rewrite rule l -> r to a term u.
--
-- For each subterm u' of u that matches l with substitution sigma,
-- returns C[r*sigma] where C[_] is the context of u' in u.
--
-- Returns [] if no subterm matches.
------------------------------------------------------------
rewrite :: Term -> (Term, Term) -> [Term]
rewrite u (l, r) = tryContexts u (findContexts u) (l, r)

------------------------------------------------------------
-- Try applying a rewrite rule to each (context, subterm) pair.
--
-- For each (C[_], u'): attempt match(l, u').
--   Failure ([]): skip.
--   Success sigma: add C[r*sigma] to results.
------------------------------------------------------------
tryContexts :: Term -> [(Context, Term)] -> (Term, Term) -> [Term]
tryContexts u [] _ = []
tryContexts u ((c, v) : rest) (l, r) =
  case matchTerm l v of
    [] -> tryContexts u rest (l, r)
    sigma -> c (subTerm sigma r) : tryContexts u rest (l, r)

------------------------------------------------------------
-- Enumerate all (context, subterm) pairs of a term,
-- in breadth-first order.
--
-- For each pair (C[_], u'): C[u'] = u.
--
-- Uses an iterative layer expansion:
--   Layer 0: (id, u)
--   Layer n+1: direct subterms of each term in layer n,
--              with contexts lifted to the top level.
------------------------------------------------------------
findContexts :: Term -> [(Context, Term)]
findContexts (Var x) = [(\hole -> hole, Var x)]
findContexts func@(Func {funcArgs = args}) = 
  go [(\hole -> hole, func)]
    where
      go [] = []
      go layer = layer ++ go (nextLayer layer)

------------------------------------------------------------
-- Expand one layer: given a list of (context, subterm) pairs,
-- produce the next layer by expanding each Func subterm
-- into its direct argument positions.
--
-- Variables and constants have no subterms and are skipped.
------------------------------------------------------------
nextLayer :: [(Context, Term)] -> [(Context, Term)]
nextLayer [] = []
nextLayer ((c, Var x) : rest) = nextLayer rest
nextLayer ((c, func@(Func {funcArgs = args})) : rest) =
  liftContext c (contextsArgs func [] args) ++ nextLayer rest

------------------------------------------------------------
-- Enumerate direct-child (context, subterm) pairs of a
-- function term, using prev/rest to represent the hole position.
--
-- For argument t at position i:
--   C[_] = func { funcArgs = prev ++ [_] ++ rest }
--
-- prev accumulates left siblings; rest is the remaining args.
------------------------------------------------------------
contextsArgs :: Term -> [Term] -> [Term] -> [(Context, Term)]
contextsArgs func _ [] = []
contextsArgs func prev (t : rest) =
  (\hole -> func {funcArgs = prev ++ [hole] ++ rest}, t)
    : contextsArgs func (prev ++ [t]) rest

------------------------------------------------------------
-- Lift a list of (context, subterm) pairs through an outer context.
--
-- Given outer context c and child pairs (c', u'):
--   new context = \hole -> c (c' hole)
--
-- This composes the two contexts so the hole reaches
-- the correct position in the original term.
------------------------------------------------------------
liftContext :: Context -> [(Context, Term)] -> [(Context, Term)]
liftContext c [] = []
liftContext c ((c', t) : rest) =
  (\hole -> c (c' hole), t) : liftContext c rest