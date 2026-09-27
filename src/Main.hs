module Main where

import Data.Maybe (isNothing)
import Match (matchTerm)
import Rewrite (rewrite)
import Term (Term (Var), mkFunc)
import Unify (conflict, decompose, delete, eliminate, occursCheck, swap, unify)

main :: IO ()
main = do
  testMatch
  testRewrite

---------------------------------------------------------
-- assert
---------------------------------------------------------
assertEqual :: (Eq a, Show a) => a -> a -> String -> IO ()
assertEqual actual expected msg =
  if actual == expected
    then putStrLn ("PASS: " ++ msg)
    else do
      putStrLn ("FAIL: " ++ msg)
      putStrLn $ "  expected:\n    " ++ show expected
      putStrLn $ "  but got:\n    " ++ show actual

---------------------------------------------------------
-- Terms
--
-- Shared across all test sections.
-- Constants: a, b, c  (arity 0)
-- Variables: x, y, z
-- Functions: f1 = f(a), f2 = f(a,b), g2 = g(a,b)
---------------------------------------------------------
x :: Term
x = Var "x"

y :: Term
y = Var "y"

z :: Term
z = Var "z"

a :: Term
a = mkFunc "a" 0 []

b :: Term
b = mkFunc "b" 0 []

c :: Term
c = mkFunc "c" 0 []

f1 :: Term
f1 = mkFunc "f" 1 [a]

f2 :: Term
f2 = mkFunc "f" 2 [a, b]

g2 :: Term
g2 = mkFunc "g" 2 [a, b]

---------------------------------------------------------
-- DELETE
---------------------------------------------------------
testDelete :: IO ()
testDelete = do
  print "========== TEST DELETE =========="
  assertEqual (delete [(a, a)]) [] "delete same const"
  assertEqual (delete [(a, x)]) [(a, x)] "const-var not deleted"
  assertEqual (delete [(f1, f1)]) [] "delete same func"
  assertEqual (delete [(x, x)]) [] "delete same var"

---------------------------------------------------------
-- CONFLICT
---------------------------------------------------------
testConflict :: IO ()
testConflict = do
  print "========== TEST CONFLICT =========="
  assertEqual (conflict [(f1, f2)]) True "conflict: different arity"
  assertEqual (conflict [(f2, g2)]) True "conflict: different function"
  assertEqual (conflict [(f1, f1)]) False "no conflict"

---------------------------------------------------------
-- OCCURS CHECK
---------------------------------------------------------
testOccursCheck :: IO ()
testOccursCheck = do
  print "========== TEST occursCheck=========="
  assertEqual (occursCheck [(x, a)]) True "valid check"
  assertEqual (occursCheck [(x, mkFunc "f" 1 [x])]) False "occurs check"

---------------------------------------------------------
-- SWAP
---------------------------------------------------------
testSwap :: IO ()
testSwap = do
  print "========== TEST SWAP =========="
  assertEqual (swap [(f1, x)]) [(x, f1)] "swap needed"
  assertEqual (swap [(x, f1)]) [(x, f1)] "no swap"

---------------------------------------------------------
-- DECOMPOSE
---------------------------------------------------------
testDecompose :: IO ()
testDecompose = do
  print "========== TEST DECOMPOSE =========="
  assertEqual
    (decompose [(mkFunc "f" 2 [x, y], mkFunc "f" 2 [a, b])])
    [(x, a), (y, b)]
    "decompose function"
  assertEqual
    (decompose [(a, b)])
    [(a, b)]
    "no decomposition"

---------------------------------------------------------
-- ELIMINATE
---------------------------------------------------------
testEliminate :: IO ()
testEliminate = do
  print "========== TEST ELIMINATE =========="
  assertEqual
    (eliminate [(x, a), (x, mkFunc "f" 1 [y]), (y, y)])
    [(x, a), (a, mkFunc "f" 1 [y]), (y, y)]
    "elimination"
  assertEqual
    (eliminate [(mkFunc "f" 2 [a, x], b), (x, y), (a, Var "z")])
    [(mkFunc "f" 2 [a, y], b), (x, y), (a, Var "z")]
    "elimination"

---------------------------------------------------------
-- UNIFY
---------------------------------------------------------
testUnify :: IO ()
testUnify = do
  print "========== TEST UNIFY =========="

  -- x ≐ b, a ≐ y  →  {x ↦ b, y ↦ a}
  assertEqual
    (unify [(x, b), (a, y)])
    (Just [(x, b), (y, a)])
    "unify two var with const"

  -- f(a, x) ≐ f(a, b)  →  {x ↦ b}
  assertEqual
    (unify [(mkFunc "f" 2 [a, x], mkFunc "f" 2 [a, b])])
    (Just [(x, b)])
    "unify two functions"

  -- f(x, g(y)) ≐ f(a, g(b))  →  {x ↦ a, y ↦ b}
  assertEqual
    (unify [(mkFunc "f" 2 [x, mkFunc "g" 1 [y]], mkFunc "f" 2 [a, mkFunc "g" 1 [b]])])
    (Just [(x, a), (y, b)])
    "nested decomposition"

  -- x ≐ y  →  {x ↦ y}
  assertEqual (unify [(x, y)]) (Just [(x, y)]) "variable unifies with variable"

  -- x ≐ y, y ≐ a  →  {x ↦ a, y ↦ a}
  assertEqual
    (unify [(x, y), (y, a)])
    (Just [(x, a), (y, a)])
    "chained variable elimination"

  assertEqual (unify []) (Just []) "empty equation set"

  -- f(a) ≐ g(a)  →  Nothing
  assertEqual
    (unify [(mkFunc "f" 1 [a], mkFunc "g" 1 [a])])
    Nothing
    "conflict: different function symbols"

  -- f(a) ≐ f(a, b)  →  Nothing
  assertEqual
    (unify [(mkFunc "f" 1 [a], mkFunc "f" 2 [a, b])])
    Nothing
    "conflict: different arity"

  -- x ≐ f(x)  →  Nothing
  assertEqual (unify [(x, mkFunc "f" 1 [x])]) Nothing "occurs check: x in f(x)"

  -- x ≐ f(g(x))  →  Nothing
  assertEqual
    (unify [(x, mkFunc "f" 1 [mkFunc "g" 1 [x]])])
    Nothing
    "occurs check: x nested in f(g(x))"

  -- f(x, x) ≐ f(a, a)  →  {x ↦ a}
  assertEqual
    (unify [(mkFunc "f" 2 [x, x], mkFunc "f" 2 [a, a])])
    (Just [(x, a)])
    "same variable appears twice"

  -- x ≐ a, x ≐ b  →  Nothing
  assertEqual (unify [(x, a), (x, b)]) Nothing "conflict via chained elimination"

---------------------------------------------------------
-- MATCH
--
-- match l u = sigma  such that  l*sigma = u
-- Only variables in the pattern l are substituted.
-- Failure returns [].
---------------------------------------------------------
testMatch :: IO ()
testMatch = do
  print "========== TEST MATCH =========="

  -- x ~ x  →  {}  (x ↦ x is a no-op)
  assertEqual (matchTerm x x) [(x, x)] "match same variable"

  -- x ~ y  →  {x ↦ y}
  assertEqual (matchTerm x y) [(x, y)] "match variable with variable"

  -- x ~ a  →  {x ↦ a}
  assertEqual (matchTerm x a) [(x, a)] "match variable with constant"

  -- x ~ f(a)  →  {x ↦ f(a)}
  assertEqual (matchTerm x f1) [(x, f1)] "match variable with function"

  -- a ~ a  →  {}
  assertEqual (matchTerm a a) [] "match same constant"

  -- a ~ b  →  []  (failure: constants differ)
  assertEqual (matchTerm a b) [] "match different constants"

  -- a ~ f(a)  →  []  (failure: arity mismatch)
  assertEqual (matchTerm a f1) [] "match constant with function"

  -- f(x) ~ f(a)  →  {x ↦ a}
  assertEqual (matchTerm (mkFunc "f" 1 [x]) f1) [(x, a)] "match same function"

  -- f(x, y) ~ f(a, b)  →  {x ↦ a, y ↦ b}
  assertEqual
    (matchTerm (mkFunc "f" 2 [x, y]) f2)
    [(x, a), (y, b)]
    "match function with multiple arguments"

  -- f(x, g(y)) ~ f(a, g(b))  →  {x ↦ a, y ↦ b}
  assertEqual
    (matchTerm
      (mkFunc "f" 2 [x, mkFunc "g" 1 [y]])
      (mkFunc "f" 2 [a, mkFunc "g" 1 [b]]))
    [(x, a), (y, b)]
    "match nested functions"

  -- f(a) ~ g(a)  →  []  (failure: different function symbols)
  assertEqual (matchTerm f1 (mkFunc "g" 1 [a])) [] "match conflict: different function symbols"

  -- f(a) ~ f(a, b)  →  []  (failure: different arity)
  assertEqual (matchTerm f1 f2) [] "match conflict: different arity"

  -- f(a) ~ x  →  []  (failure: pattern is not a variable)
  assertEqual (matchTerm f1 x) [] "match function with target variable"

  -- f(x, x) ~ f(a, a)  →  {x ↦ a}  (consistent repeated variable)
  assertEqual
    (matchTerm (mkFunc "f" 2 [x, x]) (mkFunc "f" 2 [a, a]))
    [(x, a)]
    "match repeated variable consistently"

  -- f(x, x, y) ~ f(a, a, b)  →  {x ↦ a, y ↦ b}
  assertEqual
    (matchTerm (mkFunc "f" 3 [x, x, y]) (mkFunc "f" 3 [a, a, b]))
    [(x, a), (y, b)]
    "match repeated variable consistently with a pair after it"

  -- f(x, x) ~ f(a, b)  →  []  (failure: x cannot map to both a and b)
  assertEqual
    (matchTerm (mkFunc "f" 2 [x, x]) (mkFunc "f" 2 [a, b]))
    []
    "match repeated variable inconsistently"

  -- f(x, y) ~ f(a, a)  →  {x ↦ a, y ↦ a}
  assertEqual
    (matchTerm (mkFunc "f" 2 [x, y]) (mkFunc "f" 2 [a, a]))
    [(x, a), (y, a)]
    "two variables map to same target"

  -- f(a) ~ f(a)  →  {}  (ground pattern, no variables)
  assertEqual (matchTerm f1 f1) [] "match ground terms"

  -- f(a) ~ f(b)  →  []  (failure: ground terms differ)
  assertEqual (matchTerm f1 (mkFunc "f" 1 [b])) [] "match ground terms, different target"

---------------------------------------------------------
-- REWRITE
--
-- rewrite u (l, r) returns all terms reachable from u
-- in one step by applying the rule l -> r at any subterm.
--
-- For each subterm u' matching l with substitution sigma,
-- the result is C[r*sigma] where C[_] is the context of u'.
---------------------------------------------------------
testRewrite :: IO ()
testRewrite = do
  print "========== TEST REWRITE =========="

  -- a rewritten by x -> b
  -- one context: C[_]=_, u'=a, sigma={x↦a}, result=b
  assertEqual
    (rewrite a (x, b))
    [b]
    "rewrite constant: variable rule"

  -- f(a) rewritten by x -> b
  -- two contexts: C[_]=_ gives b, C[_]=f(_) gives f(b)
  assertEqual
    (rewrite f1 (x, b))
    [b, mkFunc "f" 1 [b]]
    "rewrite function: variable rule matches at all positions"

  -- f(a) rewritten by f(x) -> g(x)
  -- only root matches: sigma={x↦a}, result=g(a)
  assertEqual
    (rewrite f1 (mkFunc "f" 1 [x], mkFunc "g" 1 [x]))
    [mkFunc "g" 1 [a]]
    "rewrite function: rule matches at root only"

  -- f(a) rewritten by g(x) -> b
  -- no subterm matches g(_)
  assertEqual
    (rewrite f1 (mkFunc "g" 1 [x], b))
    []
    "rewrite: no match"

  -- f(a, b) rewritten by x -> c
  -- three contexts: root, first arg, second arg
  assertEqual
    (rewrite f2 (x, c))
    [c, mkFunc "f" 2 [c, b], mkFunc "f" 2 [a, c]]
    "rewrite binary function: variable rule matches at all positions"

  -- f(a, b) rewritten by f(x, y) -> g(y, x)
  -- root matches: sigma={x↦a, y↦b}, result=g(b, a)
  assertEqual
    (rewrite f2 (mkFunc "f" 2 [x, y], mkFunc "g" 2 [y, x]))
    [mkFunc "g" 2 [b, a]]
    "rewrite: swap arguments via rule"

  -- f(f(a)) rewritten by f(x) -> g(x)
  -- root: sigma={x↦f(a)}, result=g(f(a))
  -- inner f(a): sigma={x↦a}, result=f(g(a))
  assertEqual
    (rewrite
      (mkFunc "f" 1 [mkFunc "f" 1 [a]])
      (mkFunc "f" 1 [x], mkFunc "g" 1 [x]))
    [ mkFunc "g" 1 [mkFunc "f" 1 [a]]
    , mkFunc "f" 1 [mkFunc "g" 1 [a]]
    ]
    "rewrite nested: rule matches at multiple depths"