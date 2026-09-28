# Term Rewriting System (Haskell)

A step-by-step implementation of core term rewriting theory in Haskell,
built up from first principles.

---

## Current Progress

### Implemented
- **Term** — first-order term representation (variables, constants, functions)
- **Unification** — rule-based syntactic unification (Martelli & Montanari 1982);
  returns the unifier in solved form
- **Matching** — one-sided unification; finds σ such that l·σ = u
- **Rewriting** — one-step rewriting via context decomposition; returns all
  one-step reducts, for a single rule (`rewrite`) or a list of rules (`rewriteSystem`)

### Planned
- **Normalization** — multi-step rewriting and normal forms for a rewrite system
- **Unification Modulo Rewriting** — equational unification using rewrite rules
  as an equational theory

---

## Project Structure

```
src/
├── Term.hs       -- Term data type: variables, constants, functions
│                    Type aliases: EqSet, Sub, Context, Rule, RewriteSystem
├── Match.hs      -- Matching: match l u = σ such that l·σ = u
├── Unify.hs      -- Unification: rule-based algorithm (Martelli & Montanari)
├── Rewrite.hs    -- One-step rewriting: context enumeration and rule application
└── Main.hs       -- Test suite for all modules
```

---

## Algorithm Overview

### Unification

Given a set of equations { s₁ ≐ t₁, …, sₙ ≐ tₙ } (`EqSet`), find a substitution σ
such that sᵢ·σ = tᵢ·σ for all i.

Based on the transformation rules of Martelli & Montanari (1982), presented here
as six rules following Baader & Snyder (2001):

| Rule | Function | Condition | Action |
|---|---|---|---|
| Delete | `delete` | s ≐ s | Remove |
| Decompose | `decompose` | f(s₁,…,sₙ) ≐ f(t₁,…,tₙ), n > 0 | Replace with s₁ ≐ t₁, …, sₙ ≐ tₙ |
| Conflict | `conflict` | f(s̄) ≐ g(t̄), f ≠ g or arity differs | Fail |
| Swap | `swap` | t ≐ x, t not a variable | Replace with x ≐ t |
| Eliminate | `eliminate` | x ≐ t | Apply {x ↦ t} to all other equations, keep x ≐ t |
| Occurs Check | `occursCheck` | x ≐ t, t not a variable, x ∈ vars(t) | Fail |

Each round applies the rules in a fixed order:

```
check → Swap → Decompose → check → Delete → check → Eliminate
```

where `check` fails on Conflict or Occurs Check. Rounds repeat until the equation
set no longer changes.

`unify` returns `Just` the result in solved form { x₁ ≐ t₁, …, xₖ ≐ tₖ },
read as the unifier { x₁ ↦ t₁, …, xₖ ↦ tₖ }, or `Nothing` on failure.

```
unify [x ≐ y, y ≐ a]        →  Just [x ≐ a, y ≐ a]
unify [x ≐ f(x)]            →  Nothing   (occurs check)
unify [x ≐ a, x ≐ b]        →  Nothing   (conflict after elimination)
```

### Matching

One-sided unification: σ is only applied to the pattern, never the target.
Variables in the target are treated as constants.

```
match (f(x, b)) (f(a, b))  →  [x ↦ a]
match (f(x, y)) (f(y, x))  →  [x ↦ y, y ↦ x]
match (f(a))    (g(a))     →  []   (failure)
match (f(x, x)) (f(a, b))  →  []   (failure: x cannot map to both a and b)
```

**Return convention.** `[]` denotes failure. A match that binds no variable
cannot return the empty substitution, so constants produce a pseudo-binding
(c, c) as a success marker:

```
match a (a)                →  [(a, a)]
match (f(a))    (f(a))     →  [(a, a)]
match (f(b, x)) (f(b, a))  →  [(b, b), x ↦ a]
```

Pseudo-bindings are ignored when σ is applied (`subTerm` only replaces variables).

### Rewriting

Given a term u and a rule l → r, find all one-step reducts:

1. Enumerate all contexts C[_] and subterms u' such that C[u'] = u,
   breadth-first (outermost positions first, left to right)
2. For each u', attempt match(l, u') to get σ
3. Return C[r·σ] for each successful match, in enumeration order

```
rewrite f(a)    (f(x) → g(x))       →  [g(a)]
rewrite f(f(a)) (f(x) → g(x))       →  [g(f(a)), f(g(a))]
rewrite f(y, x) (f(x, y) → g(y, x)) →  [g(x, y)]
```

**Well-formed rules.** By convention a rewrite rule l → r satisfies:

- l is not a variable
- vars(r) ⊆ vars(l)

These conditions are **not enforced** by the code. The test suite deliberately
uses rules with a bare variable on the left, because such a rule matches every
subterm and is convenient for testing position enumeration:

```
rewrite f(a) (x → b)   →  [b, f(b)]   -- accepted, but not a well-formed rule
```

---

## Build & Run

```bash
cabal build
cabal run
```

---

## Verification

Cross-check results with SWI-Prolog:

```bash
# Install
sudo apt install swi-prolog   # Ubuntu
brew install swi-prolog       # Mac

# Run
swipl
```

Unification:

```prolog
?- unify_with_occurs_check(f(X, b), f(a, Y)).
?- unify_with_occurs_check(X, f(X)).
?- unify_with_occurs_check(f(a), g(a)).
```

Matching (`subsumes_term(General, Specific)` is one-sided matching):

```prolog
?- G = f(X, X), S = f(a, a), subsumes_term(G, S), G = S.
?- subsumes_term(f(X, X), f(a, b)).     % false
```

---

## Reference

- Martelli, A. & Montanari, U. (1982). *An Efficient Unification Algorithm*.
  ACM TOPLAS 4(2), 258–282.
- Baader, F. & Snyder, W. (2001). *Unification Theory*.
  In Handbook of Automated Reasoning, Vol. I, Ch. 8.
- Baader, F. & Nipkow, T. (1998). *Term Rewriting and All That*.
  Cambridge University Press.

---

## Author

https://github.com/va00980297