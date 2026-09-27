# Term Rewriting System (Haskell)

A step-by-step implementation of core term rewriting theory in Haskell,
built up from first principles.

---

## Current Progress

### Implemented
- **Term** — first-order term representation (variables, constants, functions)
- **Unification** — Martelli & Montanari (1982) six-rule algorithm
- **Matching** — one-sided unification; finds σ such that l·σ = u
- **Rewriting** — one-step rewriting via context decomposition; returns all possible reducts

### Planned
- **Rewrite System** — full rewrite system with rule sets, connected to an LLM API
- **Unification Modulo Rewriting** — equational unification using rewrite rules as an equational theory

---

## Project Structure

```
src/
├── Term.hs       -- Term data type: variables, constants, functions
│                    Type aliases: Sub, Context, Pos
├── Match.hs      -- Pattern matching: match l u = σ such that l·σ = u
├── Unify.hs      -- Unification: Martelli & Montanari six-rule algorithm
├── Rewrite.hs    -- One-step rewriting: context enumeration and rule application
└── Main.hs       -- Test suite for all modules
```

---

## Algorithm Overview

### Unification (Martelli & Montanari 1982)

Given two terms s and t, find σ such that s·σ = t·σ.

Six rules applied repeatedly until stable:

| Rule | Condition | Action |
|---|---|---|
| Delete | s ≐ s | Remove |
| Decompose | f(s̄) ≐ f(t̄) | Replace with sᵢ ≐ tᵢ |
| Conflict | f(s̄) ≐ g(t̄), f≠g | Fail |
| Orient | t ≐ x, t not a variable | Flip |
| Eliminate | x ≐ t, x ∉ vars(t) | Substitute everywhere |
| OccursCheck | x ≐ t, x ∈ vars(t) | Fail |

### Matching

One-sided unification: σ is only applied to the pattern, never the target.

```
match (f(x, b)) (f(a, b))  →  { x ↦ a }
match (f(a))    (g(a))     →  [] (failure)
match (f(x, x)) (f(a, b))  →  [] (failure: x cannot map to both a and b)
```

### Rewriting

Given term u and rule l → r, find all one-step reducts:

1. Enumerate all contexts C[_] and subterms u' such that C[u'] = u
2. For each u', attempt match(l, u') to get σ
3. Return C[r·σ] for each successful match

```
rewrite f(a)  (f(x) → g(x))  →  [g(a)]
rewrite f(a)  (x → b)        →  [b, f(b)]
rewrite f(f(a)) (f(x) → g(x)) →  [g(f(a)), f(g(a))]
```

---

## Build & Run

```bash
cabal build
cabal run
```

---

## Verification

Cross-check unification results with SWI-Prolog:

```bash
# Install
sudo apt install swi-prolog   # Ubuntu
brew install swi-prolog        # Mac

# Run
swipl
```

```prolog
?- unify_with_occurs_check(f(X, b), f(a, Y)).
?- unify_with_occurs_check(X, f(X)).
?- unify_with_occurs_check(f(a), g(a)).
```

---

## Reference

- Martelli, A. & Montanari, U. (1982). *An Efficient Unification Algorithm*. ACM TOPLAS.
- Baader, F. & Snyder, W. (2001). *Unification Theory*. Handbook of Automated Reasoning.

---

## Author

https://github.com/va00980297