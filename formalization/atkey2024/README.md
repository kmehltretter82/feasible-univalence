# Atkey 2024: Costed Machine Model (M4.0) in Lean 4.33.1

This package formalizes the target machine of:

> Robert Atkey, *Polynomial Time and Dependent Types*, Proc. ACM Program. Lang. 8 (POPL 2024), Article 76, DOI [10.1145/3632918](https://doi.org/10.1145/3632918); extended version [arXiv:2307.09145v2](https://arxiv.org/abs/2307.09145v2), Section 5.1 and Figure 1.

It is milestone M4.0 of the M4 plan in the [rule audit](../../docs/atkey-rule-audit.md). The reference artefact is [`bobatkey/qtt-models`](https://github.com/bobatkey/qtt-models/tree/76fdbacd6e7bee19cb448b4d41bc21ac3687d63e), tag `popl-2024-artefact-submission`, commit `76fdbacd6e7bee19cb448b4d41bc21ac3687d63e`, module `AmortisedModel.Machine`.

The package uses core Lean 4.33.1 only; no Mathlib is required. The upstream BSD 3-Clause license is retained in [LICENSE](LICENSE).

## Why this machine

Atkey's polynomial-time theorems (6.1 and 6.2) bound the step count of this machine. The audit recommends it as the common cost model for Papers A and B: it is a call-by-value closure machine, which is the target style the roadmap prefers for Paper A. Every rule costs one unit, and an applied closure receives itself as an extra argument, which is how recursive iterators are implemented.

## Source-to-Lean map

| Source (Figure 1 / `AmortisedModel.Machine`) | Lean ([`Atkey2024/Machine.lean`](Atkey2024/Machine.lean)) |
|---|---|
| `exp n`: `` ` `` · `ƛ` · `_·_` · `⋆` · `_,_` · `letpair_then_` · `true` · `false` · `cond_then_else_` · `seq_then_` | `Expr n`: `var` · `lam` · `app` · `unit` · `pair` · `letpair` · `true` · `false` · `cond` · `seq` |
| `val`, `env` (mutual) | `Val`, `Env` (mutual) |
| `nat-val` (§6.1.3) | `natValue` |
| `i , η ⇓v V` | `Lookup`; equivalent to `Env.get` by `lookup_iff_get` |
| `E , η ⇓[ k ] V`: `access`, `lam`, `app`, `mkunit`, `mkpair`, `letpair`, `true`, `false`, `cond-true`, `cond-false`, `seq` | `Eval E η k V`: `access`, `lam`, `app`, `mkunit`, `mkpair`, `letpair`, `true`, `false`, `condTrue`, `condFalse`, `seq` |

Syntax is intrinsically scoped, as in the artefact. Lookup premises are stated with the total function `Env.get`; `lookup_iff_get` proves this equivalent to the artefact's inductive relation. Rule costs are written exactly as in the artefact (`1 + k`, `k₁ + 1 + k₂`).

## Additions not in the source

- `Eval.deterministic`: both the value and the step count are determined by the program and the environment, so a step count `steps_M(e, x)` is well defined.
- `run`: a fuel-bounded evaluator. `run_sound`, `run_complete` and `eval_iff_run` show that it computes exactly the evaluation relation: `Eval E η k V ↔ run k E η = some (k, V)`.
- `countdown_cost`: a recursive traversal of the unary input `natValue m` takes exactly `3 * m + 6` steps. It is proved by induction on `m`, so it holds uniformly over all inputs, as a polynomial bound must.

## Verification

```sh
lake build
lake env lean MachineChecks.lean
```

Both pass with Lean 4.33.1. `MachineChecks.lean` contains executable `#guard` tests of `run` and prints the axioms of the main theorems:
- `lookup_iff_get` and `Eval.deterministic` use no axioms;
- `run_sound`, `run_complete`, `eval_iff_run` and `countdown_cost` use only `propext`.

## Scope

This is only the machine. The resource monoids, the realisability model, the QTT model of §5.3, and the interpretation of QTT syntax (M4.1–M4.5) are not formalized here.
