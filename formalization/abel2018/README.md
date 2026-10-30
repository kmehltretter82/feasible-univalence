# Abel 2018: draft Lean implementation

This is a **pre-review implementation checkpoint**, not a proof of the paper or a ready Prove2Me proposal. It uses Lean 4.33.1 and core Lean only; no Mathlib dependency is required for these files.

The source is Abel–Öhman–Vezzosi, *Decidability of Conversion for Type Theory in Type Theory*, with the [v2.1 Agda artifact](https://github.com/mr-ohman/logrel-mltt/tree/eb2b15ab1c4b45923025834d3bb798943cb44b8e). The source MIT license is retained in [LICENSE](LICENSE).

## Contents

- `Abel2018/Syntax.lean`: raw de Bruijn terms, binding operations, weakening, and normal-form predicates.
- `Abel2018/Judgments.lean`: declarative typing, equality, typed reduction, and substitution judgments.
- `Abel2018/Algorithm.lean`: an executable comparison prototype using a natural-number fuel bound.
- `AlgorithmChecks.lean`: twelve executable checks, including beta, eta, large elimination, and dependent-context lookup.
- [Candidate computational goal](algorithm-goal.md) and [source review](source-review.md): statement design and remaining audit obligations.

Contexts use newest-first lists. Declarative judgments express inhabitation in `Prop`; this does not reproduce the Agda development's foundational-strength claim about avoiding K.

The algorithm's fuel bounds recursive call depth. It is not a runtime bound or a polynomial complexity certificate. Well-formed inputs are the intended domain of its future correctness theorem. A bounded run on malformed syntax is not a type-checking result.

## Build

From this directory:

```sh
lake build
lake env lean AlgorithmChecks.lean
```

Compilation verifies that the definitions are accepted by Lean. It does not establish source correspondence, soundness, completeness, or the existence of sufficient fuel for every well-formed comparison. Those obligations remain open. There are no theorem placeholders in the library.

See the [handover](../../HANDOVER.md), [source plan](../../docs/abel-mission-plan.md), and [catalogue intake](../../docs/prove2me-intake-2026-10-30.md) for scope and next steps.
