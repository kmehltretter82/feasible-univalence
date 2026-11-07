# Computational Statement and Proof of Theorem 4.12

This document records the computational statement of Theorem 4.12 against the executable conversion-checking algorithm in [`Abel2018/Algorithm.lean`](Abel2018/Algorithm.lean), proved without `sorry` or classical choice in [`Abel2018/Decidable.lean`](Abel2018/Decidable.lean) (`theorem_4_12_computational`).

## Main Theorem (`theorem_4_12_computational`)

The proved main theorem in [`Abel2018/Decidable.lean`](Abel2018/Decidable.lean) establishes **both** clauses below as a single conjunction:

```lean
theorem theorem_4_12_computational :
    (∀ (Γ : Context) (A B : Term), TypeWf Γ A → TypeWf Γ B →
      (∃ fuel b, compareTypeUp fuel Γ A B = some b) ∧
      (∀ fuel b, compareTypeUp fuel Γ A B = some b →
        (b = true ↔ TypeEq Γ A B))) ∧
    (∀ (Γ : Context) (t u A : Term), HasType Γ t A → HasType Γ u A →
      (∃ fuel b, compareTermUp fuel Γ t u A = some b) ∧
      (∀ fuel b, compareTermUp fuel Γ t u A = some b →
        (b = true ↔ TermEq Γ t u A)))
```

Its two halves are also exposed individually as:
- `compareTypeUp_decides_typeEq` (type conversion adequacy and all-run correctness)
- `compareTermUp_decides_termEq` (term conversion adequacy and all-run correctness)
- `dec : TypeWf Γ A → TypeWf Γ B → TypeEq Γ A B ∨ ¬ TypeEq Γ A B` (Theorem 4.12, type clause)
- `decTerm : HasType Γ t A → HasType Γ u A → TermEq Γ t u A ∨ ¬ TermEq Γ t u A` (Theorem 4.12, term clause)

## Why Both Clauses (Convergence + All-Run Correctness) Are Essential

1. **Finite-fuel termination on well-formed inputs:** The existential clause `∃ fuel b, compare*Up fuel ... = some b` proves that on every well-formed type pair (or well-typed term pair at a common type), some finite recursion-depth budget returns a definitive Boolean answer (`some true` or `some false`) rather than exhausting fuel (`none`).
2. **All-successful-run correctness:** The universal clause `∀ fuel b, compare*Up fuel ... = some b → (b = true ↔ ...)` guarantees that *every* fuel budget that produces `some b` returns the exact truth value of judgmental equality (`TypeEq` / `TermEq`). A weaker existential-only statement (`∃ fuel b, run fuel = some b ∧ (b = true ↔ ...)`) could conceal an earlier wrong `some false` or `some true` answer at a smaller fuel value; proving global fuel monotonicity (`compare*_mono` in [`Abel2018/Conversion.lean`](Abel2018/Conversion.lean)) and propagating correctness across all successful runs (`compareTypeUp_all_runs_correct`, `compareTermUp_all_runs_correct`) rules out any discrepancy between budgets.
3. **Constructive proof (`[propext]` only):** `#print axioms Abel2018.theorem_4_12_computational` confirms that the proof depends solely on `[propext]` — neither `Classical.choice` nor `Quot.sound` is used.

## Neutral Inference and Expected Neutral Types

- `compareNeutralUp` selects the canonical context-lookup type (`lookupType Γ x`) for variables. Because the declarative neutral variable rule admits converted variable types, `uniqueNeUp` and `uniqueNeDown` in [`Abel2018/Decidable.lean`](Abel2018/Decidable.lean) prove uniqueness of inferred neutral types up to `TypeEq`, and `compareNeutralUp_adequate` / `compareNeutralDown_adequate` relate `some (some T)` to `ConvNeUp Γ k l T` / `ConvNeDown Γ k l T` and `some none` to `∀ T, ¬ ConvNe* Γ k l T`.
- In accordance with the POPL 2018 paper and Agda artifact (`ne-ins`), `compareTermDown` at a neutral expected type `N` checks `neutralHead N && neutralHead t && neutralHead u` and delegates to `compareNeutralDown` without recursively comparing the inferred type `M` against `N`; compatibility follows from neutral type uniqueness (`neTypeEq`, Theorem 3.33).

No fuel-to-runtime or polynomial complexity claim is made by this theorem.
