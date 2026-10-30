# Candidate computational statement for Theorem 4.12

This is a proposed statement against the current concrete algorithm. It is not
proved, author-approved, frozen, or submitted to Prove2Me. The executable code
implements the six comparison modes with a recursive-depth budget; the source
does not give this fuel presentation, so its adequacy is an additional obligation
of this Lean implementation.

The intended main theorem has **both** clauses below as one conjunction:

```lean
  (∀ (Γ : Context) (A B : Term), TypeWf Γ A → TypeWf Γ B →
    (∃ fuel b, compareTypeUp fuel Γ A B = some b) ∧
    (∀ fuel b, compareTypeUp fuel Γ A B = some b →
      (b = true ↔ TypeEq Γ A B))) ∧
  (∀ (Γ : Context) (t u A : Term), HasType Γ t A → HasType Γ u A →
    (∃ fuel b, compareTermUp fuel Γ t u A = some b) ∧
    (∀ fuel b, compareTermUp fuel Γ t u A = some b →
      (b = true ↔ TermEq Γ t u A)))
```

The existential fuel establishes termination on every well-formed input. The
universal successful-run clauses prevent an earlier false answer from being
hidden by the existence of a later correct one. A definable search over fuel
would therefore yield the intended partial-on-raw-syntax, total-on-well-formed
conversion procedure once this theorem is proved. This is not a classical
`Nonempty (Decidable P)` claim.

`compareNeutralUp` selects a context-lookup type. The source neutral variable
rule admits other types by conversion; any relational adequacy statement must
allow a convertible output type or existentially quantify it. It must not claim
that all inferred type syntax is identical. The `ne-ins` case intentionally
does not compare this inferred type to the given neutral expected type.

Remaining obligations include source-to-algorithm adequacy, well-formedness of
the intermediate inputs, the logical-relation/normalization development,
eventual convergence, and correctness of every successful positive and negative
answer. No fuel-to-runtime or polynomial complexity claim is intended.
