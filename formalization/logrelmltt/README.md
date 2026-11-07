# LogrelMLTT: Complete Lean 4.33.1 Formalization of Conversion Decidability for Extended MLTT

This directory contains `LogrelMLTT`, a complete, zero-`sorry`, constructive (`[propext]` / `[Quot.sound]` only, zero `Classical.choice`) Lean 4.33.1 formalization of conversion decidability via Kripke logical relations for Martin-Löf Type Theory with `Π`, `Σ`, `Id`, `ℕ`, `Unit`, `Empty`, and one Russell universe `U`.

It ports the full `master` branch of [`mr-ohman/logrel-mltt`](https://github.com/mr-ohman/logrel-mltt/tree/9d6e290064962a1987c9e1a131c2fb967d6ef928) (commit `9d6e290064962a1987c9e1a131c2fb967d6ef928`), which extends the POPL 2018 artifact (`eb2b15ab1c4b45923025834d3bb798943cb44b8e`, formalized in `formalization/abel2018`) with dependent pair types (`Σ`, `prod`, `fst`, `snd` with β and η), the unit type (`Unit`, `star` with η), and the empty type (`Empty`, `emptyrec`), and further extends it with intensional identity types (`Id`, `rfl`, `idrec`/`J` with β-reduction, following the identity type logical relation of [`mr-ohman/graded-modal-types`](https://github.com/mr-ohman/graded-modal-types/tree/63291cd97eb8c4ea65fa0aa0d5a4267f3caaf9a4), commit `63291cd97eb8c4ea65fa0aa0d5a4267f3caaf9a4`).

The library uses core Lean 4.33.1 only; no Mathlib dependency is required. The upstream MIT license is retained in [LICENSE](LICENSE).

## Module Overview

- [`LogrelMLTT/Syntax.lean`](LogrelMLTT/Syntax.lean): Raw de Bruijn terms (`Term`), order-preserving renamings (`Wk`, `wk`), parallel substitutions (`Subst`, `subst`, `subst2`), recursor step types (`recStepType`), numerals (`suck`), and syntactic `Neutral` / `Whnf` / view predicates.
- [`LogrelMLTT/UntypedProperties.lean`](LogrelMLTT/UntypedProperties.lean): Complete renaming and substitution algebra (`wk_comp`, `wk_subst`, `subst_wk`, `subst_comp`, `subst_beta`, `subst_beta_natrec`, `wk_subst2`, `subst_subst2`).
- [`LogrelMLTT/Judgments.lean`](LogrelMLTT/Judgments.lean): Declarative typing (`CtxWf`, `TypeWf`, `HasType`), judgmental equality (`TypeEq`, `TermEq`), typed weak-head reduction (`TypeStep`, `Step`, `TypeStar`, `Star`, `TypeWhnf`, `TermWhnf`), and substitution typing (`SubstWf`, `SubstEq`).
- [`LogrelMLTT/Weakening.lean`](LogrelMLTT/Weakening.lean): Typed context weakening (`WkCtx`) and Lemma 2.7 (`wkTypeWf`, `wkHasType`, `wkTypeEq`, `wkTermEq`, `wkStep`, `wkTypeStep`, `wkStar`, `wkTypeStar`).
- [`LogrelMLTT/TypedProperties.lean`](LogrelMLTT/TypedProperties.lean): Basic properties of typed reduction (`whnfRed*`, `whrDet*`, `subset*`, `redSubst*`) and the generic equality relation interface (`EqRelSet`, `synEqRel`).
- [`LogrelMLTT/Algorithm.lean`](LogrelMLTT/Algorithm.lean): Executable fuel-bounded weak-head normalizer (`whnfFuel`) and six-mode conversion checker (`compareNeutralUp`, `compareNeutralDown`, `compareTypeUp`, `compareTypeDown`, `compareTermUp`, `compareTermDown`).
- [`LogrelMLTT/Conversion.lean`](LogrelMLTT/Conversion.lean): Inductive algorithmic conversion relations (`ConvNeUp`, `ConvNeDown`, `ConvTypeUp`, `ConvTypeDown`, `ConvTermUp`, `ConvTermDown`, `CtxEq`), weakening (`wkConv*`), fuel monotonicity (`whnfFuel_mono`, `compare*_mono`), and `whnfFuel` adequacy on typed WHNF reductions.
- [`LogrelMLTT/LogicalRelation.lean`](LogrelMLTT/LogicalRelation.lean): Kripke logical relation for reducibility parameterized by `EqRelSet`, constructed in Lean 4 without induction-recursion via `LogRelKit : TypeLevel → Context → Term → Type` and `LogRelAt` / `LogRel`.
- [`LogrelMLTT/LogicalRelationProperties.lean`](LogrelMLTT/LogicalRelationProperties.lean): Proof irrelevance / shape transfer (`irrelevance*`), weakening (`wk*`), escape (`escape*`), reflexivity (`refl*`), symmetry (`symm*`), transitivity (`trans*`), conversion (`conv*`), and WHNF expansion (`redSubst*`).
- [`LogrelMLTT/Substitution.lean`](LogrelMLTT/Substitution.lean): Semantic validity of contexts, substitutions, types, and terms (`ValidCtx`, `ValidSubst`, `ValidType`, `ValidTypeEq`, `ValidTerm`, `ValidTermEq`), plus weakening, lifting, single-variable, and two-variable substitution validity.
- [`LogrelMLTT/Fundamental.lean`](LogrelMLTT/Fundamental.lean): Fundamental Theorem (`valid`, `fundamental`, `fundamentalTerm`, `fundamentalEq`, `fundamentalTermEq`), substitution validity (`fundamentalSubst`, `fundamentalSubstEq`), and reducibility (`reducible`, `reducibleTerm`, `reducibleEq`, `reducibleEqTerm`).
- [`LogrelMLTT/Consequences.lean`](LogrelMLTT/Consequences.lean): Syntactic validity (`syntacticEq`, `syntacticTerm`, `syntacticEqTerm`), `Π`-, `Σ`-, and `Id`-injectivity (`injectivity`, `sigma_injectivity`, `id_injectivity`), type constructor disjointness and WHNF agreement, substitution (`substitution`, `substitutionTerm`, `subst2Type`, `subst2TypeEq`), weak-head normalization (`whNorm`, `whNormTerm`), canonicity for `ℕ`, `Unit`, and `Id` (`canonicity`, `canonicity_unit`, `canonicity_unit_red`, `canonicity_id`), non-inhabitation of `Empty` (`noEmpty`), and consistency (`zero_ne_one`).
- [`LogrelMLTT/Completeness.lean`](LogrelMLTT/Completeness.lean): Soundness (`soundness*`), context stability (`stability*`), symmetry and transitivity (`sym*`, `trans*`), reflection/reification (`lift*`, `univConv*`, `convEqRel`), and Completeness of Algorithmic Equality (`completeEq`, `completeEqTerm`).
- [`LogrelMLTT/Decidable.lean`](LogrelMLTT/Decidable.lean): Uniqueness of inferred neutral types (`uniqueNeUp`, `uniqueNeDown`), mutual fuel adequacy (`compare*_adequate`), Decidability of Algorithmic Equality (`decConv*`), Decidability of Judgmental Equality (`dec`, `decTerm`), and executable conversion adequacy (`compareTypeUp_decides_typeEq`, `compareTermUp_decides_termEq`, `theorem_4_12_computational`).
- [`LogrelMLTT/Decider.lean`](LogrelMLTT/Decider.lean): Fuel-free deciders (`findNat`, `decTypeEq`, `decTermEq`, `decideTypeEq`, `decideTermEq`, `decideTypeEq_iff`, `decideTermEq_iff`, `theorem_4_12_decidable`).
- [`AlgorithmChecks.lean`](AlgorithmChecks.lean): Executable `#guard` regression tests and `#check` signature verifications.

## Build and Verification

```sh
lake build
lake env lean AlgorithmChecks.lean
lake env lean --run ../../scripts/AxiomAudit.lean LogrelMLTT
```
