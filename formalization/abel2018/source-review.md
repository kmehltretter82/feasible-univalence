# Source review for the Abel–Öhman–Vezzosi conversion mission

Review date: 30 October 2026. Scope: the complete 29-page paper and the pinned Agda definitions of raw syntax, typed judgments, algorithmic equality, and the final decision functions. This is a source-informed review, **not** a blind read-back or a certification of the developing Lean files.

## Source identity and exact scope

- Paper: *Decidability of Conversion for Type Theory in Type Theory*, DOI [10.1145/3158111](https://doi.org/10.1145/3158111), author PDF `popl18.pdf`; SHA-256 `9b1e10047c66efa194ff0d5dac406c8ec712b46ba9c0bfc32180eb9f81c88cb0`.
- Artifact: [`mr-ohman/logrel-mltt`, v2.1, commit `eb2b15ab1c4b45923025834d3bb798943cb44b8e`](https://github.com/mr-ohman/logrel-mltt/tree/eb2b15ab1c4b45923025834d3bb798943cb44b8e).
- Object language: raw de Bruijn terms; one Russell universe, dependent function types with eta equality, and natural numbers with dependent recursion, including large elimination. No identity type, Sigma type, erased modality, or cubical feature belongs to this source.
- Main result: Theorem 4.12, p. 23:26, both clauses. It decides equality of well-formed types in the same context and equality of terms at a common type. It is not total type reconstruction for arbitrary raw terms.
- The main artifact functions are `Definition.Typed.Decidable.dec` and `decTerm`. Their inputs contain evidence of well-formedness; their outputs carry either equality evidence or a refutation.

## Review of the proposed fuel interface

A structurally recursive fuel evaluator is a reasonable executable presentation of the source algorithm. It is an implementation choice, not a verbatim transcription of the source's derivation-recursive Agda functions. It needs adequacy theorems linking its runs to the six source relations and typed weak-head reduction.

For each well-formed input pair, the final result must establish **both**:

1. some finite budget returns a Boolean answer;
2. every successful Boolean answer at every budget is correct: it is true exactly when the source judgment holds.

A weaker statement `exists fuel, answer, run fuel input = some answer and Correct answer` can conceal an earlier wrong answer. Searching increasing fuel would stop at that earlier answer. A proved global fuel-monotonicity theorem can support an equivalent formulation, but monotonicity must not remain an assumed property. Budget exhaustion must remain distinct from a negative equality answer.

The final main theorem should quantify over the actual executable function definitions, not over an assumed sound/complete decider. `Nonempty (Decidable P)` or an arbitrary Boolean witness is classically trivial and does not certify the intended computation. Termination of each bounded run alone also does not prove termination of conversion search.

The source promises no polynomial bound on this checker. No bound on checking fuel should be inferred from the later feasible-runtime research goal.

## Definition and algorithm traps

1. **Binding positions.** Only the body of `lam`, codomain of `pi`, and motive of `natrec` bind. The recursor's zero, step, and scrutinee arguments do not bind. All three binding cases must lift substitution.
2. **Context order and lookup.** Reversing snoc contexts into newest-first lists is representationally harmless only when membership and context extension are translated consistently. A stored variable type must be weakened for the newly introduced binder and again for each later binder passed during lookup.
3. **Recursor step type.** The source is `Pi Nat (G -> G[successor(var0)]↑)`. The nondependent arrow itself weakens its codomain. Omitting or doubling this weakening changes the theorem. The `↑` substitution keeps the surrounding predecessor context; it is not the ordinary binder-removing singleton substitution.
4. **Universe.** `U` is a well-formed large type; there is no `U : U` rule. Large elimination is retained. Replacing the universe with an untyped syntactic tag while omitting its rules would remove a central source feature.
5. **Typed reduction.** Source reduction is weak-head, not full compatible beta reduction. Its reflexive closures require a typing/type-well-formedness witness. An untyped reflexive-transitive closure cannot replace them without a proved restriction theorem.
6. **Redundant source premises.** Several typing/equality rules explicitly require domain well-formedness. The paper explains why these premises support induction. Preserve them rather than deleting them because they seem derivable.
7. **Neutral inferred type.** The unrestricted neutral comparison relation can infer any convertible typing of a variable; its output type is not unique as raw syntax. Theorem 4.5's neutral clause asks whether there exists an output type. A lookup implementation may return a canonical type, but its refinement must allow conversion or existential output types.
8. **Expected neutral type.** The term-comparison rule at neutral type `N` intentionally does not compare `N` with the inferred type `M`. The source derives the needed compatibility from Theorem 3.33. An added recursive type comparison is a different algorithm and needs its own termination/refinement argument.
9. **Eta.** Function comparison applies both weakened functions to the fresh variable. Merely comparing lambda bodies, or using alpha/beta equality alone, misses source equality of a neutral function and its eta expansion.
10. **Self-related premises in 4.5.** The algorithmic decision theorem assumes self-comparison evidence in equal contexts. It does not assume the cross-comparison being decided. Restricting to already-equal inputs would eliminate the negative case.
11. **PDF notation.** Barred variables denote weak-head forms, and `n`, `m`, `N`, `M` denote neutrals by convention. Plain text extraction loses bars. In particular, Theorems 3.28–3.30 need these restrictions. The extracted last rule of Figure 6 also displays function typings ambiguously; the pinned Agda `eta-eq` rule explicitly types both functions at `Pi F G`.
12. **Standing context assumptions.** After p. 23:9, well-formed source and target contexts are implicit whenever typed weakenings or substitutions appear. Include them in corresponding Lean theorem signatures or in the faithfully defined relation.
13. **Semantic level of the fundamental lemma.** The relation has levels zero and one, and the universe is reducible only at the upper level. Do not read the schematic level symbol in Theorem 3.21 as an unrestricted universal quantifier over both levels: `U` is well formed but is not a small reducible type. Resolve the precise level parameters from the full pinned fundamental-lemma artifact before drafting that milestone.

## Source milestones and their obligations

| Source | Required content or dependency |
|---|---|
| 2.2–2.5 | Inclusion of typed reduction in equality; subject typing; irreducibility of weak-head forms; deterministic steps and weak-head endpoints. |
| 2.7 | Weakening, with the stated context assumptions and all supported judgment forms. |
| 3.1–3.20 | Logical-relation and validity infrastructure, including independence from semantic derivation choice and substitution lifting. These are proof obligations, not free model assumptions. |
| 3.21 | Fundamental lemma for all five judgments; terms and term equality include the required validity of their type. |
| 3.23 | Fundamental lemma for substitutions in well-formed contexts. |
| 3.24–3.26 | Closed-natural canonicity, dependent-function injectivity, and the full syntactic-validity package. |
| 3.28 | Weak-head normalization of well-formed types and terms; the output must be a weak-head form. |
| 3.31–3.34 | Substitution, composition, uniqueness up to conversion of neutral types, and the stated universe-membership conditions. |
| 3.35 | Impossibility of equality between zero and its successor. |
| 4.1–4.4 | Context change, soundness of all six algorithmic relations, and conversion stability. |
| 4.5 | Algorithmic decidability, including the existential neutral output and the source self-related input premises. |
| 4.6–4.10 | The laws needed for the second generic-equality instance; do not postulate that instance already has them. |
| 4.11 | Completeness for both type equality and equality at a common type. |
| 4.12 | Executable conversion decision for both source clauses. |

This table is a source map; it is not a verified formal dependency graph. The conversion mission should expose the important results as source-faithful theorem items before launch. Prove2Me's private proposal milestones require attached theorem items; this source map alone does not create them. An unimplemented logical relation must be described as unimplemented, rather than replaced by an abstract structure containing the fundamental theorem.

## Metatheory and claim boundary

The Agda proof uses induction-recursion and `--without-K`. Lean can represent the object-language judgments as propositions and verify metatheorems about them; this does not add object-language UIP, since object judgments remain distinct from Lean equality. Nevertheless, a Lean port does not by itself reproduce the source's claim about proof in a metatheory without K.

The source logical relation is defined recursively on semantic type derivations, with an explicit later proof that the result is independent of the chosen derivation. Putting every semantic derivation into Lean `Prop` can prevent the required elimination into data or silently obscure this issue. Construct a supported replacement and justify its source meaning. The paper's conclusion discusses replacing induction-recursion using extra meta-universes, but does not supply that Lean construction.

## Acceptance requirements and current handover

Before treating the first proposal as ready:

- Review the complete actual syntax, judgments, reduction, and comparison definitions against the pinned artifact; record representational changes.
- Compile the executable definitions without `sorry`, custom axioms, unsafe escape routes, or noncomputable decisions.
- Check recursor binding, universe distinctions, beta computation, eta comparison, neutral applications, and negative comparison on well-typed examples. Examples detect mistakes; they do not prove the theorem.
- State and elaborate the actual combined main goal with convergence and all-successful-run correctness; retain the full type and term input domains.
- Include, or explicitly leave open, the evaluator-to-typed-reduction and evaluator-to-algorithmic-relation proofs. They are not granted by compilation.
- Keep logical-relation construction and fundamental-lemma work visible in the mission. Do not claim the paper fully formalized from executable definitions alone.
- Obtain blind read-backs of the final actual items, then perform the separate source comparison and human review required for launch.

At handover, a limited source scan of `Algorithm.lean` checked canonical context lookup and the expected-neutral-type branch. Lookup weakens once per traversed binder, and the neutral branch deliberately accepts an inferred type without comparing it with the expected neutral type. No concrete discrepancy was found in those two branches. This is not a full implementation audit; adequacy and convergence remain proof obligations. No theorem is certified here as proved. The completed review result is the precise target boundary and mismatch checklist above.
