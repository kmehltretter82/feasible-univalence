# Abel papers: source intake and mission preparation

Plan dated 30 October 2026. This workstream prepares the Abel sources for the [formalization roadmap](formalization-roadmap.md). A separate workstream handles Schwichtenberg papers. Exchange theorem interfaces and environment pins between the workstreams before sharing imports.

**First candidate:** Abel–Öhman–Vezzosi, *Decidability of Conversion for Type Theory in Type Theory*, POPL 2018, DOI [10.1145/3158111](https://doi.org/10.1145/3158111).

**Current status:** source and catalogue intake. No Lean declarations have been frozen, no Prove2Me proposal has been uploaded, and no new proof is claimed. This file specifies the preparation work; it is not a launchable mission.

## 1. Fix the first source

Use the [author PDF](https://www.cse.chalmers.se/~abela/popl18.pdf) and the Agda artifact [tag v2.1, commit `eb2b15ab1c4b45923025834d3bb798943cb44b8e`](https://github.com/mr-ohman/logrel-mltt/tree/eb2b15ab1c4b45923025834d3bb798943cb44b8e). Its README identifies the paper and Agda 2.5.3. The older v1.0 tag lacks the conversion modules and is not the selected baseline.

The downloaded PDF's SHA-256 is `9b1e10047c66efa194ff0d5dac406c8ec712b46ba9c0bfc32180eb9f81c88cb0`. Source links and this digest identify the reviewed copy without redistributing the paper.

The object calculus is the paper's lambda-Pi-U-N system: natural numbers with their dependent eliminator, dependent functions with eta equality, and one Russell universe. Keep its typing, judgmental equality, and typed reduction distinct from Lean's own judgments.

## 2. Main goal and milestones

The main goal is **Theorem 4.12, p. 23:26**: decide judgmental equality of two well-formed types in a common context, and of two terms at a common type. Both clauses belong to the same mission.

The corresponding artifact functions are [`dec` and `decTerm`](https://github.com/mr-ohman/logrel-mltt/blob/eb2b15ab1c4b45923025834d3bb798943cb44b8e/Definition/Typed/Decidable.agda). They are computational witnesses, not merely propositions asserting excluded middle.

| Source result | Role in the mission |
|---|---|
| Lemma 2.7 | Weakening for well-formed judgments. |
| Theorem 3.21 | Fundamental lemma for the parameterized logical relation; retain all five judgment forms. |
| Theorem 3.23 | Validity of well-formed substitutions. |
| Theorems 3.24–3.26 | Numeral canonicity, dependent-function injectivity, and syntactic validity. |
| Theorem 3.28 | Weak-head normalization of types and terms. |
| Theorems 3.31–3.32 | Substitution and its composition. |
| Theorem 3.35 | Separation of zero and its successor. |
| Lemmas 4.1–4.3 | Context change and soundness of the algorithmic relations. |
| Theorem 4.5 | Deciding the algorithmic relations under their precise source premises. |
| Theorem 4.11 | Completeness of algorithmic equality. |
| Theorem 4.12 | Main conversion decision result. |

This is a source map, not a formal dependency graph or a complete set of Lean signatures. The full source premises must be transcribed and checked before uploading each item. Technical closure lemmas may be supplied through later decompositions of these milestones.

## 3. Preserve the computational claim in Lean

A statement such as `Nonempty (Decidable P)` can be discharged classically for any proposition. That would not formalize a conversion-checking algorithm. Likewise, assuming a sound, complete decider would remove the main content of the paper.

The Lean deliverable must include an executable decision procedure and proofs of its correctness and termination on the source's well-formed inputs. There are two representation choices to investigate before freezing the goal:

- a program receiving explicit, computationally represented typing certificates;
- a partial algorithm on encoded syntax, with a theorem that it terminates and returns the correct answer on well-formed inputs.

Choose one after a prototype of the source's mutually defined comparison relations. If the Prove2Me goal is propositional, connect it to the actual program or its code and computation semantics. Do not replace that connection with arbitrary existence of a Boolean function. Total decision of typability for arbitrary unannotated terms is not the source target.

The Agda development uses induction-recursion. Its Lean replacement needs a justified construction, not an axiom asserting the desired logical relation. Also record the distinction between proving object-language metatheorems in Lean and reproducing the original proof's foundational-strength claim: Lean's metatheory has proof irrelevance, while the source explicitly works without K.

## 4. Preparation tasks and first proof tasks

1. **Syntax and judgments.** Translate the pinned [`Definition.Untyped`](https://github.com/mr-ohman/logrel-mltt/blob/eb2b15ab1c4b45923025834d3bb798943cb44b8e/Definition/Untyped.agda) and [`Definition.Typed`](https://github.com/mr-ohman/logrel-mltt/blob/eb2b15ab1c4b45923025834d3bb798943cb44b8e/Definition/Typed.agda) concepts. Review binder scope, lifting, substitution into dependent codomains, the universe rules, and the natural-number recursor against the paper's figures.
2. **Computational interface.** Prototype the six relations in [`Definition.Conversion`](https://github.com/mr-ohman/logrel-mltt/blob/eb2b15ab1c4b45923025834d3bb798943cb44b8e/Definition/Conversion.agda) and choose the computational representation above. Use examples involving function eta and dependent recursion to detect a reduced language disguised as the full source.
3. **First bounded proofs.** Establish renaming/substitution identities and composition, substitution under a binder, and weakening (Lemma 2.7). Compare any existing binding library before building these. These tasks must refer to the actual selected syntax.
4. **Logical relation.** Construct the universe-indexed relation and its generic equality interface. Treat the natural-number recursion/congruence case as an early stress test. Then prove the fundamental lemma and its first consequences.
5. **Conversion.** Complete soundness, algorithm termination/decision, and completeness, using the two source instantiations of the logical relation. Close both clauses of the main goal with the same executable algorithm.

For module planning, separate syntax, judgments/reduction, algorithmic equality, logical relations, and consequences. A shared binding layer with M2 is desirable, but its compatibility must be demonstrated. No full PTS-normalization theorem or groupoid-model theorem is required to begin these tasks.

## 5. Subsequent Abel missions

### M2: graded erasure

Pin [arXiv:2603.29716v2](https://arxiv.org/abs/2603.29716v2), the extended 2026 paper, and an artifact matching that version. Use **Theorem 6.9**, operational extraction correctness, as the initial main-goal candidate. The underlying logical result in Theorem 6.8 and the grade-substitution and preservation results in Theorems 5.3–5.4 are substantial milestones.

Preserve the modality hypotheses and the distinction between closed programs and programs in erasable contexts. The source places conditions on erased pair elimination and on consistency when erased empty-type elimination is allowed. The extensions require their own checks. It is not sound to generalize the theorem to arbitrary contexts or modalities from its informal slogan. The 2023 publication and the 2026 extension should be reconciled in a single versioned mission scope.

### M3: graded recursion and resource correctness

Use [the ICFP 2026 paper](https://doi.org/10.1145/3828677) with [the archived artifact](https://zenodo.org/records/21166412). The artifact's `icfp26` reference resolves to [commit `93987e3ddc11f583fc3ecdc05472e1dac4094c4f`](https://github.com/graded-type-theory/graded-type-theory/tree/93987e3ddc11f583fc3ecdc05472e1dac4094c4f).

Before proposal creation, map the exact resource theorem and its modality instances from the complete paper to artifact declarations. The current plan does not invent theorem numbers or replace the machine by an abstract cost counter. The authors' [issue #95](https://github.com/graded-type-theory/graded-type-theory/issues/95) explains the gap to our Paper A: their machine operates on source terms using call-by-name; extraction with removal of erased content and a call-by-value or call-by-need target needs further work.

### M11: erased univalence

Read [Abel–Danielsson–Vezzosi's 2021 draft](https://www.cse.chalmers.se/~nad/publications/abel-danielsson-vezzosi-erased-univalence.html), especially the [extended version](https://www.cse.chalmers.se/~nad/publications/abel-danielsson-vezzosi-erased-univalence-long.pdf), before refining Paper C. SHA-256 of the downloaded extended PDF: `940ae7582e025339fad58170666df6c73a1749bb28b5b64919c5ecf0853f7881`.

Its CTT0ω calculus restricts Glue and higher constructors to erased code. Theorem 4.2 provides a logical compilation result and Corollary 4.3 gives agreement on closed runtime naturals, **under Conjecture 4.1**. That conjecture includes forcing/reducibility facts and injectivity/disjointness of canonical forms. These are explicitly unproved in the selected draft.

A faithful mission must retain that conditional scope and expose the conjectured metatheory as open obligations if pursuing an unconditional extension. It must not describe the draft as a completed normalization or polynomial-time theorem. Closing those obligations would be a possible intermediate research target, after checking subsequent literature. Its cubical presentation also needs comparison with the Cartesian calculus currently proposed for Paper C.

## 6. What an upload will contain

Prepare one `ResearchPaper` proposal per selected paper. For M1 the package should include the source/version record, compiled meaning-bearing definitions, the computational goal, source-linked milestones, and independent blind read-backs of the actual Lean items. Use the current supported environment, initially Lean 4.33.1 / Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and recheck it at upload.

The Prove2Me proposal workflow separates editable private drafts from human review and submission. The useful next upload is that reviewable package, rather than a paper title with a classical or axiomatic stand-in for its theorem. This intake creates neither a platform draft nor a claim that such a package is ready.
