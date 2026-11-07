# M4 Rule Audit: Atkey's Polynomial-Time QTT and an Intensional Core

Updated 7 November 2026. This audit carries out the parallel item of the roadmap's first work package: record precisely which M4 rules can be interpreted in the proposed intensional core and which require replacement. It prepares [Paper B](formalization-roadmap.md#paper-b-feasible-dependent-types-without-equality-reflection).

It is a source and design audit, not a proof. Claims marked *inference* follow from the cited rules but have not been checked formally.

## Findings

1. **Equality reflection blocks checking, not closed-program extraction.** The pinned M2 artifact already contains Atkey's equality discipline as an optional rule.
   - `Definition/Typed.agda` has the rule `equality-reflection`, enabled by the type restriction `Equality-reflection`.
   - The conversion decision module `Definition.Typed.Decidable.Equality` takes `⦃ no-equality-reflection : No-equality-reflection ⦄` as a module parameter. So do some canonicity results, such as `canonicity-Only-Level-or-U`.
   - Closed-program extraction soundness, `Soundness₀.soundness-ℕ`, is proved for arbitrary type restrictions. Its assumption `No-equality-reflection or-empty Δ` is discharged by `ε` in `fundamental-assumptions⁻₀`.

   Atkey's `Id-Reflect` has an erased premise, and M2's typing judgment is grade-agnostic, so the two rules correspond. Paper B must drop reflection to obtain decidable checking, which is clause 1 of the central theorem. Extraction correctness for closed programs is not what fails.

2. **Grades alone do not give feasibility.** M2's natural numbers have a runtime `suc`. With closed recursion branches and an induction hypothesis used once, iterating a doubling function computes $2^n$ (failure test F1). M3's resource-correctness theorem says evaluation never overdraws heap grades; it does not bound the number of steps. Feasibility must come from Atkey's iteration discipline, which has either no runtime constructors (Cons-free) or constructors paid for with diamonds (LFPL).

3. **The source's polynomial-time theorems are mechanised over semantic morphisms only.** The artefact proves `poly-time` for every model morphism `` f : ℕ ⊢ `nat ⇒ X ``. It does not contain:
   - the QTT syntax or typing rules;
   - the construction of the full QTT model (§5.3), which the paper says is "currently unmechanised";
   - the interpretation of typing derivations into the model.

   A Lean M4 mission whose main goal concerns syntactic terms must construct these parts.

4. **The source theorems fix a narrow interface.**
   - Theorems 6.1 and 6.2 take one runtime input of unary type `Nat`.
   - The realiser is existentially quantified.
   - The cost model is a unit-cost call-by-value closure machine.
   - The paper claims completeness (abstract, §7) but proves no completeness theorem for its dependent systems.

   FP over binary words, a fixed extraction function, a bit-cost model and completeness are additional obligations for the programme.

5. **Recommendation: build Paper B's first core on the LFPL variant.** Its recursor has β-rules in both fragments, and they preserve usage. It needs no `dupNat`. The Cons-free variant's equation $\mathrm{dupNat}(M) \equiv (M,M)$ holds only in the erased fragment. Used as a typed reduction, it would break M2-style usage preservation (rule table, row 12).

## Source pins

| Item | Pin |
|---|---|
| Paper | Robert Atkey, *Polynomial Time and Dependent Types*, Proc. ACM Program. Lang. 8 (POPL 2024), Article 76, DOI [10.1145/3632918](https://doi.org/10.1145/3632918). Extended version [arXiv:2307.09145v2](https://arxiv.org/abs/2307.09145v2) (14 November 2023, 37 pages, PDF SHA-256 `44abdee62d09d7682fc7c1f6b81871b36eccaa4ef0d46d4aa76d1cd4227b8e5a`). Section, theorem and appendix numbers below refer to this version. |
| Agda artefact | [`bobatkey/qtt-models`](https://github.com/bobatkey/qtt-models), tag `popl-2024-artefact-submission`, commit [`76fdbacd6e7bee19cb448b4d41bc21ac3687d63e`](https://github.com/bobatkey/qtt-models/tree/76fdbacd6e7bee19cb448b4d41bc21ac3687d63e). Also archived as Zenodo DOI [10.5281/zenodo.8425923](https://doi.org/10.5281/zenodo.8425923). It targets Agda 2.6.2.2 and standard library 1.7.1. `ConsFree`, `LFPL`, `IndexedLinear` and `AmortisedModel.Machine` use `--safe`. |
| Comparison artifact | M2's [`graded-type-theory`](https://github.com/graded-type-theory/graded-type-theory/tree/75c23df3b1421184cffe35ffd492bb9743dff240) at the pinned commit `75c23df3b1421184cffe35ffd492bb9743dff240` (tag `jfp-submission-2026-04-30`), as in the [Abel mission plan](abel-mission-plan.md). |

## What the source establishes

| Result | Statement (abridged) | Mechanised in the artefact |
|---|---|---|
| Figure 1, §5.1 | Untyped call-by-value λ-calculus with de Bruijn environments and costed big-step semantics $E,\eta \Downarrow_k V$. Every rule costs one unit. Application passes the invoked closure to itself, which permits recursion. | `AmortisedModel.Machine` |
| Definitions 5.1–5.4, §6.1 | Resource monoids, `MaxPoly` (Cons-free) and `PlusPoly` (LFPL), and iteration resource monoids. | `Algebra.ResourceMonoid.*`, `Data.Polynomial.*` |
| Proposition 5.6 | Realisers form an indexed linear preorder with $I$, $\otimes$, $\multimap$, $!_n$ and $\forall_B$. | `AmortisedModel.*` |
| §5.3, items 1–8 | Construction of a QTT model from an indexed linear preorder. Identity types and universes are interpreted "as normal in Set" with a trivial realisability component. $R(A)$ is interpreted as the subset of realisable elements. | **No.** The paper says this is "currently unmechanised". Its introduction says the technical content of these sections has been formalised; read that statement with this caveat. |
| Theorem 6.1 | Cons-free system: if $n :^1 \mathrm{Nat} \vdash M :^1 T(n)$, there are a realising expression $E$ and a polynomial $p$ such that for every $n$, $E,[\mathrm{natValue}(n)] \Downarrow_k v$ with $k \le p(n)$, and $v$ realises $[\![M]\!](n)$. | `ConsFree.poly-time`, for model morphisms `` ℕ ⊢ `nat ⇒ X `` only |
| Theorem 6.2 | LFPL system: as Theorem 6.1, with $k \le p(n+1)$. | `LFPL.poly-time`, for model morphisms only |
| Completeness | Claimed for both systems (abstract; §7). Informal arguments are given only for the simply typed systems (§2.3, §2.4, the latter citing Aehlig and Schwichtenberg). | No theorem |
| Type checking | Not addressed. §7.2 asks whether polynomial-time type checking is possible. | None |

The input encoding is a unary chain: $\mathrm{natValue}(0)=(\mathrm{true},*)$ and $\mathrm{natValue}(1+n)=(\mathrm{false},\mathrm{natValue}(n))$. Bounds are polynomials in $n$, which is the input length for this encoding. §4.2 deliberately takes arbitrary types as problem domains rather than bit strings.

## Rule-by-rule classification

Atkey's term judgment is $\Gamma \vdash M :^\sigma S$ with $\sigma \in \{0,1\}$:
- $\sigma = 0$ is the erased fragment, where "all the normal rules of type theory apply";
- $\sigma = 1$ is the runtime fragment.

Types are formed in $0\Gamma$, and `Conv` uses type equality in $0\Gamma$. M2 instead has one grade-agnostic typing judgment and a separate usage relation $\gamma \mathbin{▸}[m]\, t$ with modes $\mathbf 0^m$ and $\mathbf 1^m$. Atkey's admissible 0-ing rule corresponds to mode $\mathbf 0^m$.

This audit assumes the M2-style design. A rule restricted to the erased fragment becomes an ordinary typing and conversion rule together with a usage rule that is unavailable in mode $\mathbf 1^m$. Under this design, one conversion relation (the erased-fragment one) suffices for type checking.

Status labels:
- **Keep:** normalization and decidable conversion are already proved in M1 or in the pinned M2 artifact. The usage annotations still have to be transcribed.
- **Extend:** new syntax that fits the M1 logical-relation method but has no existing decidability proof. This is a Paper B obligation.
- **Replace:** incompatible with decidable conversion.
- **Optional:** not needed for Paper B's extraction theorem.

| # | Atkey rule (section) | Paper B status | Notes |
|---|---|---|---|
| 1 | Structural rules `Emp`, `Ext`, `Var`, `Conv`, `Sub`, and 0-ing (§3.1.2; App. A.1, A.4) | Keep | `Sub` is affine weakening along the reverse order. 0-ing is mode $\mathbf 0^m$. |
| 2 | Usage semiring: ℕ with the reverse order and no ω (§3.1.1) | Keep, with a check | M2's `Modality` requires a grade ω with `ω≤𝟙` and `ω·+≤ω·ʳ : ω · (p + q) ≤ ω · q`. Under Atkey's order ($m \sqsubseteq n$ iff $m \ge n$), any ω ≥ 1, such as ω = 1, appears to satisfy both laws (*inference*). This does not make ω unrestricted, so the recursor's usage rule must be Atkey's.<br><br>M3 shows that GLB-based `natrec` usage needs ∞ in ℕ (`Graded.Modality.Instances.Nat.¬nrᵢ-GLB`). Atkey's recursor avoids this: its branches use only erased free variables, so the usage of `rec` is the scrutinee's usage. M2's `Linearity-like-nr-for-𝟙` gives the same value, $(\mathbf 1 + p) \cdot n$ with $p = \mathbf 0$, when $z = s = \mathbf 0$. |
| 3 | Π: `Ty-Pi`, `Tm-Lam`, `Tm-App`; β and η in both fragments (§3.1.3; A.5) | Keep | M1 has Π with β and η. Atkey's side condition $\sigma' = 0 \Leftrightarrow (\rho = 0 \lor \sigma = 0)$ is M2's argument mode. |
| 4 | Σ / ⊗: pairs at σ; `fst`, `snd` and η only at σ = 0; `let (x,y)` with β at σ (§3.1.3; A.6) | Keep, with a design check | Atkey's ⊗ combines strong-Σ features in the erased fragment (projections, η) with a weak-Σ eliminator (`let`) at runtime. M2 provides these as two type formers: strong Σ with projections and η, and weak Σ with `prodrec`.<br><br>The safe choice is weak Σ with `prodrec`, deriving projections in mode $\mathbf 0^m$; erased-fragment η then becomes a propositional equality. Keeping definitional η alongside a runtime `prodrec` requires checking that M2's conversion and usage results still hold. |
| 5 | Unit $I$: `let * = M in N` at σ; η only at σ = 0 (§3.1.3; A.6) | Keep | M2's weak unit `Unitʷ` with `unitrec`. The type variant `η-for-Unitʷ` adds η (`Definition/Typed/Variant.agda`). |
| 6 | Id formation; `refl` at σ (§3.1.4; A.7) | Keep | M2's `Id` and `rfl`. |
| 7 | `Id-Reflect`: $\Gamma \vdash N :^0 M_1 =_S M_2$ gives $\Gamma \vdash M_1 \equiv M_2 :^0 S$ (§3.1.4; A.7) | **Replace** with J | This is M2's optional `equality-reflection` (Finding 1). The source model interprets Id in Set, which also validates J. A runtime transport along an erased proof can then plausibly be realised by the identity (*inference*; it depends on the unmechanised §5.3 model). |
| 8 | `Id-Uniq`: $0\Gamma \vdash P :^0 M =_A M$ gives $P \equiv \mathrm{refl}(M)$ (§3.1.4; A.7) | **Replace** with K, or omit | This is definitional uniqueness of identity proofs. Neither M1 nor M2 proves decidable conversion with it. M2 offers the K rule under the restriction `K-allowed`, and the decision module's parameters do not exclude K.<br><br>Abel and Coquand (*Failure of Normalization in Impredicative Type Theory with Proof-Irrelevant Propositional Equality*, LMCS 2020) show that definitional proof irrelevance for equality breaks normalization in the presence of an impredicative universe. The predicative case would be a new obligation. |
| 9 | Universe U (Russell style), `El`, codes for Bool and ⊗ (§3.1.5; A.8) | Keep (M1), then Extend | M1 has one Russell universe with large elimination. Each new type former needs a code and a logical-relation case. The source elides most code rules, so Paper B must state them. Codes carry usage annotations. |
| 10 | Bool and dependent `if` at σ; introduction in $0\Gamma$ (§3.2.1; A.9) | Extend | A routine closed inductive type. |
| 11 | List(T): `nil`, `cons` and `match` at σ; `recList` only at σ = 0 (§3.2.2; A.10) | Extend | The source says it permits "matching without recursion in the σ = 1 fragment". In the M2-style design, `recList` is an ordinary eliminator whose usage rule exists only in mode $\mathbf 0^m$. |
| 12 | Cons-free Nat (§3.3; A.11): `zero` and `succ` only at σ = 0; `dupNat`, with $\mathrm{dupNat}(M) \equiv (M,M)$ only at σ = 0; `rec` with $n :^0$, branches in $0\Gamma$, β only at σ = 0 | Extend, with a conflict | The paper states the `dupNat` equation only at σ = 0, where it is well typed because 0 + 0 = 0. As a typed weak-head reduction, $\mathrm{dupNat}(M) \Rightarrow (M,M)$ would double the usage of $M$.<br><br>That breaks M2-style usage preservation (M2 Theorem 5.4), whose reduction relation is also the one the conversion algorithm normalizes with. This variant would need separate conversion and runtime reductions. |
| 13 | LFPL ◇ and Nat (§3.4; A.12–A.13): ◇ introduction and η only at σ = 0; `zero(d)` and `succ(d, n)` at σ; `rec` with $d :^\sigma$, $n :^0$, $p :^\sigma$; β in both fragments | Extend (recommended core) | ◇ behaves as a unit type for conversion but has no runtime introduction. β substitutes the scrutinee's tail twice, once at grade 0 and once at grade σ, so it preserves usage (§3.4). This is the closest match to M1's and M2's `natrec`. |
| 14 | Realisability reflection $R(A)$ and $R^{-1}$; $R(R^{-1}M) \equiv M$ in both fragments, $R^{-1}(R(M)) \equiv M$ only at σ = 0 (§3.5; A.14) | Optional | Used for internal statements such as $\mathrm{PTIME}(A, P)$ (§4.2). It is the only rule through which runtime-fragment equality enters erased-fragment conversion (§3.5, "by congruence"), so keeping it as stated needs a second conversion relation.<br><br>Candidate simplification: congruence via erased-fragment equality. The §5.3 interpretation of $R(A)$ as a subset of the Set component appears to validate this (*inference*). |
| 15 | Non-iterable `ND(A)` and `Dist(A)` (§4.3) | Optional | NP and BPP characterisations, outside Paper B's target. |
| 16 | `IList` via `rec` into U (§4.1) | Keep (derived) | The large-elimination pattern already exercised in M1's `AlgorithmChecks.lean`. |

## Interface obligations beyond the rules

**Runtime inputs.** M2's soundness theorems cover closed programs (`Soundness₀`) and programs whose free variables are all erased ($\mathbf 0^c \mathbin{▸} t$). Atkey's theorems concern a program with one runtime input variable, which is supplied to the realiser as a machine value.

In the LFPL variant, a closed instance at a concrete numeral is not even typable at σ = 1, because the numeral's diamonds can only be introduced at σ = 0 (*inference* from §3.4). Paper B therefore needs an extraction theorem for open programs with runtime inputs.

**A fixed extraction function.** Theorems 6.1 and 6.2 assert that some realiser exists, constructed from the model interpretation. Paper B's completion condition requires the bound to concern *the* extraction function. Paper B must therefore:
- define extraction, as M2-style erasure followed by compilation of `rec` to self-referential closures;
- prove that the extracted program simulates the model's realiser.

**Machine.** Atkey's machine is a unit-cost call-by-value closure machine, which is the target style the roadmap prefers for Paper A. Adopting it as Paper A's target, extended with representations for ◇ and Nat, would let Papers A and B state bounds about the same machine.

Relating it to a bit-cost model remains open. A candidate starting point is Dal Lago and Martini, *The Weak Lambda Calculus as a Reasonable Machine* (TCS 2008); it has not yet been compared with this machine.

**Words and outputs.** For FP over $\{0,1\}^{*}$ the core needs an iterable word input type. §6.3 remarks that the iterator proofs could be adapted to any finitely branching inductive type, but states no theorem.

In the LFPL variant, runtime `Nat` outputs cannot exceed the input's size potential: ◇ has no runtime introduction, and `PlusPoly` adds sizes (§6.3, items 1–3). Iterable outputs are therefore non-size-increasing (*inference*). Lists are non-iterable and constructible at σ = 1 (§3.2.2), so FP outputs should be non-iterable words.

**Completeness.** Paper B must prove completeness for its chosen dependent core. Starting points are the source's simply typed arguments: nested `dupNat` iteration (§2.3) and the Aehlig–Schwichtenberg iterators (§2.4).

## Failure tests for the first Paper B experiment

**F1: doubling iteration.** Let

$$
f = \lambda m.\,\mathrm{natrec}\;m\;0\;(\lambda\,\mathit{ih}.\,\mathrm{suc}(\mathrm{suc}\;\mathit{ih})),
\qquad
g = \lambda n.\,\mathrm{natrec}\;n\;1\;(\lambda\,\mathit{ih}.\,f\;\mathit{ih}).
$$

Every variable is used at most once, and all branches are closed. For a modality satisfying `Linearity-like-nr-for-𝟙`, M2-style usage therefore accepts $g$ with the usage of $n$ alone; this should be checked against the pinned `nr` instances. Yet $g(n)=2^n$, and evaluation takes $\Theta(2^n)$ steps.

Atkey's rules reject $g$. The Cons-free system has no runtime `succ`. In LFPL, each doubling step needs two diamonds but receives one.

**F2: erased clock.** An erased `Nat` cannot drive runtime iteration, because `rec` requires its scrutinee at the ambient grade ($\Gamma \vdash M :^\sigma \mathrm{Nat}$). The Lean rules must preserve this.

**F3: conversion versus usage.** No reduction used by conversion may change the usage of a runtime term. Test `dupNat` (row 12) and every erased-fragment-only equation that is implemented as a reduction.

## Consequences for the programme

- **Research proposal.** The proposal's statement that Atkey's complexity result cannot simply be combined with a conversion-decision theorem is confirmed. Finding 1 locates the conflict precisely: in M2 it is a single optional rule, and only checking and open-context results depend on its absence.
- **Paper A.** Paper A's resource theorem cannot by itself yield polynomial time; F1 is a concrete witness. The roadmap already states that resource access counts are not time bounds.
- **M4 mission scope.** Keep equality reflection in M4, for fidelity to the source; the intensional variant belongs to Paper B. Proposed milestones:

  | Milestone | Content | Agda guide in the artefact |
  |---|---|---|
  | M4.0 | The Figure 1 machine | Yes |
  | M4.1 | Resource and iteration monoids | Yes |
  | M4.2 | Proposition 5.6 | Yes |
  | M4.3 | The QTT model of §5.3 | No |
  | M4.4 | QTT syntax and typing (Appendix A), and their interpretation | No |
  | M4.5 | Theorems 6.1 and 6.2 for syntactic terms | No (the iterator lemmas have guides) |

  M4.0 is formalized in [`formalization/atkey2024`](../formalization/atkey2024/README.md). It adds a determinism theorem for value and cost, an evaluator proved to compute exactly the evaluation relation, and an exact linear cost bound for a recursive traversal of unary input.

- **First Paper B experiment.** Add LFPL `Nat`, ◇ and the recursor to an M1-style logical relation, with intensional Id and J. Keep F1–F3 as regression tests. This refines [proof idea 2](proof-ideas.md#2-recover-feasibility-with-intensional-equality).

## Open checks

- The rule bodies in Appendix A.10–A.13 (list-recursor β, and `Nat` and ◇ formation) were not compared line by line with the main text.
- The claims marked *inference* need proofs: ω = 1 in M2's `Modality`; the Set-model validation of J, K and the simplified $R$-congruence; and non-size-increasing LFPL outputs.
- Whether the pinned M2 `nr` instances accept F1.
