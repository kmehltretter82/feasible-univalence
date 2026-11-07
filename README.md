# Feasible Univalence

Research notes, proof ideas, and a Lean 4 formalization roadmap for univalent reasoning and certified polynomial-time programs.

The central question is whether a single dependent type theory can support abstract univalent reasoning, decidable conversion, correct erasure, and extraction of programs with certified execution bounds.

**Status:** active, November 2026. The repository contains the research plans and **27,423 lines of zero-`sorry`, constructive (`[propext]` / `[Quot.sound]` only, zero `Classical.choice`) Lean 4.33.1 formalizations** across [`formalization/abel2018/`](formalization/abel2018/README.md) and [`formalization/atkey2024/`](formalization/atkey2024/README.md):
- **Direct paper ports:** **M1** ([POPL 2018 conversion decidability](formalization/abel2018/README.md), 14 modules, 12,979 lines), **M2** ([graded dependent erasure](formalization/abel2018/FeasibleUnivalence/Erasure.lean), 3 modules, 5,866 lines), **M3** ([graded recursion and heap machine](formalization/abel2018/FeasibleUnivalence/HeapMachine.lean), 3,999 lines), and **M4.0** ([Atkey's POPL 2024 costed machine](formalization/atkey2024/README.md), 492 lines), alongside the [M4 rule audit](docs/atkey-rule-audit.md) and [Abel mission plan](docs/abel-mission-plan.md).
- **Formalized models of the research stages (Gates G2–G6):** [**Paper A**](formalization/abel2018/FeasibleUnivalence/PaperA.lean) (target closure-and-heap machine simulation and resource conservation after erasure, 1,609 lines), [**Paper B**](formalization/abel2018/FeasibleUnivalence/PaperB.lean) (stratified Bellantoni–Cook / Atkey safe recursion core over binary words with static polynomial certificates and intensional `Id`/`J` transport, 762 lines), [**Paper C & M11**](formalization/abel2018/FeasibleUnivalence/PaperC.lean) (cryptographic transport obstruction, Cartesian cubical fragment with quantitative `V`-type equivalences, and `ListMap`/`TreeMap` representation transfer, 1,092 lines), and the [**Final Synthesis**](formalization/abel2018/FeasibleUnivalence/Synthesis.lean) (quantitative gluing and $\Pi\Sigma$ polynomial witness extraction, 435 lines). See the [handover](HANDOVER.md) and [source review & scope audit](formalization/abel2018/source-review.md) for the exact scope boundaries distinguishing the direct Agda ports from the stratified models.

## Read the programme

| Document | Contents |
|---|---|
| [Research proposal](docs/research-proposal.md) | Target theorem, its mathematical limits, existing results, and intended applications. |
| [Proof ideas](docs/proof-ideas.md) | Candidate arguments, the hard proof obligations, and ways to test them. |
| [Formalization roadmap](docs/formalization-roadmap.md) | Prioritized source-paper missions, three intermediate papers, and a Prove2Me workflow. |
| [Live Prove2Me intake](docs/prove2me-intake-2026-10-30.md) | Existing missions, observed proof status, reuse limits, and missing Abel candidates. |
| [Abel mission plan](docs/abel-mission-plan.md) | Pinned conversion source, main theorem, milestones, and preparation for the first upload. |
| [M4 rule audit](docs/atkey-rule-audit.md) | Atkey's polynomial-time rules classified against an intensional core with decidable conversion, and the resulting constraints on Paper B. |
| [Contributing](CONTRIBUTING.md) | How to propose statements, report obstacles, and distinguish ideas from checked results. |

## Proposed paper sequence

1. **Resource Correctness Survives Erasure:** connect graded source programs to an extracted runtime with an explicit evaluation strategy.
2. **Feasible Dependent Types without Equality Reflection:** combine polynomial-time expressiveness with decidable conversion and verified extraction in an intensional core.
3. **The Cost of Transport:** identify and verify the resource conditions for computational transport in a cubical fragment.
4. **Feasible Univalence:** establish the combined normalization and quantitative extraction theorem for the resulting calculus.

These are research targets, not assertions of novelty or completed results. Each stage has a separate literature review and theorem checkpoint.

## The intended mathematical result

For a syntactically specified feasible fragment, a checked derivation of

$$
t : \prod_{x:\{0,1\}^{*}}\sum_{y:\{0,1\}^{*}} R(x,y)
$$

should yield a program computing a valid witness and an explicit polynomial bounding its runtime in the input bit length. The same calculus should have decidable definitional equality and a univalent specification layer. Executable representation changes must satisfy resource conditions.

The target first-order function class is **FP**. This does not require efficient proof checking or complete inference of complexity bounds.

## Starting points

The programme builds on [graded dependent erasure](https://arxiv.org/abs/2603.29716), [polynomial-time dependent types](https://bentnib.org/polytime-deptypes.html), [cubical normalization](https://arxiv.org/abs/2101.11479), and [modular abstraction with cost](https://arxiv.org/abs/2502.20496). The roadmap identifies what can be reused, what needs translation, and what remains a new proof obligation.

Prove2Me would host the audited Lean statements and their proof dependencies. Its verification would establish the submitted formal statements; correspondence with the intended mathematics remains a separate review obligation.
