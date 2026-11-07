# Feasible Univalence

Research notes, proof ideas, and a Lean 4 formalization roadmap for univalent reasoning and certified polynomial-time programs.

The central question is whether a single dependent type theory can support abstract univalent reasoning, decidable conversion, correct erasure, and extraction of programs with certified execution bounds.

**Status:** active, November 2026. The central theorem is **not** proved. The repository contains the research plans and **54,356 lines of Lean 4.33.1** across [`formalization/abel2018/`](formalization/abel2018/README.md), [`formalization/logrelmltt/`](formalization/logrelmltt/README.md), and [`formalization/atkey2024/`](formalization/atkey2024/README.md). Every declaration has zero `sorry` and depends only on `propext` / `Quot.sound` (no `Classical.choice`, no custom axioms); CI checks this for **all 11,339 declarations**, theorems included, with [`scripts/AxiomAudit.lean`](scripts/AxiomAudit.lean). The files fall into three tiers of very different evidential weight:

1. **Direct paper ports and established complexity theorems:** **M1** ([POPL 2018 conversion decidability](formalization/abel2018/README.md), 15 modules, 13,120 lines, including fuel-free deciders `decTypeEq` / `decTermEq` in [`Decider.lean`](formalization/abel2018/Abel2018/Decider.lean)), **M1+ (`LogrelMLTT`)** ([conversion decidability for extended MLTT with $\Pi, \Sigma, \mathrm{Id}, \mathbb{N}, \mathrm{Unit}, \mathrm{Empty}, \mathcal{U}$](formalization/logrelmltt/README.md), 15 modules, 22,179 lines), **M2** ([graded dependent erasure](formalization/abel2018/FeasibleUnivalence/Erasure.lean), 3 modules, 5,880 lines), **M3** ([graded recursion and heap machine](formalization/abel2018/FeasibleUnivalence/HeapMachine.lean), 3,999 lines), **M4.0** ([Atkey's POPL 2024 costed machine](formalization/atkey2024/README.md), 492 lines), and **BC** ([Bellantoni–Cook 1992 characterization of $\mathrm{FP}$](formalization/abel2018/FeasibleUnivalence/BC/README.md), 7 modules, 4,442 lines: `BC.Fn n m`, deterministic multi-tape Turing machines `BC.TM`, `BC.bc_soundness`, `BC.bc_completeness`, `BC.defFun_eq_FP`), alongside the [M4 rule audit](docs/atkey-rule-audit.md) and [Abel mission plan](docs/abel-mission-plan.md).
2. **Research prototypes (new statements, awaiting independent audit):** [**Paper A**](formalization/abel2018/FeasibleUnivalence/PaperA.lean) (1,609 lines: an erased closure-and-heap target machine simulated in lockstep by the M3 machine, with erased heap slots never accessed) and the repaired [**Paper B**](formalization/abel2018/FeasibleUnivalence/PaperB.lean) (826 lines: stratified first-order word programs `FeasibleProg` / `BCSafeDerivation` with the earlier `boundedTransition` oracle deleted, compiled to `BC.Fn 1 0` and multi-tape Turing machines via `paper_B_tm_soundness`, `paper_B_FP_completeness`, `paper_B_defFun_eq_FP`, and proving `transport_obstruction_xor` in [`PaperC.lean`](formalization/abel2018/FeasibleUnivalence/PaperC.lean) against `BC.FP`).
3. **Interface models / proof skeletons (not evidence for the unified research claim):** the cubical layer of [**Paper C & M11**](formalization/abel2018/FeasibleUnivalence/PaperC.lean) and the [**Final Synthesis**](formalization/abel2018/FeasibleUnivalence/Synthesis.lean). They fix names and the intended shape of statements, but two structural limitations remain:
   - `pi_sigma_quantitative_extraction` assumes its conclusion: `PiSigmaDerivation` takes the witness program and its correctness proof as fields, and the "proof" is a `specTag : Nat`. Nothing is extracted from a typing derivation (violates R4).
   - `feasible_univalence_main_theorem` is a conjunction of results about **four different calculi** (`Abel2018.Term`, `GTerm`, `FeasibleProg`, `CubicalTerm`). No single calculus has all the properties at once, which is what the [research proposal](docs/research-proposal.md) asks for (violates R1).

See the [holy grail plan](docs/holy-grail-plan.md) for the acceptance rules (R1–R6) and the phases that would turn tier 3 into real results, the [handover](HANDOVER.md), and the [source review & scope audit](formalization/abel2018/source-review.md) for detailed scope boundaries.

## Read the programme

| Document | Contents |
|---|---|
| [Research proposal](docs/research-proposal.md) | Target theorem, its mathematical limits, existing results, and intended applications. |
| [Proof ideas](docs/proof-ideas.md) | Candidate arguments, the hard proof obligations, and ways to test them. |
| [Formalization roadmap](docs/formalization-roadmap.md) | Prioritized source-paper missions, three intermediate papers, and a Prove2Me workflow. |
| [Holy grail plan](docs/holy-grail-plan.md) | One calculus, one theorem: honest baseline, non-cheating acceptance rules, design decisions, phases, and risks. |
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
