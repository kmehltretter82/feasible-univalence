# Feasible Univalence

Research notes, proof ideas, and a Lean 4 formalization roadmap for univalent reasoning and certified polynomial-time programs.

The central question is whether a single dependent type theory can support abstract univalent reasoning, decidable conversion, correct erasure, and extraction of programs with certified execution bounds.

**Status:** research proposal, October 2026. The combined theorem is a proposed target. This repository currently contains mathematical plans and proof ideas; it does not contain a completed calculus, Lean proofs, or launched Prove2Me missions.

## Read the programme

| Document | Contents |
|---|---|
| [Research proposal](docs/research-proposal.md) | Target theorem, its mathematical limits, existing results, and intended applications. |
| [Proof ideas](docs/proof-ideas.md) | Candidate arguments, the hard proof obligations, and ways to test them. |
| [Formalization roadmap](docs/formalization-roadmap.md) | Prioritized source-paper missions, three intermediate papers, and a Prove2Me workflow. |
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
