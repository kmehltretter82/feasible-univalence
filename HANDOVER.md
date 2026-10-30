# Handover: feasible univalence and Abel missions

**Paused at the user's request, 30 October 2026.** Resume substantive work only when the user resumes the task. The pause includes allowing the current agents to finish, checking their output, and committing/pushing this checkpoint.

## Objective and scope

Prepare Prove2Me missions and the three intermediate-paper plans in [the roadmap](docs/formalization-roadmap.md), leading toward the research proposal *Feasible Univalence*. Preserve the full programme; the first Lean prototype does not complete it.

This workstream focuses on Abel's papers. Another agent handles Schwichtenberg papers. Coordinate before duplicating related missions.

## Existing results and decisions

- The [live catalogue survey](docs/prove2me-intake-2026-10-30.md) found no matching entries for the selected Abel sources. Repeat the search before creating a proposal.
- Hofmann–Moser's resource-analysis mission is marked proved, including all six milestones. Review it for reuse; do not reprove the completed targets. Its Lean environment differs from the current default.
- The groupoid and general PTS missions do not supply the first Abel conversion theorem. Neither is required to begin the selected source formalization.
- Work through M1 conversion, M2 graded erasure, and M3 graded recursion. Read M11, *Compiling Programs with Erased Univalence*, now for prior work. Its compilation result assumes Conjecture 4.1; preserve that conditional scope.
- Plans for Papers A–C are already published. Their research theorems remain conjectural targets, not completed or novelty-certified results.

## Checkpoint

The standalone [Lean project](formalization/abel2018/README.md) contains draft syntax, declarative judgments, and an executable fuel-bounded comparison prototype. It is based on the pinned Agda commit recorded in [the Abel mission plan](docs/abel-mission-plan.md). These definitions are candidates under review, not author-approved frozen declarations. The [candidate goal](formalization/abel2018/algorithm-goal.md) and [source review](formalization/abel2018/source-review.md) capture the important statement-design findings.

No Prove2Me proposal, theorem, definition, or proof has been uploaded by this workstream. No proof of the conversion theorem or of the logical relation is present.

## Verified at the pause checkpoint

- `lake build` in `formalization/abel2018` completed successfully with Lean 4.33.1.
- `lake env lean AlgorithmChecks.lean` passed all twelve executable checks.
- The committed Lean sources contain no proof holes, custom axioms, noncomputable definitions, or unsafe declarations.
- Local documentation links and Markdown fences were checked. Build artifacts and credentials are excluded from the commit.
- All three contributing agents finished their current tasks; no proof worker or platform verification job remains running from this workstream.

These checks validate compilation and the listed examples. They do not certify the source translation or prove the main theorem.

## Resume sequence

1. Build the checkpoint with `cd formalization/abel2018`, `lake build`, and `lake env lean AlgorithmChecks.lean`. Read its implementation notes and source review before editing.
2. Audit the syntax and all declarative rules against the pinned artifact. Pay particular attention to context order, substitution into the recursor motive, the step-argument type, and typed reflexive reduction.
3. Add the six source algorithmic relations as actual inductive definitions. They are not yet represented by a separate relational module. Prove the correspondence between these relations and the executable comparison functions.
4. Review the computational target. **Existence of one correct successful fuel value is insufficient.** Require correctness of every successful run as well as convergence on well-formed inputs, or prove an adequate stability result first. Neutral comparison chooses a representative type; the source's relational variable rule allows converted types. Do not require syntactic equality with every admissible inferred type.
5. Construct the logical relation and its Lean replacement for induction-recursion. Prove the required binding, weakening, and substitution results on the actual syntax. Do not assume normalization or a sound complete decider as an input to the main theorem.
6. Prepare the source-linked mission items and independent blind read-backs, using the Prove2Me skill. A private editable draft is permissible; human self-audit/submission is a later platform step, after the package is concrete and reviewable. Do not request that step for this checkpoint.
7. Continue M2/M3 and the three-paper programme with explicit translations between differing calculi and cost models.

For the main theorem, use an actual executable procedure or an explicit computation semantics. A classical proof of `Nonempty (Decidable P)` does not formalize the paper's algorithm. Do not assert total decision of typability for arbitrary raw terms.

## Repository hygiene

Keep downloaded papers, credentials, raw catalogue dumps, generated binaries, and private staging files out of this public repository. Preserve the upstream MIT notice for translated code. Do not mutate another agent's Lean cache or source workspace. Check current remote state before pushing.
