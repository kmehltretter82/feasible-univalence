# Contributing

Contributions can clarify a definition, supply a counterexample, identify prior work, develop a proof, or formalize a precise result.

Distinguish these statuses in every contribution:

- **Established source result:** give a versioned source and the relevant section or theorem.
- **Proof idea:** explain the argument and name the missing obligations.
- **Conjecture:** state the assumptions and conclusion, and describe attempted counterexamples.
- **Formalized result:** identify the exact Lean statement, source correspondence, environment, proof, and dependencies.

A successful Lean check proves the submitted statement. It does not establish that the definitions faithfully encode the source or that a proposed result is new.

For a proposed formalization, first record the source calculus, equality rules, universe levels, evaluation strategy, data representation, and cost model. Audit meaning-carrying definitions as carefully as the headline theorem. State dependencies as lemmas to prove, rather than adding them as new assumptions to the target.

Changes to a source-facing statement must be explicit and versioned. A restricted pilot is useful when clearly identified as a restricted pilot; it does not close a mission for the full source theorem.

Proof-idea notes should explain what would falsify the idea and which bounded lemma should be attempted first. New research papers need a literature comparison beyond this repository's initial survey.

For Prove2Me, use one mission per research paper, with supporting results as milestones. Search for reusable definitions and theorems before proposing duplicates, pin a compatible verification environment, and follow the platform's statement-audit and submission workflow.
