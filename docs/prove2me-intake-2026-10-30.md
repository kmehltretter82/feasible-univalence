# Prove2Me intake: existing work and the Abel workstream

Checked 30 October 2026 using the live Prove2Me API. These are catalogue observations and source comparisons, not new proof submissions or independent certifications of existing proofs.

**Recommendation:** prepare the Abel conversion mission first. The existing missions found in this survey do not directly discharge its conversion theorem. Reuse suitable completed work later, and keep the separate Schwichtenberg workstream coordinated through explicit interfaces.

## Existing missions worth tracking

| Existing mission | Observed status | Use for this programme | Recommended action |
|---|---|---|---|
| [Multivariate Amortised Resource Analysis for Term Rewrite Systems](https://prove2.me/missions/40ee9db5-61d6-4ed9-a3af-e640151629f1) — Hofmann–Moser | Main Theorem 16 and all six milestones **Proved**; no open root leaves. | Potential accounting, constructor shifts, and sharing are candidates for a later resource-analysis interface. | Reuse review; do not spend a new proof effort on these completed targets. |
| [The Groupoid Model Refutes Uniqueness of Identity Proofs](https://prove2.me/missions/6dee1b1f-e7c2-4269-818b-ea9047240380) — Hofmann–Streicher | Main goal **Open**; three of four milestones proved. The remaining leaf is `HofmannStreicher1994.uip_underivable`. | Relevant background for intensional identity and avoiding an accidental UIP assumption. It is not a prerequisite for the 2018 conversion calculus. | Coordinate with related work; outside the current Abel assignment. |
| [Weak and strong normalization in pure type systems](https://prove2.me/missions/0a5f8ffb-9869-47b0-b1d8-5822404c30ec) | Main goal **Open**; no milestones, no proof submissions, and the only open leaf is the main goal itself. | Its published syntax contains renaming and substitution definitions worth comparing. | Do not make the general normalization implication a prerequisite. No bounded, already-published supporting theorem was identified here. |

The first row's accepted main proof is submission `c400681e-2518-411d-8fdc-813eed675de7`, recorded as `ACCEPTED`. Its environment is Lean **4.30.0**, Mathlib revision `c5ea00351c28e24afc9f0f84379aa41082b1188f`. The other two roots use Lean **4.33.1**, revision `0df444a360eaa60ab8c11dca51a86af692955474`. Cross-environment reuse requires a checked port; imports cannot simply be mixed.

### What the completed resource result actually supplies

[Hofmann–Moser Theorem 16](https://prove2.me/theorems/421b897d-d831-465c-ba35-e243ea968b95) bounds the steps of an existing innermost evaluation by the decrease of a potential, under its annotated typing and rewrite-system hypotheses. Particularly useful completed components are [Lemma 12](https://prove2.me/theorems/56b47aca-0c96-442c-9104-2a3960bf9711), for constructor shifts, and [Lemma 13](https://prove2.me/theorems/b21cd386-5bd7-4fb1-a982-830f5f645385), for sharing. [Original paper](https://doi.org/10.4230/LIPIcs.TLCA.2015.241).

Our language has dependent types and an erasure compiler, whereas this result concerns constructor rewrite systems. Reuse would need a translation and a simulation relating the counted operations. A potential bound also needs a polynomial-growth argument before it becomes a polynomial-time certificate; the listed theorem alone does not prove termination or the programme's FP characterization.

### Why the PTS mission is not the first proof target

Its `TypeSystemNormalization` definition uses annotated lambda terms, arbitrary sort specifications, and full beta reduction. The Abel source instead includes natural numbers, a Russell universe, function eta equality, and typed weak-head reduction. The binding machinery is comparable, but the typing and equality judgments differ. A lemma proved for the PTS definition cannot be imported as an Abel theorem without a justified connection.

Renaming/substitution composition and reduction stability would be useful small contributions **if** we choose that shared representation. They are suggested future targets, not existing open theorem IDs discovered in this intake. We should first settle the Abel representation rather than create unrelated infrastructure missions.

## Missing Abel candidates, in order

No matching published mission, theorem, or definition was found for these source-specific searches. This is a search result, not a claim that the entire platform has been exhaustively audited.

| Order | Source | Why it belongs here |
|---|---|---|
| 1 — M1 | Abel–Öhman–Vezzosi, [*Decidability of Conversion for Type Theory in Type Theory*](https://doi.org/10.1145/3158111), 2018 | Theorem 4.12 and its constructive algorithm provide the first conversion foundation. |
| 2 — M2 | Abel–Danielsson–Eriksson, [*A Graded Modal Dependent Type Theory with Erasure, Formalized*](https://arxiv.org/abs/2603.29716v2), 2026 extended version | Graded substitution, preservation, and extraction correctness supply the source side of Paper A. |
| 3 — M3 | Eriksson–Abel–Danielsson, [*On Recursion in Graded Modal Type Theory*](https://doi.org/10.1145/3828677), 2026 | Resource correctness for the source abstract machine is the operational baseline that Paper A must extend. |
| 4 — M11 | Abel–Danielsson–Vezzosi, [*Compiling Programs with Erased Univalence*](https://www.cse.chalmers.se/~nad/publications/abel-danielsson-vezzosi-erased-univalence.html), 2021 draft | Essential prior work for Paper C. Its compilation result is conditional on unproved metatheory, so its assumptions require explicit treatment. |

Read M11 now for design and novelty; prepare its formal mission after the basic erasure infrastructure. One paper should have one mission, with companion results as milestones. The 2023 and extended 2026 versions of the graded-erasure paper should not become duplicate missions for overlapping results.

See the [Abel mission plan](abel-mission-plan.md) for the exact first source, theorem map, computational requirement, and upload sequence.

## Scope of the search

The initial mission sweep retrieved all reported pages for 16 topic queries, yielding 3,512 distinct mission IDs. Keyword matches were screened for mathematical relevance; most were unrelated uses of words such as “type”, “conversion”, or “univalent”. Detailed inspection was limited to the candidates discussed above.

Follow-up author/title queries included:

- `Abel Ohman Vezzosi` and `Decidability Conversion Type Theory`;
- `Graded Modal Dependent Type Theory Erasure`;
- `Recursion Graded Modal Type Theory`;
- `Andreas Abel` and `Eriksson Danielsson`;
- `Compiling Programs Erased Univalence`, `Erased Univalence`, and `Abel Danielsson Vezzosi`.

Theorem and definition searches used `env=all`. These targeted Abel queries returned no matching theorem/definition rows; the conversion mission query returned unrelated missions, including the PTS entry above. Broader theorem/definition searches were capped at 50 results per query and are not exhaustive. The platform's fuzzy search can return unrelated words and titles. Repeat the duplicate check immediately before creating each proposal.

No platform theorem, definition, mission, or proof was created during this intake. The next deliverable is the first Abel proposal's actual Lean definitions and computational statement, followed by source review and independent read-backs.
