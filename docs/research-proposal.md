# Feasible Univalence: From Abstract Proofs to Certified Efficient Programs

Research proposal, 30 October 2026.

The main result below is a **research target**, not an established theorem. Its precise calculus, rules, and proof remain to be discovered. The literature establishes substantial ingredients already; novelty would have to lie in their mathematically coherent integration.

The question driving the paper would be:

> Can we reason about programs using the full abstraction of dependent and univalent mathematics, while extracting executable programs with explicit, machine-checked complexity bounds?

The desired discovery is a quantitative fundamental theorem connecting **equality, normalization, erasure, and feasible computation**. It would explain which mathematical abstractions can safely disappear during compilation, which operations must remain, and how the cost of those operations composes.

## The proposed central theorem

**Feasible univalence and quantitative extraction — schematic target.**

Construct a predicative dependent type theory $\mathcal Q$ with an explicit distinction between mathematical specifications and executable content. Give it a univalent specification layer and a syntactically defined feasible fragment $\mathcal Q_{\mathrm{poly}}$. Prove the following properties for the **same specified calculus**.

1. **Normalization and checking.** Well-typed expressions admit computable normal forms; definitional equality and checking of fully annotated terms are decidable. Closed terms of natural-number type have canonical numeral results.
2. **Correct quantitative extraction.** An annotated derivation in the feasible fragment yields executable code, a correctness proof, and a polynomial bound on execution under a fixed machine semantics.
3. **Exact first-order expressive power.** The functions on binary words represented by the feasible fragment are exactly the polynomial-time computable functions, conventionally called FP.
4. **Controlled interaction with univalence.** Abstract univalent reasoning is available in specifications. Crossing into executable computation respects erasure and resource rules; a representation conversion that actually runs must carry a justified resource bound.

For the extraction clause, let $W=\{0,1\}^{*}$, with $|x|$ the bit length of a word. Suppose a checked derivation $D$ establishes

$$
  t : \prod_{x:W}\;\sum_{y:W} R(x,y)
$$

in $\mathcal Q_{\mathrm{poly}}$. The sum carries an executable witness $y$; its certification component is erasable under the theory's rules. The target theorem should construct a program $e_D$ and an explicit polynomial $P_D$ such that, for every input $x$, evaluation returns a word $y$ satisfying

$$
  R(x,y)
  \qquad\text{and}\qquad
  \operatorname{steps}_{M}(e_D,x)\leq P_D(|x|).
$$

Here $M$ is a fully specified machine, including the costs of primitive operations. If it is a closure machine, its relationship to a conventional bit-cost model must also be proved. The polynomial depends on the fixed derivation/program, not on the particular input. Its certificate is constructed compositionally; defining the bound by rerunning the program would not meet the objective.

The completeness clause is

$$
  \operatorname{DefFun}(\mathcal Q_{\mathrm{poly}},W\to W)=\mathrm{FP}.
$$

This is extensional completeness: every polynomial-time function has a representation. It does not promise that every efficient implementation is accepted, or that optimal complexity bounds can be inferred automatically. Proof checking and compilation themselves are not asserted to be polynomial-time.

The central research problem is finding the exact restrictions under which these clauses hold together. A feasible fragment consisting merely of programs bundled with an assumed polynomial-time proof would not establish the intended syntactic characterization.

## The obstruction that gives the paper its substance

Equality of mathematical results does not imply equality of runtime. Two algorithms can return the same output while taking very different amounts of time. Similarly, a mathematical equivalence between representations can be expensive to execute.

A useful boundary example starts with a total Boolean function $h$ on words. Define

$$
  e_h(x,b)=(x,b\mathbin{\mathrm{xor}}h(x)).
$$

This map is its own inverse. If $h$ is not polynomial-time computable, neither is $e_h$: running $e_h(x,0)$ reveals $h(x)$. Consequently, a rule that allowed every equivalence from an unrestricted specification layer to become a feasible runtime conversion would fail whenever that layer can express such an $h$.

This is an elementary diagnostic argument, not a claimed new result. A formal impossibility theorem would have to specify the language, realizability assumptions, and expressible non-polynomial function precisely.

The constructive answer should distinguish:

- equality used only to justify a specification;
- proof and type information that can be erased;
- computational transport that changes a representation and must be charged;
- equivalences equipped with explicit bounds for the operations that will run.

The desired theorem must make this distinction stable under dependent substitution, recursion, cubical composition, and compilation. Establishing each feature in a separate language would leave the main problem unresolved.

## What is already known in October 2026

Several apparently ambitious versions of this proposal would reproduce existing research.

- **Dependent types and polynomial-time computation already coexist.** Robert Atkey's *Polynomial Time and Dependent Types* develops systems based on quantitative type theory, including an LFPL-based system, and proves polynomial-time soundness through realizability. The paper includes Agda formalization of its semantic development. [Paper and artifact links](https://bentnib.org/polytime-deptypes.html).
- **Graded dependent erasure already has a formal metatheory.** Abel, Danielsson, and Eriksson prove normalization, conversion decidability, and extraction results under explicit conditions on modalities and elimination. [2026 extended paper](https://arxiv.org/abs/2603.29716).
- **Univalent cubical normalization already exists for a specified calculus.** Sterling and Angiuli's result also yields decidability of judgmental equality. Its exact scope and universe treatment must be respected when reusing it. [LICS 2021 paper](https://arxiv.org/abs/2101.11479).
- **Dependent reasoning about cost already exists.** Calf separates behavior from cost and supports verified cost analysis. [Niu–Sterling–Grodin–Harper](https://arxiv.org/abs/2107.04663).
- **Abstraction and cost have already been combined in univalent type theory.** Grodin, Li, and Harper's *Abstraction Functions as Types* establishes modular reasoning about behavior and cost. [POPL 2026 paper](https://arxiv.org/abs/2502.20496).
- **Potential-based amortized analysis is already being integrated with these ideas.** *Potential Functions as Types* develops a synthesis involving abstraction, potential, and a graded dependent language. [Grodin–Chu–Li–Hoffmann–Harper, 2026 preprint](https://arxiv.org/abs/2607.08547).

Atkey's presentation includes equality reflection in its erased fragment (§3.1.4). Its complexity result therefore cannot simply be combined with another calculus's conversion-decision theorem. Replacing that equality discipline while preserving feasible expressiveness is one of the proposed intermediate research problems. [Source rules](https://arxiv.org/html/2307.09145v2#S3.SS1.SSS4).

The candidate contribution is therefore an explicit, executable, normalizing theory with a proved connection from its resource discipline through erasure to actual execution, and a justified account of univalent transport. The cited works do not by themselves establish that exact package. This research survey does not establish that no other work does; a detailed novelty audit is an early project deliverable.

## The proof architecture we would investigate

The proposed organizing idea is a quantitative logical relation, or gluing construction, attaching three compatible pieces of information to an expression:

1. its mathematical interpretation;
2. its computational/normalization interpretation;
3. an executable realizer with resource evidence.

The fundamental lemma would show that every typing rule preserves this combined interpretation. The difficult cases would include dependent substitution, recursion, erased elimination, universe formation, and cubical transport. The model must be constructed for concrete syntax; assuming a model already satisfying all desired properties would move the theorem into its hypotheses.

Normalization and operational complexity concern different evaluations. A proof assistant may perform expensive normalization while checking a proof whose extracted program is cheap. The construction must relate these processes without identifying their costs.

This is a proof direction, not a completed argument. The smaller-paper roadmap is designed to test the risky components before committing to the complete theorem.

## What the paper would contain

1. A precise calculus with a finite, explicitly listed collection of type formers, predicative universes, grades, erasure rules, and a chosen cubical presentation.
2. A specified extraction procedure and target machine.
3. The quantitative fundamental theorem, followed by normalization, canonicity, checking, and extraction consequences.
4. A soundness-and-completeness theorem for the feasible first-order fragment.
5. A theorem explaining when representation changes preserve feasibility and how their bounds compose.
6. A substantial example and a reproducible formal artifact.

The first example should use finite data: an abstract finite-map interface implemented by lists and by balanced trees. Correctness is transferred through proved abstraction relations; operation bounds are supplied separately for each implementation. Different representations need not be bijective, and changing them need not preserve identical runtime.

A later application could treat exact real arithmetic. It would bound the work needed for a requested finite precision, with explicit assumptions about input approximations and separation of a divisor from zero. Schwichtenberg and Wiesnet already extract a division algorithm from coinductive proofs; adding a verified resource analysis would be an extension of that work. [*Logic for exact real arithmetic*](https://lmcs.episciences.org/7383).

General coinduction, arbitrary higher inductive types, and full induction-recursion should enter only when a proved extension theorem supports them. They are separate extensions, rather than prerequisites for the first result.

## What would justify the strongest claim

The finished paper would need one common calculus and a closed chain of proofs from its rules to executable behavior. In particular, it would need a nontrivial example using abstract equality, erasure, and a resource-sensitive implementation together.

The scientific payoff would be a precise extension of proofs-as-programs: a mathematical proof can determine an algorithm, justify which parts of the proof need not execute, and supply a certificate explaining the resources required by the remaining computation.

The [companion roadmap](formalization-roadmap.md) proposes the established-paper missions, three preceding research papers, and the final integration mission needed to pursue that result.
