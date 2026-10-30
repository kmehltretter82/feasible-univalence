# Proof ideas and mathematical tests

These are candidate arguments for the [research programme](research-proposal.md). They are not completed proofs. Each idea names the missing obligation and a bounded first experiment. The [roadmap](formalization-roadmap.md) identifies the proposed papers and established results on which they would build.

## 1. Preserve resources through an erasing compiler

**Target: Paper A.** Start with a graded source calculus and define an actual translation into a target language with closures and a fixed evaluation strategy.

A value-only logical relation is insufficient: it can prove that two programs return the same value while saying nothing about duplication or access to erased inputs. The relation should track a source environment, a target environment, and the resource ownership represented by their bindings and reachable values.

For an affine instance, aim for an invariant of the schematic form

$$
\operatorname{used}(\tau)+\operatorname{live}(s')\leq\operatorname{available}(s),
$$

where a machine trace $\tau$ takes initial state $s$ to state $s'$. The vectors count the resource notion selected by the source discipline; they are not automatically time or memory counts. For a linear instance, formulate an appropriate conservation law, including ownership retained in a returned closure or data structure.

The initial budget cannot simply be defined as whatever the execution happens to consume. It must come from the typing derivation and the supplied resource environment.

**Proof obligations.** Establish environment extension, renaming, substitution, closure creation, application, and recursive elimination. Erasing an argument must remove its evaluation as well as its stored representation when the selected extraction semantics requires that behavior. The simulation has to account for source steps that disappear and target administrative steps that remain.

**First experiment.** Formalize a recursive fold whose body captures one resource, then returns a closure containing it. This tests substitution and ownership transfer together. An identity function does not exercise the difficult interaction.

**Failure tests.** Look for a source term whose extracted call-by-value execution evaluates an otherwise erased argument, duplicates an affine resource, or discards a resource that the selected linear interpretation requires to remain accounted for. An unqualified change from call-by-name to call-by-value is not automatically sound.

The starting source-machine theorem and the need for an extracted operational result are documented in the authors' [2026 issue](https://github.com/graded-type-theory/graded-type-theory/issues/95).

## 2. Recover feasibility with intensional equality

**Target: Paper B.** Specify an intensional graded calculus with controlled recursion. Investigate a sound interpretation into a quantitative realizability model while obtaining normalization through an independent relation on the same syntax.

The two arguments have different duties. Resource realizability must connect each accepted program to an operational bound. Normalization must justify the actual conversion algorithm. Neither result may be imported from a different calculus merely because its syntax looks similar.

Atkey's [polynomial-time dependent theory](https://bentnib.org/polytime-deptypes.html) is a source for the feasible recursion and realizability components. The change of equality discipline is a separate theorem obligation.

**Candidate route.** Interpret intensional identity and its eliminator in the existing semantic setting, while keeping the source's definitional equality algorithmic. For first-order completeness, embed a known feasible programming fragment or a bounded machine simulation. This need not provide an inverse translation of all extensional proofs.

**First experiment.** Prove realizability and normalization for one dependent iterator with its exact usage annotations. Then add identity elimination and verify that the same resource interpretation survives.

**Failure tests.** Check whether conversion can disguise a runtime resource increase; whether an erased input can become a recursion clock; and whether the chosen recursion rule permits repeated duplication of growing intermediate data.

The success criterion is an explicit syntax and a proved interpretation. Defining the feasible terms as those already known to have polynomial runtime would make the central soundness claim circular.

## 3. Derive bounds without executing the program

**Targets: Papers B and C.** Keep output-size information alongside time bounds. Composition needs both.

Suppose $f$ has a time bound $p_f(n)$ and output-length bound $s_f(n)$, and $g$ has a time bound $p_g(n)$. A candidate composition rule has the form

$$
p_{g\circ f}(n)\leq p_f(n)+p_g(s_f(n))+a(n),
$$

where $a$ accounts for the chosen machine's call and representation overhead. Its exact form must be derived from the machine, rather than assumed.

Similarly, an iterator must accumulate a bound justified by its resource rule. Merely requiring that each individual step is polynomial-time is insufficient: the size of intermediate states and the number of iterations also matter.

**First experiment.** Produce bound certificates for two list traversals and their composition, then a nested iterator. Check that certificate generation examines the annotated derivation without evaluating the program on all possible inputs.

**Failure tests.** Unary/binary encoding changes; unit-cost arithmetic on arbitrarily large integers; hidden copying in substitution; and treating a supplied higher-order function as a free oracle. These can invalidate a claimed bit-complexity bound while leaving an abstract reduction-count theorem true.

These composition inequalities are standard ingredients. The proposed contribution would be their sound integration with the specified dependent calculus and erasure compiler.

## 4. Identify the boundary for feasible transport

**Target: Paper C.** Begin with a simple obstruction before designing transport rules.

For any total Boolean function $h$ on words, define

$$
e_h(x,b)=(x,b\mathbin{\mathrm{xor}}h(x)).
$$

Then $e_h\circ e_h=\mathrm{id}$. Any implementation of $e_h$ computes $h(x)$ by applying it to $(x,0)$ and reading the second component. Subject to the fixed encodings, polynomial-time computability of $e_h$ would imply polynomial-time computability of $h$.

Thus, if the unrestricted layer expresses a non-polynomial $h$, all of its equivalences cannot automatically be admitted as feasible runtime transports. This conditional obstruction is elementary; an unconditional language-specific result also requires establishing the relevant expressiveness and complexity separation.

**Positive direction.** Attach implementation and size/cost evidence to the equivalences used computationally. Prove a simulation between the extracted transport and its intended forward implementation. Charge the cubical machinery that survives erasure. Mathematical specifications may still use equivalences without such executable certificates.

The required theorem is stronger than closure of polynomial-time functions under composition. It must show that dependent substitution, dimension substitution, cubical composition, and the selected univalence rules preserve the resource interpretation.

**First experiment.** Use a concrete equivalence between two finite-data representations, prove a bound for both directions, and compare evaluation of transport with direct conversion. Then make the conversion occur inside a dependent function.

**Failure tests.** An erased proof reveals a new runtime operation; cubical composition duplicates a linear input; a dimension substitution changes what can be erased; or a purported zero-cost cast performs real data conversion.

The exact chosen Cartesian presentation must determine whether the relevant constructors are named $V$, glue, coercion, or otherwise. A lemma for a De Morgan calculus cannot be substituted without a translation theorem.

## 5. Build a combined logical relation

**Target: the final paper.** Explore a logical relation assigning to each well-typed expression a compatible normalization interpretation, mathematical behavior, and executable resource interpretation.

An initial schematic semantic value might carry

$$
(\text{normalization evidence},\;\text{runtime realizer},\;
\text{resource certificate},\;\text{compatibility evidence}).
$$

This tuple is only a design sketch. The actual universe levels, dependence on contexts, and closure conditions must be defined before it can support a theorem.

**Fundamental lemma.** Show, by the syntax's derivation rules, that well-typed terms preserve this relation under related substitutions. The novel content lies in proving every closure condition, particularly for universes, recursion, erased elimination, and cubical operations.

**Possible staging.** First combine normalization and resource relations for the intensional feasible core. Then extend the construction to the cubical fragment from Paper C. Finally prove the required universe closure. A product of two pre-existing models is not automatically a model of the interacting language.

**First experiment.** Prove the substitution case for a dependent function type where the parameter influences an erased type index and is used with a nontrivial grade by executable code.

**Failure tests.** The resource evidence ceases to be stable under conversion; normalization requires a forbidden duplication; semantic equality identifies programs whose resource certificates cannot be related; or a universe construction depends circularly on its own normalization theorem.

The literature on [cubical normalization](https://arxiv.org/abs/2101.11479) and [quantitative realizability](https://doi.org/10.1016/j.tcs.2010.12.025) supplies distinct starting points. Their combination is a research obligation, not an existing imported lemma.

## 6. Transfer specifications across data implementations

**Target: a joint example.** Specify finite-map behavior abstractly and supply list and balanced-tree implementations through abstraction relations. Multiple concrete values can denote the same map, so a bijection between representation carriers should not be assumed.

Prove operation correctness and costs separately. A client theorem can then be instantiated with either implementation, producing the corresponding bound. Changing implementation preserves the abstract specification; it need not preserve an identical cost expression.

**First experiment.** Verify a small client that builds a map and performs a batch of lookups. Its proof should use the abstract interface, while its cost certificate depends explicitly on the implementation's operation bounds.

**Failure tests.** The client inspects a private representation; a supposedly abstract theorem assumes the implementation's balancing invariant without proving it; or correctness transfers but cost is silently kept unchanged.

This example should build on existing work such as [*Abstraction Functions as Types*](https://arxiv.org/abs/2502.20496). The research contribution is the connection to the programme's actual checked compiler and feasible calculus.

## What to record after each experiment

Record the precise source and proposed rules, the lemma attempted, the proof or counterexample, and the remaining obligations. Keep a failed candidate available as evidence when revising the design. A restricted theorem can be useful, but it must be named and described at its actual scope.

The first useful deliverable is a closed operational lemma for the erasure/resource bridge, together with a source comparison. A long list of plausible type-theoretic constructions is not a substitute for that experiment.
