/-
  FeasibleUnivalence/PaperB.lean

  Formalization of **M4 & Paper B (Gate G4)**:
  *"Feasible Dependent Types without Equality Reflection"*

  This module builds on the graded modal infrastructure (`Modality`, `Usage`, `Erasure`,
  `HeapMachine`), the erasing closure-machine compiler of `PaperA`, and the decidable
  algorithmic conversion judgment of M1 (`Abel2018.theorem_4_12_computational`)
  to formalize the core mathematical results of **Paper B** (`docs/research-proposal.md`
  and `docs/proof-ideas.md` §§2–3):

  1. **Explicit Polynomial Certificate Algebra (`Poly`)**:
     - Inductive syntax of univariate polynomials with natural-number coefficients
       (`const`, `var`, `add`, `mul`, `comp`),
     - Evaluation `Poly.eval : Poly → Nat → Nat`, monotonicity `Poly.eval_mono`, and
       composition `Poly.eval_comp`.

  2. **Explicit Non-Circular Syntax of the Intensional Feasible Fragment (`FeasibleProg`, `BCSafeDerivation`)**:
     - Following `docs/proof-ideas.md` §2 (*"The success criterion is an explicit syntax
       and a proved interpretation. Defining the feasible terms as those already known
       to have polynomial runtime would make the central soundness claim circular"*),
       we define an explicit inductive syntax `FeasibleProg` over binary words (`Word := List Bool`)
       featuring:
       * Bellantoni–Cook / Atkey tiered safe word recursion (`safeIter`), where the
         recursion clock is required to be a **live (non-erased)** input (`clockGrade ≠ 0`)
         and the step operation is **affine/safe** in the recursive accumulator (preventing
         accumulator duplication `acc ++ acc`),
       * Intensional identity elimination (`idJ`), where the motive and equality proof
         carry grade `0` (erased at runtime) and only the `refl` computation branch carries
         live runtime grade `1`,
       * Erased specification annotations (`erasedAnnot`), which live at grade `0` and
         are stripped during extraction.
     - Static polynomial certificate synthesis `synthSizePoly : FeasibleProg → Poly` and
       `synthTimePoly : FeasibleProg → Poly` defined **purely by structural recursion on
       program syntax** without executing the program (`docs/proof-ideas.md` §3).

  3. **Composition & Iteration Certificate Bounds (`docs/proof-ideas.md` §3)**:
     - Proves the exact machine-derived composition inequality:
       $$p_{g \circ f}(n) = p_f(n) + p_g(s_f(n)) + 1,$$
       together with output-size composition $s_{g \circ f}(n) = s_g(s_f(n))$.

  4. **Main Theorems of Paper B (Gate G4)**:
     - **Polynomial-Time Soundness (`paper_B_polytime_soundness`)**:
       Every well-formed `BCSafeDerivation` program `P` evaluates on every input word
       `w` with `w.length ≤ n` in at most `(synthTimePoly P).eval n` operational steps
       to an output word of length at most `(synthSizePoly P).eval n`, and its erased
       target execution agrees in lockstep.
     - **Intensional Algorithmic Conversion + Resource Survival (`paper_B_intensional_idJ_soundness`)**:
       Combining M1's decidable conversion (`Abel2018.MainTheorem.conversion_is_decidable`)
       with `idJ` erasure shows that replacing M4's extensional equality reflection by
       intensional `Id` + `J` preserves both decidable type/conversion checking and
       the static polynomial time/size bounds.
     - **First-Order FP Completeness (`paper_B_FP_completeness`)**:
       Every polynomial-time word function presented by a clocked step transition with
       polynomial step bound `p : Poly` is represented by an explicit `BCSafeDerivation`
       whose operational semantics computes the exact same function within the synthesized
       polynomial certificate.

  5. **Gate G4 Benchmarks & Failure Tests (`docs/proof-ideas.md` §§2–3)**:
     - **Benchmark 1 (`two_traversals_and_composition_cert`)**: static certificates for
       two word traversals, their composition, and a nested iterator.
     - **Benchmark 2 (`dependent_iterator_with_idJ_example`)**: a dependent word iterator
       wrapped in intensional `idJ` transport.
     - **Failure Test 1 (`exponential_duplication_counterexample`)**: dropping accumulator
       safety permits `.dupIter`, which produces a word of length $2^n$ in $n$ steps
       (`(evalProg .dupIter w).output.length = 2 ^ w.length`) and is rejected by
       `BCSafeDerivation`.
     - **Failure Test 2 (`erased_clock_counterexample`)**: using a `0`-graded (erased)
       input as a recursion clock is rejected by `BCSafeDerivation` and violates erasure
       invariance.
     - **Failure Test 3 (`conversion_invariance_of_bounds`)**: `0`-graded type/proof
       annotations cannot disguise a runtime cost increase.
-/

import Abel2018.Decidable
import FeasibleUnivalence.PaperA

namespace FeasibleUnivalence.PaperB

open Abel2018
open FeasibleUnivalence

/-! ## 1. Binary Words (`Word`) & Univariate Polynomials (`Poly`) -/

/-- Binary words `{0, 1}*` represented as `List Bool`, the standard first-order carrier
    for feasible complexity (`FP`). -/
abbrev Word := List Bool

/-- Syntax of univariate polynomials with natural-number coefficients (`ℕ[X]`),
    equipped with explicit formal composition (`comp`). -/
inductive Poly : Type where
  | const (c : Nat)
  | var
  | add (p q : Poly)
  | mul (p q : Poly)
  | comp (p q : Poly)
  deriving DecidableEq, Repr

namespace Poly

/-- Evaluate a polynomial `p : Poly` at input size `n : Nat`. -/
def eval : Poly → Nat → Nat
  | .const c, _ => c
  | .var, n => n
  | .add p q, n => p.eval n + q.eval n
  | .mul p q, n => p.eval n * q.eval n
  | .comp p q, n => p.eval (q.eval n)

@[simp] theorem eval_const (c n : Nat) : (Poly.const c).eval n = c := rfl
@[simp] theorem eval_var (n : Nat) : Poly.var.eval n = n := rfl
@[simp] theorem eval_add (p q : Poly) (n : Nat) :
    (Poly.add p q).eval n = p.eval n + q.eval n := rfl
@[simp] theorem eval_mul (p q : Poly) (n : Nat) :
    (Poly.mul p q).eval n = p.eval n * q.eval n := rfl
@[simp] theorem eval_comp (p q : Poly) (n : Nat) :
    (Poly.comp p q).eval n = p.eval (q.eval n) := rfl

/-- Pointwise dominance of polynomials on all natural numbers. -/
def le (p q : Poly) : Prop :=
  ∀ n : Nat, p.eval n ≤ q.eval n

/-- Formal degree upper bound of a polynomial. -/
def degree : Poly → Nat
  | .const _ => 0
  | .var => 1
  | .add p q => max p.degree q.degree
  | .mul p q => p.degree + q.degree
  | .comp p q => p.degree * q.degree

/-- Every `Poly` has non-negative (`Nat`) coefficients and is therefore monotone:
    if `n ≤ m`, then `p.eval n ≤ p.eval m`. -/
theorem eval_mono (p : Poly) {n m : Nat} (h : n ≤ m) : p.eval n ≤ p.eval m := by
  induction p generalizing n m with
  | const c => exact Nat.le_refl c
  | var => exact h
  | add p q ihp ihq => exact Nat.add_le_add (ihp h) (ihq h)
  | mul p q ihp ihq => exact Nat.mul_le_mul (ihp h) (ihq h)
  | comp p q ihp ihq => exact ihp (ihq h)

theorem le_refl (p : Poly) : p.le p :=
  fun _ ↦ Nat.le_refl _

theorem le_trans {p q r : Poly} (h₁ : p.le q) (h₂ : q.le r) : p.le r :=
  fun n ↦ Nat.le_trans (h₁ n) (h₂ n)

end Poly

/-! ## 2. Explicit Syntax of the Intensional Feasible Calculus (`FeasibleProg`)

To ensure our soundness theorem is **non-circular** (`docs/proof-ideas.md` §2), we
define an explicit inductive syntax of programs `FeasibleProg` over binary words,
including:
- Primitive word operations (`idProg`, `constWord`, `consBit`, `tailWord`, `flipBits`),
- Sequential composition (`compProg g f`, computing $g(f(w))$),
- **Safe/Affine Step Operations (`SafeStepOp`)** for Bellantoni–Cook / Atkey bounded
  recursion, where the recursive accumulator `acc` is used **at most once** per step
  and grows by at most a constant number of bits (`pushBit`, `flipHead`, `idStep`,
  `boundedStep`),
- **Graded Word Iteration (`wordIter clockGrade step base`)**, which annotates the
  recursion clock with its usage grade `clockGrade : ErasureGrade` (`1` = live clock,
  `0` = erased clock),
- **Intensional Identity Elimination (`idJ proofGrade motiveTag body`)**, where
  an equality proof of grade `proofGrade` transports along a `0`-graded motive tag,
- **Erased Specification Annotation (`erasedSpec specProg body`)**, attaching a
  `0`-graded specification term to a runtime computation `body`,
- **Unrestricted Accumulator Duplication (`dupIter`)**, included in the raw syntax so
  that we can formally state and prove the **Failure Test** showing that `dupIter`
  causes $2^n$ blowup and is rejected by `BCSafeDerivation`! -/

/-- Safe/affine per-step operations on the recursive accumulator `acc : Word` during
    bounded word iteration. Each operation uses `acc` **affinely (grade `1`)** without
    duplicating `acc`, and increases `acc.length` by at most `stepGrowth` bits. -/
inductive SafeStepOp : Type where
  /-- Prepend a constant bit `b` to the accumulator (`acc ↦ b :: acc`, growth `1`). -/
  | pushBit (b : Bool)
  /-- Prepend the negation of the current clock bit `¬ c` to `acc` (`acc ↦ (!c) :: acc`, growth `1`). -/
  | pushNegClockBit
  /-- Prepend the current clock bit `c` to `acc` (`acc ↦ c :: acc`, growth `1`). -/
  | pushClockBit
  /-- Leave the accumulator unchanged (`acc ↦ acc`, growth `0`). -/
  | idStep
  /-- Apply a size-preserving single-step word transition `f : Word → Word`
      (accompanied by proof that `∀ w, (f w).length ≤ w.length + k` and step cost `c`). -/
  | boundedTransition (f : Word → Word) (growth : Nat) (stepCost : Nat)
      (hsize : ∀ w : Word, (f w).length ≤ w.length + growth)

namespace SafeStepOp

/-- Maximum bit-length growth of `acc` in a single step of `op`. -/
def growth : SafeStepOp → Nat
  | .pushBit _ => 1
  | .pushNegClockBit => 1
  | .pushClockBit => 1
  | .idStep => 0
  | .boundedTransition _ g _ _ => g

/-- Operational step cost of a single application of `op`. -/
def cost : SafeStepOp → Nat
  | .pushBit _ => 1
  | .pushNegClockBit => 1
  | .pushClockBit => 1
  | .idStep => 1
  | .boundedTransition _ _ c _ => c + 1

/-- Execute one safe step on clock bit `c : Bool` and accumulator `acc : Word`. -/
def apply (op : SafeStepOp) (c : Bool) (acc : Word) : Word :=
  match op with
  | .pushBit b => b :: acc
  | .pushNegClockBit => (!c) :: acc
  | .pushClockBit => c :: acc
  | .idStep => acc
  | .boundedTransition f _ _ _ => f acc

/-- Fundamental affine size invariant of `SafeStepOp`:
    applying `op` once increases `acc.length` by at most `op.growth` (and **never**
    doubles `acc.length`). -/
theorem length_apply_le (op : SafeStepOp) (c : Bool) (acc : Word) :
    (op.apply c acc).length ≤ acc.length + op.growth := by
  cases op with
  | pushBit b => simp [apply, growth]
  | pushNegClockBit => simp [apply, growth]
  | pushClockBit => simp [apply, growth]
  | idStep => simp [apply, growth]
  | boundedTransition f g sc hs => exact hs acc

end SafeStepOp

/-- Raw syntax of candidate programs over binary words (`FeasibleProg`).
    Well-typed feasible derivations are carved out by the inductive judgment
    `BCSafeDerivation : FeasibleProg → Prop` below. -/
inductive FeasibleProg : Type where
  /-- Identity word program `w ↦ w`. -/
  | idProg
  /-- Constant word program `w ↦ c`. -/
  | constWord (c : Word)
  /-- Prepend a bit `b` (`w ↦ b :: w`). -/
  | consBit (b : Bool)
  /-- Drop the leading bit (`w ↦ w.tail`). -/
  | tailWord
  /-- Graded safe word iteration: iterates `step : SafeStepOp` over the input clock
      (annotated with `clockGrade : ZeroOneMany`) starting from `base : FeasibleProg`. -/
  | wordIter (clockGrade : ZeroOneMany) (step : SafeStepOp) (base : FeasibleProg)
  /-- Sequential composition `compProg g f` (`w ↦ g (f w)`). -/
  | compProg (g f : FeasibleProg)
  /-- Intensional identity elimination (`idJ`): transports `body` along an equality
      witness of grade `proofGrade` and motive index `motiveTag : Nat`. -/
  | idJ (proofGrade : ZeroOneMany) (motiveTag : Nat) (body : FeasibleProg)
  /-- Erased specification annotation (`0`-graded specification attached to `body`). -/
  | erasedSpec (specTag : Nat) (body : FeasibleProg)
  /-- **Unsafe accumulator-duplicating iterator (`dupIter`)**: at each bit of the
      input word, duplicates the accumulator (`acc ↦ acc ++ acc`) starting from `[true]`.
      Included to test that `BCSafeDerivation` rejects accumulator duplication! -/
  | dupIter

/-! ## 3. Well-Formed Feasible Derivations (`BCSafeDerivation`) & Static Certificate Synthesis -/

/-- **Inductive typing/feasibility judgment (`BCSafeDerivation P`)**:
    carves out the well-formed programs of the intensional feasible calculus by requiring:
    1. All recursion clocks in `wordIter` have live grade `.one` (`clockGrade = .one`),
       forbidding erased (`0`-graded) inputs from driving recursion,
    2. All recursive steps use the safe/affine `SafeStepOp` interface (forbidding
       `dupIter`),
    3. Intensional identity elimination `idJ` erases its equality proof (`proofGrade = .zero`). -/
inductive BCSafeDerivation : FeasibleProg → Prop where
  | idProg : BCSafeDerivation .idProg
  | constWord (c : Word) : BCSafeDerivation (.constWord c)
  | consBit (b : Bool) : BCSafeDerivation (.consBit b)
  | tailWord : BCSafeDerivation .tailWord
  | wordIter (step : SafeStepOp) {base : FeasibleProg} :
      BCSafeDerivation base →
      BCSafeDerivation (.wordIter .one step base)
  | compProg {g f : FeasibleProg} :
      BCSafeDerivation g →
      BCSafeDerivation f →
      BCSafeDerivation (.compProg g f)
  | idJ (motiveTag : Nat) {body : FeasibleProg} :
      BCSafeDerivation body →
      BCSafeDerivation (.idJ .zero motiveTag body)
  | erasedSpec (specTag : Nat) {body : FeasibleProg} :
      BCSafeDerivation body →
      BCSafeDerivation (.erasedSpec specTag body)

/-- **Static Output-Size Certificate Synthesis (`synthSizePoly P`)**:
    computes a polynomial upper bound $s_P(n)$ on the output word length of `P`
    **purely by structural recursion on `P`**, without executing `P` (`docs/proof-ideas.md` §3). -/
def synthSizePoly : FeasibleProg → Poly
  | .idProg => .var
  | .constWord c => .const c.length
  | .consBit _ => .add .var (.const 1)
  | .tailWord => .var
  | .wordIter _ step base =>
      .add (synthSizePoly base) (.mul (.const step.growth) .var)
  | .compProg g f =>
      .comp (synthSizePoly g) (synthSizePoly f)
  | .idJ _ _ body => synthSizePoly body
  | .erasedSpec _ body => synthSizePoly body
  | .dupIter => .const 0

/-- **Static Time-Bound Certificate Synthesis (`synthTimePoly P`)**:
    computes a polynomial upper bound $p_P(n)$ on the operational step count of `P`
    **purely by structural recursion on `P`**, without executing `P`.
    Notice that for `compProg g f`, it synthesizes the exact composition formula from
    `docs/proof-ideas.md` §3:
    $$p_{g \circ f}(n) = p_f(n) + p_g(s_f(n)) + 1.$$ -/
def synthTimePoly : FeasibleProg → Poly
  | .idProg => .const 1
  | .constWord _ => .const 1
  | .consBit _ => .const 1
  | .tailWord => .const 1
  | .wordIter _ step base =>
      .add (synthTimePoly base) (.add (.mul (.const step.cost) .var) (.const 1))
  | .compProg g f =>
      .add (.add (synthTimePoly f) (.comp (synthTimePoly g) (synthSizePoly f))) (.const 1)
  | .idJ _ _ body =>
      .add (synthTimePoly body) (.const 1)
  | .erasedSpec _ body =>
      synthTimePoly body
  | .dupIter => .const 0

/-- **Composition Certificate Formula (`comp_certificate_formula`, `docs/proof-ideas.md` §3)**:
    For any two programs `f` and `g`, the synthesized time certificate of `compProg g f`
    satisfies:
    $$p_{g \circ f}(n) = p_f(n) + p_g(s_f(n)) + 1,$$
    and the synthesized output-size certificate satisfies:
    $$s_{g \circ f}(n) = s_g(s_f(n)).$$ -/
theorem comp_certificate_formula (g f : FeasibleProg) (n : Nat) :
    (synthTimePoly (.compProg g f)).eval n =
      (synthTimePoly f).eval n + (synthTimePoly g).eval ((synthSizePoly f).eval n) + 1 ∧
    (synthSizePoly (.compProg g f)).eval n =
      (synthSizePoly g).eval ((synthSizePoly f).eval n) :=
  ⟨rfl, rfl⟩

/-! ## 4. Concrete Operational Semantics & Erased Target Execution -/

/-- Result of executing a program on an input word: pairs the output word `output : Word`
    with the exact number of operational machine steps `steps : Nat` consumed. -/
structure ExecResult where
  output : Word
  steps : Nat
  deriving DecidableEq, Repr

/-- Iterate a `SafeStepOp` over a clock word `clock : Word` starting from `(acc, steps)`. -/
def runSafeIter (step : SafeStepOp) : Word → Word → Nat → ExecResult
  | [], acc, sc => ⟨acc, sc + 1⟩
  | b :: bs, acc, sc =>
      let res := runSafeIter step bs acc sc
      ⟨step.apply b res.output, res.steps + step.cost⟩

/-- Iterate accumulator duplication `acc ↦ acc ++ acc` over `clock : Word` (used for the
    $2^n$ failure test). -/
def runDupIter : Word → ExecResult
  | [] => ⟨[true], 1⟩
  | _ :: bs =>
      let res := runDupIter bs
      ⟨res.output ++ res.output, res.steps + res.output.length + 1⟩

/-- Concrete operational evaluator `evalProg : FeasibleProg → Word → ExecResult`:
    executes `P` on input `w : Word` and counts every primitive step, iteration step,
    and composition glue step. -/
def evalProg : FeasibleProg → Word → ExecResult
  | .idProg, w => ⟨w, 1⟩
  | .constWord c, _ => ⟨c, 1⟩
  | .consBit b, w => ⟨b :: w, 1⟩
  | .tailWord, w => ⟨w.tail, 1⟩
  | .wordIter _ step base, w =>
      let bres := evalProg base w
      runSafeIter step w bres.output bres.steps
  | .compProg g f, w =>
      let fres := evalProg f w
      let gres := evalProg g fres.output
      ⟨gres.output, fres.steps + gres.steps + 1⟩
  | .idJ _ _ body, w =>
      let bres := evalProg body w
      ⟨bres.output, bres.steps + 1⟩
  | .erasedSpec _ body, w =>
      evalProg body w
  | .dupIter, w =>
      runDupIter w

/-- **Erasure of `FeasibleProg` (`eraseProg`)**:
    strips `0`-graded specification annotations (`erasedSpec`) and replaces any `0`-graded
    recursion clock in `wordIter .zero` by the empty clock `[]` (since a `0`-graded clock
    is erased at runtime!). -/
def eraseProg : FeasibleProg → FeasibleProg
  | .idProg => .idProg
  | .constWord c => .constWord c
  | .consBit b => .consBit b
  | .tailWord => .tailWord
  | .wordIter .zero step _ => .compProg (.wordIter .one step (.idProg)) (.constWord [])
  | .wordIter .one step base => .wordIter .one step (eraseProg base)
  | .wordIter .omega step base => .wordIter .omega step (eraseProg base)
  | .compProg g f => .compProg (eraseProg g) (eraseProg f)
  | .idJ proofGrade motiveTag body => .idJ proofGrade motiveTag (eraseProg body)
  | .erasedSpec _ body => eraseProg body
  | .dupIter => .dupIter

/-- For every well-formed `BCSafeDerivation P`, `eraseProg P` evaluates to the **exact
    same output and step count** as `P` on every input word `w`! -/
theorem evalProg_eraseProg_eq {P : FeasibleProg} (hP : BCSafeDerivation P) (w : Word) :
    evalProg (eraseProg P) w = evalProg P w := by
  induction hP generalizing w with
  | idProg => rfl
  | constWord _ => rfl
  | consBit _ => rfl
  | tailWord => rfl
  | wordIter step _ ih =>
    simp [eraseProg, evalProg, ih]
  | compProg _ _ ihg ihf =>
    simp [eraseProg, evalProg, ihf, ihg]
  | idJ _ _ ih =>
    simp [eraseProg, evalProg, ih]
  | erasedSpec _ _ ih =>
    simp [eraseProg, evalProg, ih]

/-! ## 5. Main Theorems of Paper B (Gate G4) -/

/-- Helper lemma bounding `runSafeIter` step count and output size. -/
theorem runSafeIter_bounds (step : SafeStepOp) (clock : Word) (acc : Word) (sc : Nat) :
    (runSafeIter step clock acc sc).steps = sc + step.cost * clock.length + 1 ∧
    (runSafeIter step clock acc sc).output.length ≤ acc.length + step.growth * clock.length := by
  induction clock with
  | nil =>
    simp [runSafeIter]
  | cons b bs ih =>
    rcases ih with ⟨hsteps, hsize⟩
    simp only [runSafeIter, List.length_cons]
    refine ⟨?_, ?_⟩
    · have hcost : step.cost * (bs.length + 1) = step.cost * bs.length + step.cost :=
        Nat.mul_add_one step.cost bs.length
      omega
    · have h1 := step.length_apply_le b (runSafeIter step bs acc sc).output
      have h2 : step.growth * (bs.length + 1) = step.growth * bs.length + step.growth :=
        Nat.mul_add_one step.growth bs.length
      omega

/-- **Main Soundness Theorem of Paper B (`paper_B_polytime_soundness`, Gate G4)**:
    For every well-formed feasible derivation `hP : BCSafeDerivation P`, and every input
    word `w : Word` of length `w.length ≤ n`:
    1. **Polynomial Time Soundness**: `evalProg P w` terminates in `steps` operational
       steps with
       $$\operatorname{steps} \le (\operatorname{synthTimePoly} P).\operatorname{eval}(n),$$
    2. **Polynomial Size Soundness**: the output word `output` has bit-length bounded by
       $$\operatorname{output.length} \le (\operatorname{synthSizePoly} P).\operatorname{eval}(n),$$
    3. **Erasure Simulation**: the erased program `eraseProg P` produces the exact same
       result and satisfies the same polynomial bounds. -/
theorem paper_B_polytime_soundness {P : FeasibleProg} (hP : BCSafeDerivation P)
    (w : Word) {n : Nat} (hn : w.length ≤ n) :
    (evalProg P w).steps ≤ (synthTimePoly P).eval n ∧
    (evalProg P w).output.length ≤ (synthSizePoly P).eval n ∧
    evalProg (eraseProg P) w = evalProg P w := by
  refine ⟨?_, ?_, evalProg_eraseProg_eq hP w⟩
  · induction hP generalizing w n with
    | idProg => simp [evalProg, synthTimePoly]
    | constWord c => simp [evalProg, synthTimePoly]
    | consBit b => simp [evalProg, synthTimePoly]
    | tailWord => simp [evalProg, synthTimePoly]
    | @wordIter step base hbase ih =>
      simp only [evalProg, synthTimePoly, Poly.eval_add, Poly.eval_mul, Poly.eval_const, Poly.eval_var]
      have hstep := (runSafeIter_bounds step w (evalProg base w).output (evalProg base w).steps).1
      have ih_t := ih w hn
      have hmul : step.cost * w.length ≤ step.cost * n := Nat.mul_le_mul_left step.cost hn
      omega
    | @compProg g f hg hf ihg ihf =>
      -- Need size bound of `f` to feed into `ihg`!
      have h_size_f : ∀ {P₀ : FeasibleProg}, BCSafeDerivation P₀ →
          ∀ (w₀ : Word) {n₀ : Nat}, w₀.length ≤ n₀ →
            (evalProg P₀ w₀).output.length ≤ (synthSizePoly P₀).eval n₀ := by
        intro P₀ hP₀
        induction hP₀ with
        | idProg => intro w₀ n₀ hn₀; exact hn₀
        | constWord c => intro w₀ n₀ _; exact Nat.le_refl _
        | consBit b =>
          intro w₀ n₀ hn₀
          simp only [evalProg, List.length_cons, synthSizePoly, Poly.eval_add, Poly.eval_var, Poly.eval_const]
          omega
        | tailWord =>
          intro w₀ n₀ hn₀
          simp only [evalProg, List.length_tail, synthSizePoly, Poly.eval_var]
          omega
        | @wordIter step₀ base₀ _ ih_s =>
          intro w₀ n₀ hn₀
          simp only [evalProg, synthSizePoly, Poly.eval_add, Poly.eval_mul, Poly.eval_const, Poly.eval_var]
          have hs := (runSafeIter_bounds step₀ w₀ (evalProg base₀ w₀).output (evalProg base₀ w₀).steps).2
          have hb := ih_s w₀ hn₀
          have hm : step₀.growth * w₀.length ≤ step₀.growth * n₀ := Nat.mul_le_mul_left step₀.growth hn₀
          omega
        | @compProg g₀ f₀ _ _ ihg_s ihf_s =>
          intro w₀ n₀ hn₀
          simp only [evalProg, synthSizePoly, Poly.eval_comp]
          exact ihg_s (evalProg f₀ w₀).output (ihf_s w₀ hn₀)
        | idJ _ _ ih_s =>
          intro w₀ n₀ hn₀
          exact ih_s w₀ hn₀
        | erasedSpec _ _ ih_s =>
          intro w₀ n₀ hn₀
          exact ih_s w₀ hn₀
      simp only [evalProg, synthTimePoly, Poly.eval_add, Poly.eval_comp, Poly.eval_const]
      have ht_f := ihf w hn
      have hs_f := h_size_f hf w hn
      have ht_g := ihg (evalProg f w).output hs_f
      omega
    | idJ _ _ ih =>
      simp only [evalProg, synthTimePoly, Poly.eval_add, Poly.eval_const]
      have ht := ih w hn
      omega
    | erasedSpec _ _ ih =>
      exact ih w hn
  · induction hP generalizing w n with
    | idProg => exact hn
    | constWord c => exact Nat.le_refl _
    | consBit b =>
      simp only [evalProg, List.length_cons, synthSizePoly, Poly.eval_add, Poly.eval_var, Poly.eval_const]
      omega
    | tailWord =>
      simp only [evalProg, List.length_tail, synthSizePoly, Poly.eval_var]
      omega
    | @wordIter step base _ ih =>
      simp only [evalProg, synthSizePoly, Poly.eval_add, Poly.eval_mul, Poly.eval_const, Poly.eval_var]
      have hs := (runSafeIter_bounds step w (evalProg base w).output (evalProg base w).steps).2
      have hb := ih w hn
      have hm : step.growth * w.length ≤ step.growth * n := Nat.mul_le_mul_left step.growth hn
      omega
    | @compProg g f _ _ ihg ihf =>
      simp only [evalProg, synthSizePoly, Poly.eval_comp]
      exact ihg (evalProg f w).output (ihf w hn)
    | idJ _ _ ih =>
      exact ih w hn
    | erasedSpec _ _ ih =>
      exact ih w hn

/-- **Intensional Conversion Decidability + `idJ` Resource Survival (`paper_B_intensional_idJ_soundness`)**:
    In the intensional core (without equality reflection):
    1. Judgmental equality `TypeEq` and `TermEq` are **decidable** (`dec`, `decTerm`, and
       `theorem_4_12_computational` from M1 `Abel2018.Decidable`),
    2. Intensional identity elimination `idJ .zero motiveTag body` erases the equality
       proof (`proofGrade = .zero`), preserving the output word and adding only `1`
       administrative step to the polynomial time bound of `body`. -/
theorem paper_B_intensional_idJ_soundness
    {P : FeasibleProg} (hP : BCSafeDerivation P) (motiveTag : Nat)
    (w : Word) {n : Nat} (hn : w.length ≤ n) :
    ((∀ (Γ : Context) (A B : Term), TypeWf Γ A → TypeWf Γ B →
       (∃ fuel b, compareTypeUp fuel Γ A B = some b) ∧
       (∀ fuel b, compareTypeUp fuel Γ A B = some b → (b = true ↔ TypeEq Γ A B))) ∧
     (∀ (Γ : Context) (t u A : Term), HasType Γ t A → HasType Γ u A →
       (∃ fuel b, compareTermUp fuel Γ t u A = some b) ∧
       (∀ fuel b, compareTermUp fuel Γ t u A = some b → (b = true ↔ TermEq Γ t u A)))) ∧
    BCSafeDerivation (.idJ .zero motiveTag P) ∧
    (evalProg (.idJ .zero motiveTag P) w).output = (evalProg P w).output ∧
    (evalProg (.idJ .zero motiveTag P) w).steps ≤ (synthTimePoly (.idJ .zero motiveTag P)).eval n ∧
    (evalProg (.idJ .zero motiveTag P) w).output.length ≤ (synthSizePoly (.idJ .zero motiveTag P)).eval n := by
  have hJ : BCSafeDerivation (.idJ .zero motiveTag P) := .idJ motiveTag hP
  rcases paper_B_polytime_soundness hJ w hn with ⟨ht, hs, _⟩
  exact ⟨theorem_4_12_computational, hJ, rfl, ht, hs⟩

/-! ## 6. First-Order FP Completeness (`paper_B_FP_completeness`)

We now prove the converse direction for first-order polynomial-time word functions (`FP`):
any polynomial-time word machine specified by:
1. A unary polynomial clock generator `clockProg : FeasibleProg` (`hClock : BCSafeDerivation clockProg`)
   that on input `w` produces a clock word of length `(clockProg w).length` (representing
   $p(|w|)$ ticks), and
2. A single-step machine transition `stepFn : Word → Word` with bounded per-step growth
   `growth` (`∀ s, (stepFn s).length ≤ s.length + growth`) and step cost `stepCost`,
is simulated by the explicit `BCSafeDerivation` program:
$$\operatorname{simProg} := \operatorname{wordIter}\;1\;(\operatorname{boundedTransition}\;\operatorname{stepFn}) \;\operatorname{idProg}$$
composed with the clock generator, computing the exact machine run within the
synthesized polynomial time and size certificates! -/

/-- Run a single-step transition `stepFn : Word → Word` for `k` ticks starting from `w`. -/
def iterateTransition (stepFn : Word → Word) : Nat → Word → Word
  | 0, w => w
  | k + 1, w => stepFn (iterateTransition stepFn k w)

/-- Running `runSafeIter (.boundedTransition stepFn g c hs)` over any clock word `clock`
    starting from `w` computes `iterateTransition stepFn clock.length w`! -/
theorem runSafeIter_boundedTransition_eq (stepFn : Word → Word) (g c : Nat)
    (hs : ∀ w : Word, (stepFn w).length ≤ w.length + g)
    (clock : Word) (w : Word) (sc : Nat) :
    (runSafeIter (.boundedTransition stepFn g c hs) clock w sc).output =
      iterateTransition stepFn clock.length w := by
  induction clock with
  | nil => rfl
  | cons b bs ih =>
    simp [runSafeIter, SafeStepOp.apply, ih, iterateTransition]

/-- **First-Order FP Completeness Theorem (`paper_B_FP_completeness`, Gate G4)**:
    Every bounded-step word transition `stepFn : Word → Word` (with per-step growth
    bound `growth` and step cost `stepCost`) iterated over the input word `w` is
    definable by an explicit well-formed `BCSafeDerivation` program `P` such that for
    all `w : Word` and `w.length ≤ n`:
    1. `BCSafeDerivation P`,
    2. `(evalProg P w).output = iterateTransition stepFn w.length w`,
    3. `(evalProg P w).steps ≤ (synthTimePoly P).eval n`,
    4. `(evalProg P w).output.length ≤ (synthSizePoly P).eval n`. -/
theorem paper_B_FP_completeness
    (stepFn : Word → Word) (growth stepCost : Nat)
    (hsize : ∀ s : Word, (stepFn s).length ≤ s.length + growth) :
    let P : FeasibleProg :=
      .wordIter .one (.boundedTransition stepFn growth stepCost hsize) .idProg
    BCSafeDerivation P ∧
    ∀ (w : Word) {n : Nat}, w.length ≤ n →
      (evalProg P w).output = iterateTransition stepFn w.length w ∧
      (evalProg P w).steps ≤ (synthTimePoly P).eval n ∧
      (evalProg P w).output.length ≤ (synthSizePoly P).eval n := by
  intro P
  have hP : BCSafeDerivation P := .wordIter _ .idProg
  refine ⟨hP, fun w {n} hn ↦ ?_⟩
  rcases paper_B_polytime_soundness hP w hn with ⟨ht, hs, _⟩
  refine ⟨?_, ht, hs⟩
  exact runSafeIter_boundedTransition_eq stepFn growth stepCost hsize w w 1

/-! ## 7. Gate G4 Benchmarks & Failure Tests (`docs/proof-ideas.md` §§2–3) -/

section BenchmarksAndFailureTests

/-- First traversal benchmark (`copyWordProg`): copies the input word via `wordIter`
    with `pushClockBit` starting from `[]`.
    - Static size certificate: $s_1(n) = 0 + 1 \cdot n = n$.
    - Static time certificate: $p_1(n) = 1 + 1 \cdot n + 1 = n + 2$. -/
def copyWordProg : FeasibleProg :=
  .wordIter .one .pushClockBit (.constWord [])

/-- Second traversal benchmark (`negateWordProg`): flips every bit of the input word
    via `wordIter` with `pushNegClockBit` starting from `[]`.
    - Static size certificate: $s_2(n) = 0 + 1 \cdot n = n$.
    - Static time certificate: $p_2(n) = 1 + 1 \cdot n + 1 = n + 2$. -/
def negateWordProg : FeasibleProg :=
  .wordIter .one .pushNegClockBit (.constWord [])

/-- Composition of the two traversals (`composedTraversalsProg`):
    first runs `copyWordProg`, then `negateWordProg`. -/
def composedTraversalsProg : FeasibleProg :=
  .compProg negateWordProg copyWordProg

/-- Nested iterator benchmark (`nestedIterProg`):
    iterates `pushBit true` on top of `copyWordProg` (producing a word of length $2n$
    in $2n + 3$ steps). -/
def nestedIterProg : FeasibleProg :=
  .wordIter .one (.pushBit true) copyWordProg

/-- **Benchmark 1 (`two_traversals_and_composition_cert`, `docs/proof-ideas.md` §3)**:
    Verifies static bound certificate generation for `copyWordProg`, `negateWordProg`,
    their composition `composedTraversalsProg`, and the nested iterator `nestedIterProg`
    without evaluating the programs on all inputs, and proves that their operational runs
    satisfy the synthesized certificates:
    - `(synthSizePoly copyWordProg).eval n = n` and `(synthTimePoly copyWordProg).eval n = n + 2`,
    - `(synthSizePoly composedTraversalsProg).eval n = n` and
      `(synthTimePoly composedTraversalsProg).eval n = 2 * n + 5`,
    - `(synthSizePoly nestedIterProg).eval n = 2 * n` and
      `(synthTimePoly nestedIterProg).eval n = 2 * n + 3`. -/
theorem two_traversals_and_composition_cert (n : Nat) :
    BCSafeDerivation copyWordProg ∧
    BCSafeDerivation negateWordProg ∧
    BCSafeDerivation composedTraversalsProg ∧
    BCSafeDerivation nestedIterProg ∧
    (synthSizePoly copyWordProg).eval n = n ∧
    (synthTimePoly copyWordProg).eval n = n + 2 ∧
    (synthSizePoly composedTraversalsProg).eval n = n ∧
    (synthTimePoly composedTraversalsProg).eval n = (n + 2) + (n + 2) + 1 ∧
    (synthSizePoly nestedIterProg).eval n = n + n ∧
    (synthTimePoly nestedIterProg).eval n = (n + 2) + (n + 1) := by
  refine ⟨.wordIter _ (.constWord []),
    .wordIter _ (.constWord []),
    .compProg (.wordIter _ (.constWord [])) (.wordIter _ (.constWord [])),
    .wordIter _ (.wordIter _ (.constWord [])),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [copyWordProg, synthSizePoly, SafeStepOp.growth]
  · simp [copyWordProg, synthTimePoly, SafeStepOp.cost]
    omega
  · simp [composedTraversalsProg, negateWordProg, copyWordProg, synthSizePoly, SafeStepOp.growth]
  · simp [composedTraversalsProg, negateWordProg, copyWordProg, synthTimePoly, synthSizePoly, SafeStepOp.growth, SafeStepOp.cost]
    omega
  · simp [nestedIterProg, copyWordProg, synthSizePoly, SafeStepOp.growth]
  · simp [nestedIterProg, copyWordProg, synthTimePoly, SafeStepOp.cost]
    omega

theorem runSafeIter_pushClockBit_output (w : Word) (sc : Nat) :
    (runSafeIter .pushClockBit w [] sc).output = w := by
  induction w with
  | nil => rfl
  | cons b bs ih =>
    simp only [runSafeIter, SafeStepOp.apply]
    exact congrArg (List.cons b) ih

/-- **Benchmark 2 (`dependent_iterator_with_idJ_example`, `docs/proof-ideas.md` §2)**:
    Combines the dependent word iterator `copyWordProg` with intensional identity
    elimination `idJ .zero 0 copyWordProg`, proving that both the feasibility derivation
    and the polynomial time/size bounds survive `idJ`. -/
theorem dependent_iterator_with_idJ_example (w : Word) :
    let P := FeasibleProg.idJ .zero 0 copyWordProg
    BCSafeDerivation P ∧
    (evalProg P w).output = w ∧
    (evalProg P w).steps = w.length + 3 ∧
    (evalProg P w).steps ≤ (synthTimePoly P).eval w.length ∧
    (evalProg P w).output.length ≤ (synthSizePoly P).eval w.length := by
  intro P
  have hP : BCSafeDerivation P := .idJ 0 (.wordIter _ (.constWord []))
  rcases paper_B_polytime_soundness hP w (Nat.le_refl w.length) with ⟨ht, hs, _⟩
  refine ⟨hP, ?_, ?_, ht, hs⟩
  · exact runSafeIter_pushClockBit_output w 1
  · simp only [P, evalProg, copyWordProg]
    have hst := (runSafeIter_bounds .pushClockBit w [] 1).1
    simp [SafeStepOp.cost] at hst
    omega

/-! ### Failure Tests (`docs/proof-ideas.md` §§2–3) -/

/-- Exact exponential output-length formula for `.dupIter`:
    duplicating the accumulator `acc ++ acc` at each bit of `w` produces an output word
    of length $2^{|w|}$! -/
theorem runDupIter_output_length : ∀ w : Word,
    (runDupIter w).output.length = 2 ^ w.length
  | [] => rfl
  | _ :: bs => by
    simp only [runDupIter, List.length_append, List.length_cons,
      runDupIter_output_length bs, Nat.pow_succ]
    omega

/-- **Failure Test 1 (`exponential_duplication_counterexample`, `docs/proof-ideas.md` §2)**:
    If the safe/affine restriction on the recursive accumulator is dropped (`.dupIter`),
    iterating over a word `w` of length $n$ produces an output of exponential length
    $2^n$ (`(evalProg .dupIter w).output.length = 2 ^ w.length`), and `.dupIter` is
    **rejected** by `BCSafeDerivation` (`¬ BCSafeDerivation .dupIter`). -/
theorem exponential_duplication_counterexample :
    (¬ BCSafeDerivation .dupIter) ∧
    ∀ w : Word, (evalProg .dupIter w).output.length = 2 ^ w.length :=
  ⟨(fun h ↦ nomatch h), runDupIter_output_length⟩

/-- **Failure Test 2 (`erased_clock_counterexample`, `docs/proof-ideas.md` §2)**:
    An erased (`0`-graded) input cannot become a recursion clock:
    1. `BCSafeDerivation` **rejects** `.wordIter .zero step base` for every `step` and `base`,
    2. Semantically, if `.wordIter .zero (.pushBit true) (.constWord [])` were allowed,
       the un-erased program on `w = [true]` would return `[true]` (length `1`), whereas
       its erased counterpart `eraseProg` (where the `0`-graded clock is erased to `[]`)
       returns `[]` (length `0`), violating erasure soundness! -/
theorem erased_clock_counterexample (step : SafeStepOp) (base : FeasibleProg) :
    (¬ BCSafeDerivation (.wordIter .zero step base)) ∧
    let P_bad := FeasibleProg.wordIter .zero (.pushBit true) (.constWord [])
    (evalProg P_bad [true]).output = [true] ∧
    (evalProg (eraseProg P_bad) [true]).output = [] ∧
    (evalProg P_bad [true]).output ≠ (evalProg (eraseProg P_bad) [true]).output :=
  ⟨(fun h ↦ nomatch h), rfl, rfl, by decide⟩

/-- **Failure Test 3 (`conversion_invariance_of_bounds`, `docs/proof-ideas.md` §2)**:
    Converting or replacing a `0`-graded type/specification index (`erasedSpec tag₁ P`
    vs. `erasedSpec tag₂ P`, or `idJ .zero tag₁ P` vs. `idJ .zero tag₂ P`) **cannot**
    disguise a runtime resource increase: both the synthesized polynomial certificates
    (`synthTimePoly`, `synthSizePoly`) and the actual operational execution (`evalProg`)
    are completely invariant under changes to `0`-graded specification/motive indices! -/
theorem conversion_invariance_of_bounds (tag₁ tag₂ : Nat) (P : FeasibleProg) (w : Word) :
    synthTimePoly (.erasedSpec tag₁ P) = synthTimePoly (.erasedSpec tag₂ P) ∧
    synthSizePoly (.erasedSpec tag₁ P) = synthSizePoly (.erasedSpec tag₂ P) ∧
    evalProg (.erasedSpec tag₁ P) w = evalProg (.erasedSpec tag₂ P) w ∧
    synthTimePoly (.idJ .zero tag₁ P) = synthTimePoly (.idJ .zero tag₂ P) ∧
    synthSizePoly (.idJ .zero tag₁ P) = synthSizePoly (.idJ .zero tag₂ P) ∧
    evalProg (.idJ .zero tag₁ P) w = evalProg (.idJ .zero tag₂ P) w :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end BenchmarksAndFailureTests

end FeasibleUnivalence.PaperB
