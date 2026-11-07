/-
  FeasibleUnivalence/PaperC.lean

  Formalization of **M11 & Paper C (Gate G5)**:
  *"The Cost of Transport"*

  This module builds on `Modality`, `Usage`, `Erasure`, `HeapMachine`, `PaperA`, and
  `PaperB` to formalize the core mathematical results of **M11 & Paper C**
  (`docs/research-proposal.md` and `docs/proof-ideas.md` §§4 & 6):

  1. **Boundary Obstruction Theorem (`transport_obstruction_xor`, `docs/proof-ideas.md` §4)**:
     - For any total Boolean function on binary words $h : \mathrm{Word} \to \mathrm{Bool}$,
       defines the involution
       $$e_h(x, b) = (x, \operatorname{xor}\;b\;(h(x))).$$
     - Proves $e_h \circ e_h = \mathrm{id}$ (`eh_involution`), so $e_h$ is a self-inverse
       equivalence on $\mathrm{Word} \times \mathrm{Bool}$, and $e_h(x, \mathrm{false}).2 = h(x)$
       (`eh_recovers_h`).
     - Proves `transport_obstruction_xor`: any runtime transport implementation of $e_h$
       running in time $\le B(|x|)$ yields an algorithm computing $h(x)$ in time
       $\le B(|x|) + 1$; contrapositively, if $h$ exceeds budget $B(|x|) + 1$ on any word,
       $e_h$ cannot be admitted as a runtime transport within budget $B(|x|)$.

  2. **Explicit Cartesian Cubical Syntax & Quantitative Equivalences (`Dim`, `QuantEquiv`, `CubicalTerm`)**:
     - Formalizes an explicit **Cartesian** cubical interval (`Dim`: `.d0`, `.d1`, `.dvar i`)
       with Cartesian dimension substitutions `DimSubst` (no De Morgan involution `1 - i`
       or lattice connections assumed).
     - Defines `QuantEquiv`: bundles executable forward/backward `FeasibleProg` realizers,
       their `BCSafeDerivation` proofs, synthesized polynomial time/size certificates,
       and an abstract correspondence relation `rel : Word → Word → Prop` (supporting both
       bijections and non-bijective abstraction relations).
     - Distinguishes M11's two-grade `CTT0ω` discipline (`0` = non-exact/erased vs.
       `ω` = exact/unbounded runtime) from Paper C's quantitative discipline (`WellResourcedCubical`),
       which charges polynomial time/size certificates on `1`/`ω`-graded coercions while
       erasing `0`-graded specification paths.

  3. **Stability & Quantitative Transport Simulation (`paper_C_quantitative_transport_soundness`)**:
     - Proves stability of `WellResourcedCubical`, `synthCubicalTime`, and `synthCubicalSize`
       under Cartesian dimension substitution `DimSubst` (`cubical_certs_substDim_eq`,
       `WellResourcedCubical.substDim`).
     - Proves `paper_C_quantitative_transport_soundness` and `vType_transport_simulation`:
       every well-resourced Cartesian cubical term evaluates within its synthesized
       polynomial time and output-size bounds, and coercion `coe .d0 .d1` across a
       `V`-type `.vType (.dvar 0) .wordTy .wordTy .one eqv` simulates direct execution
       of `eqv.fwd` while preserving the abstraction relation `eqv.rel`.

  4. **Gate G5 Failure Tests (`docs/proof-ideas.md` §4)**:
     - `erased_equiv_cannot_execute_at_runtime`: a `0`-graded equivalence cannot be used
       for runtime coercion `coe` or projection `vProj`.
     - `hcomp_linear_duplication_rejected`: duplicating a `1`-graded linear resource
       across `cap` and `tube` in `hcomp` fails in `ZeroOneMany.linearityModality`.
     - `zero_cost_cast_fallacy`: no certified `QuantEquiv` conversion can have `0` step cost.

  5. **Finite-Map Representation Transfer Benchmark (`FinMapSpec`, `ListMap`, `TreeMap`, `docs/proof-ideas.md` §6)**:
     - Formalizes abstract finite maps (`Nat → Option Nat`), association lists (`ListMap`),
       and binary search trees (`TreeMap` with `ValidBST`),
     - Proves `listMap_abstraction_not_injective` (non-bijective concrete representations
       denoting the same abstract map),
     - Proves `finMap_client_transfer_theorem`: a batch lookup/insert client transfers
       its correctness specification across `ListMap` and `TreeMap` while adapting its
       explicit step-cost bound to each representation (`O(|L|)` vs. `O(depth(T))`).
-/

import FeasibleUnivalence.PaperB

namespace FeasibleUnivalence.PaperC

open FeasibleUnivalence
open FeasibleUnivalence.PaperB

/-! ## 1. Boundary Obstruction Theorem (`transport_obstruction_xor`, `docs/proof-ideas.md` §4) -/

section BoundaryObstruction

/-- For any total Boolean function on binary words `h : Word → Bool`, define the map
    $$e_h(x, b) = (x, \operatorname{xor}\;b\;(h(x)))$$
    on `Word × Bool` (`docs/proof-ideas.md` §4). -/
def eh (h : Word → Bool) (p : Word × Bool) : Word × Bool :=
  (p.1, bne p.2 (h p.1))

/-- `eh h` is a strict involution (`eh h (eh h p) = p`) for **every** Boolean function `h`
    — regardless of the computational complexity of `h`! -/
theorem eh_involution (h : Word → Bool) (p : Word × Bool) :
    eh h (eh h p) = p := by
  rcases p with ⟨x, b⟩
  simp only [eh, Prod.mk.injEq, true_and]
  cases b <;> cases h x <;> rfl

/-- Hence `eh h` has a two-sided inverse (namely `eh h` itself) and defines a mathematical
    bijection on `Word × Bool`. -/
theorem eh_bijective (h : Word → Bool) :
    (∀ p : Word × Bool, eh h (eh h p) = p) ∧
    Function.Injective (eh h) ∧
    Function.Surjective (eh h) := by
  refine ⟨eh_involution h, ?_, ?_⟩
  · intro p₁ p₂ heq
    have h1 := congrArg (eh h) heq
    rwa [eh_involution, eh_involution] at h1
  · intro p
    exact ⟨eh h p, eh_involution h p⟩

/-- Applying `eh h` to `(x, false)` and projecting the second component recovers `h x`! -/
theorem eh_recovers_h (h : Word → Bool) (x : Word) :
    (eh h (x, false)).2 = h x := by
  simp only [eh]
  cases h x <;> rfl

/-- Encoding of `Word × Bool` as a single `Word` by prefixing the Boolean tag `b :: x`,
    with decoding `(w.tail, w.headD false)`. -/
def encodeWordBool (p : Word × Bool) : Word :=
  p.2 :: p.1

def decodeWordBool (w : Word) : Word × Bool :=
  (w.tail, w.headD false)

@[simp] theorem decode_encodeWordBool (p : Word × Bool) :
    decodeWordBool (encodeWordBool p) = p := by
  rcases p with ⟨x, b⟩
  rfl

@[simp] theorem length_encodeWordBool (p : Word × Bool) :
    (encodeWordBool p).length = p.1.length + 1 := rfl

/-- **Boundary Obstruction Theorem (`transport_obstruction_xor`, `docs/proof-ideas.md` §4)**:
    For any total Boolean function `h : Word → Bool`:
    1. `eh h` is a self-inverse bijection (`eh h (eh h p) = p`),
    2. `(eh h (x, false)).2 = h x`,
    3. If `P : FeasibleProg` (`BCSafeDerivation P`) implements `eh h` under
       `(encodeWordBool, decodeWordBool)`, then `P` applied to `false :: x` computes
       `h x` as its output head bit in at most `(synthTimePoly P).eval (x.length + 1)` steps.
       Contrapositively, if `h` cannot be computed within `(synthTimePoly P).eval (|x| + 1)`
       steps, then `eh h` **cannot** be realized as a runtime transport by `P`! -/
theorem transport_obstruction_xor (h : Word → Bool) :
    (∀ p : Word × Bool, eh h (eh h p) = p) ∧
    (∀ x : Word, (eh h (x, false)).2 = h x) ∧
    (∀ (P : FeasibleProg),
      BCSafeDerivation P →
      (∀ p : Word × Bool, decodeWordBool (evalProg P (encodeWordBool p)).output = eh h p) →
      ∀ x : Word,
        ((evalProg P (false :: x)).output.headD false = h x) ∧
        (evalProg P (false :: x)).steps ≤ (synthTimePoly P).eval (x.length + 1)) := by
  refine ⟨eh_involution h, eh_recovers_h h, ?_⟩
  intro P hP hImpl x
  have h1 := hImpl (x, false)
  simp only [encodeWordBool, decodeWordBool] at h1
  have h2 : (evalProg P (false :: x)).output.headD false = (eh h (x, false)).2 :=
    congrArg Prod.snd h1
  rw [eh_recovers_h] at h2
  have hbound := (paper_B_polytime_soundness hP (false :: x) (Nat.le_refl (x.length + 1))).1
  exact ⟨h2, hbound⟩

end BoundaryObstruction

/-! ## 2. Cartesian Cubical Syntax & Quantitative Equivalences (`Dim`, `QuantEquiv`, `CubicalTerm`)

Following `docs/proof-ideas.md` §4, we fix an explicit **Cartesian** cubical presentation:
- Dimension expressions `Dim` consist of endpoints `.d0`, `.d1` and dimension variables
  `.dvar i` (closed under Cartesian dimension substitution `DimSubst`, without De Morgan
  negation `1 - i` or binary connections `i ∧ j`),
- Runtime coercions across `V`-types require an explicit `QuantEquiv` certificate package
  when the equivalence grade is live (`.one` or `.omega`), while `0`-graded equivalences
  are specification-only and cannot be executed at runtime. -/

/-- Cartesian interval dimensions (`0`, `1`, or dimension variable `i`). -/
inductive Dim : Type where
  | d0 : Dim
  | d1 : Dim
  | dvar (i : Nat) : Dim
  deriving DecidableEq, Repr

/-- A Cartesian dimension substitution maps each dimension variable `i : Nat` to a `Dim`. -/
abbrev DimSubst := Nat → Dim

namespace Dim

/-- Apply a Cartesian dimension substitution `σ : DimSubst` to a dimension `r : Dim`. -/
def subst (σ : DimSubst) : Dim → Dim
  | .d0 => .d0
  | .d1 => .d1
  | .dvar i => σ i

/-- Identity dimension substitution. -/
def idSubst : DimSubst := .dvar

/-- Specialize dimension variable `0` to `r₀ : Dim`. -/
def singleSubst (r₀ : Dim) : DimSubst
  | 0 => r₀
  | i + 1 => .dvar i

@[simp] theorem subst_id (r : Dim) : r.subst idSubst = r := by
  cases r <;> rfl

end Dim

/-- **Quantitative Equivalence Package (`QuantEquiv`)**:
    attaches executable forward and backward `FeasibleProg` realizers, their
    `BCSafeDerivation` proofs, and an abstract correspondence relation `rel : Word → Word → Prop`
    (supporting both strict bijections and non-bijective abstraction relations!). -/
structure QuantEquiv where
  fwd : FeasibleProg
  bwd : FeasibleProg
  fwdSafe : BCSafeDerivation fwd
  bwdSafe : BCSafeDerivation bwd
  rel : Word → Word → Prop
  fwd_preserves_rel : ∀ w : Word, rel w (evalProg fwd w).output

namespace QuantEquiv

/-- Synthesized forward time polynomial of `e : QuantEquiv`. -/
def fwdTime (e : QuantEquiv) : Poly := synthTimePoly e.fwd

/-- Synthesized forward output-size polynomial of `e : QuantEquiv`. -/
def fwdSize (e : QuantEquiv) : Poly := synthSizePoly e.fwd

/-- Synthesized backward time polynomial of `e : QuantEquiv`. -/
def bwdTime (e : QuantEquiv) : Poly := synthTimePoly e.bwd

/-- Synthesized backward output-size polynomial of `e : QuantEquiv`. -/
def bwdSize (e : QuantEquiv) : Poly := synthSizePoly e.bwd

/-- Identity quantitative equivalence (`fwd = .idProg`, `bwd = .idProg`, `rel = Eq`). -/
def idEquiv : QuantEquiv where
  fwd := .idProg
  bwd := .idProg
  fwdSafe := .idProg
  bwdSafe := .idProg
  rel := Eq
  fwd_preserves_rel _ := rfl

/-- Symmetric dual of a `QuantEquiv` when `bwd` also satisfies `rel` in reverse. -/
def symmEquiv (e : QuantEquiv)
    (hbwd_rel : ∀ w : Word, e.rel (evalProg e.bwd w).output w) : QuantEquiv where
  fwd := e.bwd
  bwd := e.fwd
  fwdSafe := e.bwdSafe
  bwdSafe := e.fwdSafe
  rel w₁ w₂ := e.rel w₂ w₁
  fwd_preserves_rel := hbwd_rel

end QuantEquiv

/-- **Cartesian Cubical Type Line (`CubicalType`)**:
    represents a type in a dimension context (for coercion `coe r r'`):
    - `.wordTy`: base type of binary words (`Word`),
    - `.vType r A B eqvGrade eqv`: Cartesian `V`-type along dimension `r : Dim`
      connecting `A` (at `r = .d0`) and `B` (at `r = .d1`) via `eqv : QuantEquiv`
      at grade `eqvGrade : ZeroOneMany`. -/
inductive CubicalType : Type where
  | wordTy : CubicalType
  | vType (r : Dim) (A B : CubicalType) (eqvGrade : ZeroOneMany) (eqv : QuantEquiv) : CubicalType

namespace CubicalType

/-- Apply a Cartesian dimension substitution `σ : DimSubst` to a `CubicalType`. -/
def substDim (σ : DimSubst) : CubicalType → CubicalType
  | .wordTy => .wordTy
  | .vType r A B g eqv => .vType (r.subst σ) (A.substDim σ) (B.substDim σ) g eqv

@[simp] theorem substDim_id : ∀ A : CubicalType, A.substDim Dim.idSubst = A
  | .wordTy => rfl
  | .vType r A B g eqv => by
    simp [substDim, substDim_id A, substDim_id B]

end CubicalType

/-- **Cartesian Cubical Term Syntax (`CubicalTerm`)**:
    extends `FeasibleProg` with Cartesian cubical operations:
    - `.baseProg P`: embeds a `FeasibleProg`,
    - `.pathLam body`: dimension abstraction `⟨i⟩ body`,
    - `.pathApp p r`: dimension application `p @ r`,
    - `.vIn r a b`: `V`-introduction term,
    - `.vProj r g eqv v`: `V`-projection term,
    - `.coe r r' line body`: Cartesian coercion from `r` to `r'` along `line : CubicalType`,
    - `.hcomp r r' capGrade tubeGrade cap tube`: homogeneous composition combining `cap`
      (at grade `capGrade`) with `tube` step (at grade `tubeGrade`). -/
inductive CubicalTerm : Type where
  | baseProg (P : FeasibleProg) : CubicalTerm
  | pathLam (body : CubicalTerm) : CubicalTerm
  | pathApp (p : CubicalTerm) (r : Dim) : CubicalTerm
  | vIn (r : Dim) (a b : CubicalTerm) : CubicalTerm
  | vProj (r : Dim) (eqvGrade : ZeroOneMany) (eqv : QuantEquiv) (v : CubicalTerm) : CubicalTerm
  | coe (r r' : Dim) (line : CubicalType) (body : CubicalTerm) : CubicalTerm
  | hcomp (r r' : Dim) (capGrade tubeGrade : ZeroOneMany) (cap tube : CubicalTerm) : CubicalTerm

namespace CubicalTerm

/-- Apply a Cartesian dimension substitution `σ : DimSubst` to a `CubicalTerm`. -/
def substDim (σ : DimSubst) : CubicalTerm → CubicalTerm
  | .baseProg P => .baseProg P
  | .pathLam body => .pathLam (body.substDim σ)
  | .pathApp p r => .pathApp (p.substDim σ) (r.subst σ)
  | .vIn r a b => .vIn (r.subst σ) (a.substDim σ) (b.substDim σ)
  | .vProj r g eqv v => .vProj (r.subst σ) g eqv (v.substDim σ)
  | .coe r r' line body => .coe (r.subst σ) (r'.subst σ) (line.substDim σ) (body.substDim σ)
  | .hcomp r r' cg tg cap tube =>
      .hcomp (r.subst σ) (r'.subst σ) cg tg (cap.substDim σ) (tube.substDim σ)

end CubicalTerm

/-! ## 3. Well-Resourced Cubical Derivations, Certificate Synthesis, & Operational Semantics -/

/-- A `CubicalType` has **executable runtime equivalences (`ExecutableTypeLine`)** when
    every `V`-type inside it has a non-erased equivalence grade (`eqvGrade ≠ .zero`).
    By contrast, M11 (`CTT0ω`) only tracks `{0, ω}` without polynomial certificates;
    here a `0`-graded equivalence is permitted in specifications (`SpecTypeLine`) but
    forbidden in runtime `coe` / `vProj`! -/
def ExecutableTypeLine : CubicalType → Prop
  | .wordTy => True
  | .vType _ A B g _ => g ≠ .zero ∧ ExecutableTypeLine A ∧ ExecutableTypeLine B

theorem ExecutableTypeLine.substDim (σ : DimSubst) :
    ∀ {A : CubicalType}, ExecutableTypeLine A → ExecutableTypeLine (A.substDim σ)
  | .wordTy, _ => trivial
  | .vType _ _ _ _ _, ⟨hg, hA, hB⟩ => ⟨hg, hA.substDim σ, hB.substDim σ⟩

/-- **Well-Resourced Cartesian Cubical Derivation (`WellResourcedCubical 𝕄 t`)**:
    ensures that:
    1. Embedded base programs satisfy `BCSafeDerivation`,
    2. Runtime `vProj` and `coe` only use `V`-types with non-erased (`eqvGrade ≠ .zero`)
       quantitative equivalences,
    3. `hcomp` respects the modality's resource addition (`𝕄.le 𝕄.one (𝕄.add capGrade tubeGrade)`
       when sharing a `1`-graded input across `cap` and `tube`, or only uses one branch). -/
inductive WellResourcedCubical (𝕄 : Modality ZeroOneMany) : CubicalTerm → Prop where
  | baseProg {P : FeasibleProg} :
      BCSafeDerivation P →
      WellResourcedCubical 𝕄 (.baseProg P)
  | pathLam {body : CubicalTerm} :
      WellResourcedCubical 𝕄 body →
      WellResourcedCubical 𝕄 (.pathLam body)
  | pathApp {p : CubicalTerm} (r : Dim) :
      WellResourcedCubical 𝕄 p →
      WellResourcedCubical 𝕄 (.pathApp p r)
  | vIn (r : Dim) {a b : CubicalTerm} :
      WellResourcedCubical 𝕄 a →
      WellResourcedCubical 𝕄 b →
      WellResourcedCubical 𝕄 (.vIn r a b)
  | vProj (r : Dim) {g : ZeroOneMany} (eqv : QuantEquiv) {v : CubicalTerm} :
      g ≠ .zero →
      WellResourcedCubical 𝕄 v →
      WellResourcedCubical 𝕄 (.vProj r g eqv v)
  | coe (r r' : Dim) {line : CubicalType} {body : CubicalTerm} :
      ExecutableTypeLine line →
      WellResourcedCubical 𝕄 body →
      WellResourcedCubical 𝕄 (.coe r r' line body)
  | hcomp (r r' : Dim) {cg tg : ZeroOneMany} {cap tube : CubicalTerm} :
      𝕄.le 𝕄.one (𝕄.add cg tg) →
      WellResourcedCubical 𝕄 cap →
      WellResourcedCubical 𝕄 tube →
      WellResourcedCubical 𝕄 (.hcomp r r' cg tg cap tube)

/-- **Dimension-Substitution Stability of `WellResourcedCubical` (`WellResourcedCubical.substDim`)**:
    applying any Cartesian dimension substitution `σ : DimSubst` preserves `WellResourcedCubical`! -/
theorem WellResourcedCubical.substDim {𝕄 : Modality ZeroOneMany} (σ : DimSubst)
    {t : CubicalTerm} (ht : WellResourcedCubical 𝕄 t) :
    WellResourcedCubical 𝕄 (t.substDim σ) := by
  induction ht with
  | baseProg hP => exact .baseProg hP
  | pathLam _ ih => exact .pathLam ih
  | pathApp r _ ih => exact .pathApp (r.subst σ) ih
  | vIn r _ _ iha ihb => exact .vIn (r.subst σ) iha ihb
  | vProj r eqv hg _ ih => exact .vProj (r.subst σ) eqv hg ih
  | coe r r' hline _ ih => exact .coe (r.subst σ) (r'.subst σ) (hline.substDim σ) ih
  | hcomp r r' hle _ _ ihc iht => exact .hcomp (r.subst σ) (r'.subst σ) hle ihc iht

/-- Synthesize the output-size polynomial of coercing along `line : CubicalType`
    starting from input size polynomial `s_in : Poly`. -/
def synthLineSize : CubicalType → Poly → Poly
  | .wordTy, s_in => s_in
  | .vType _ A B _ eqv, s_in =>
      let sA := synthLineSize A s_in
      let sB := synthLineSize B s_in
      .add s_in (.add (eqv.fwdSize.comp sA) (eqv.bwdSize.comp sB))

/-- Synthesize the time-cost polynomial of coercing along `line : CubicalType`
    starting from `(t_in, s_in)`. -/
def synthLineTime : CubicalType → Poly → Poly → Poly
  | .wordTy, t_in, _ => .add t_in (.const 1)
  | .vType _ A B _ eqv, t_in, s_in =>
      let sA := synthLineSize A s_in
      let sB := synthLineSize B s_in
      let tA := synthLineTime A t_in s_in
      let tB := synthLineTime B t_in s_in
      .add t_in
        (.add (.add tA (eqv.fwdTime.comp sA))
          (.add (.add tB (eqv.bwdTime.comp sB)) (.const 2)))

/-- **Static Output-Size Certificate Synthesis for `CubicalTerm` (`synthCubicalSize`)**. -/
def synthCubicalSize : CubicalTerm → Poly
  | .baseProg P => synthSizePoly P
  | .pathLam body => synthCubicalSize body
  | .pathApp p _ => synthCubicalSize p
  | .vIn _ a b => .add (synthCubicalSize a) (synthCubicalSize b)
  | .vProj _ _ eqv v =>
      .add (synthCubicalSize v) (eqv.fwdSize.comp (synthCubicalSize v))
  | .coe _ _ line body =>
      synthLineSize line (synthCubicalSize body)
  | .hcomp _ _ _ _ cap tube =>
      .add (synthCubicalSize cap) ((synthCubicalSize tube).comp (synthCubicalSize cap))

/-- **Static Time-Bound Certificate Synthesis for `CubicalTerm` (`synthCubicalTime`)**. -/
def synthCubicalTime : CubicalTerm → Poly
  | .baseProg P => synthTimePoly P
  | .pathLam body => synthCubicalTime body
  | .pathApp p _ => .add (synthCubicalTime p) (.const 1)
  | .vIn _ a b => .add (.add (synthCubicalTime a) (synthCubicalTime b)) (.const 1)
  | .vProj _ _ eqv v =>
      .add (.add (synthCubicalTime v) (eqv.fwdTime.comp (synthCubicalSize v))) (.const 1)
  | .coe _ _ line body =>
      synthLineTime line (synthCubicalTime body) (synthCubicalSize body)
  | .hcomp _ _ _ _ cap tube =>
      .add (.add (synthCubicalTime cap) ((synthCubicalTime tube).comp (synthCubicalSize cap))) (.const 1)

/-- **Dimension-Substitution Invariance of Static Cubical Certificates (`cubical_certs_substDim_eq`)**:
    Cartesian dimension substitution `σ : DimSubst` leaves `synthCubicalSize` and
    `synthCubicalTime` **definitionally invariant**! -/
theorem synthLineSize_substDim (σ : DimSubst) :
    ∀ (line : CubicalType) (s_in : Poly),
      synthLineSize (line.substDim σ) s_in = synthLineSize line s_in
  | .wordTy, _ => rfl
  | .vType _ A B _ _, s_in => by
    simp [CubicalType.substDim, synthLineSize, synthLineSize_substDim σ A, synthLineSize_substDim σ B]

theorem synthLineTime_substDim (σ : DimSubst) :
    ∀ (line : CubicalType) (t_in s_in : Poly),
      synthLineTime (line.substDim σ) t_in s_in = synthLineTime line t_in s_in
  | .wordTy, _, _ => rfl
  | .vType _ A B _ _, t_in, s_in => by
    simp [CubicalType.substDim, synthLineTime, synthLineSize_substDim σ A, synthLineSize_substDim σ B,
      synthLineTime_substDim σ A, synthLineTime_substDim σ B]

theorem cubical_certs_substDim_eq (σ : DimSubst) (t : CubicalTerm) :
    synthCubicalSize (t.substDim σ) = synthCubicalSize t ∧
    synthCubicalTime (t.substDim σ) = synthCubicalTime t := by
  induction t with
  | baseProg _ => exact ⟨rfl, rfl⟩
  | pathLam _ ih => exact ih
  | pathApp _ _ ih =>
    rcases ih with ⟨hs, ht⟩
    exact ⟨hs, congrArg (fun p ↦ Poly.add p (.const 1)) ht⟩
  | vIn _ _ _ iha ihb =>
    rcases iha with ⟨hsa, hta⟩
    rcases ihb with ⟨hsb, htb⟩
    simp [CubicalTerm.substDim, synthCubicalSize, synthCubicalTime, hsa, hta, hsb, htb]
  | vProj _ _ _ _ ih =>
    rcases ih with ⟨hs, ht⟩
    simp [CubicalTerm.substDim, synthCubicalSize, synthCubicalTime, hs, ht]
  | coe _ _ line _ ih =>
    rcases ih with ⟨hs, ht⟩
    simp [CubicalTerm.substDim, synthCubicalSize, synthCubicalTime,
      synthLineSize_substDim, synthLineTime_substDim, hs, ht]
  | hcomp _ _ _ _ _ _ ihc iht =>
    rcases ihc with ⟨hsc, htc⟩
    rcases iht with ⟨hst, htt⟩
    simp [CubicalTerm.substDim, synthCubicalSize, synthCubicalTime, hsc, htc, hst, htt]

/-- Operational execution of coercion along `line : CubicalType` from `r` to `r'`
    on an already-evaluated `(val, steps)` pair. -/
def evalCoeLine (r r' : Dim) : CubicalType → ExecResult → ExecResult
  | .wordTy, res => ⟨res.output, res.steps + 1⟩
  | .vType _ A B _ eqv, res =>
      if r = r' then
        ⟨res.output, res.steps + 1⟩
      else match r, r' with
        | .d0, .d1 =>
            let resA := evalCoeLine .d0 .d1 A res
            let resFwd := evalProg eqv.fwd resA.output
            ⟨resFwd.output, resA.steps + resFwd.steps + 1⟩
        | .d1, .d0 =>
            let resB := evalCoeLine .d1 .d0 B res
            let resBwd := evalProg eqv.bwd resB.output
            ⟨resBwd.output, resB.steps + resBwd.steps + 1⟩
        | _, _ =>
            ⟨res.output, res.steps + 1⟩

/-- Concrete operational evaluator for `CubicalTerm`. -/
def evalCubical : CubicalTerm → Word → ExecResult
  | .baseProg P, w => evalProg P w
  | .pathLam body, w => evalCubical body w
  | .pathApp p _, w =>
      let res := evalCubical p w
      ⟨res.output, res.steps + 1⟩
  | .vIn r a b, w =>
      if r = .d0 then
        let ra := evalCubical a w
        ⟨ra.output, ra.steps + 1⟩
      else
        let rb := evalCubical b w
        ⟨rb.output, rb.steps + 1⟩
  | .vProj r _ eqv v, w =>
      let rv := evalCubical v w
      if r = .d0 then
        let rfwd := evalProg eqv.fwd rv.output
        ⟨rfwd.output, rv.steps + rfwd.steps + 1⟩
      else
        ⟨rv.output, rv.steps + 1⟩
  | .coe r r' line body, w =>
      evalCoeLine r r' line (evalCubical body w)
  | .hcomp r r' _ _ cap tube, w =>
      let rcap := evalCubical cap w
      if r = r' then
        ⟨rcap.output, rcap.steps + 1⟩
      else
        let rtube := evalCubical tube rcap.output
        ⟨rtube.output, rcap.steps + rtube.steps + 1⟩

/-- Helper lemma: `evalCoeLine` respects `synthLineTime` and `synthLineSize`. -/
theorem evalCoeLine_bounds (r r' : Dim) (line : CubicalType) (res : ExecResult)
    {t_in s_in : Poly} {n : Nat}
    (ht : res.steps ≤ t_in.eval n)
    (hs : res.output.length ≤ s_in.eval n) :
    (evalCoeLine r r' line res).steps ≤ (synthLineTime line t_in s_in).eval n ∧
    (evalCoeLine r r' line res).output.length ≤ (synthLineSize line s_in).eval n := by
  induction line generalizing r r' res with
  | wordTy =>
    simp only [evalCoeLine, synthLineTime, synthLineSize, Poly.eval_add, Poly.eval_const]
    exact ⟨Nat.add_le_add_right ht 1, hs⟩
  | vType rv A B g eqv ihA ihB =>
    simp only [evalCoeLine, synthLineTime, synthLineSize,
      QuantEquiv.fwdTime, QuantEquiv.fwdSize, QuantEquiv.bwdTime, QuantEquiv.bwdSize,
      Poly.eval_add, Poly.eval_comp, Poly.eval_const]
    rcases ihA .d0 .d1 res ht hs with ⟨htA, hsA⟩
    rcases ihB .d1 .d0 res ht hs with ⟨htB, hsB⟩
    rcases paper_B_polytime_soundness eqv.fwdSafe (evalCoeLine .d0 .d1 A res).output hsA with
      ⟨ht_fwd, hs_fwd, _⟩
    rcases paper_B_polytime_soundness eqv.bwdSafe (evalCoeLine .d1 .d0 B res).output hsB with
      ⟨ht_bwd, hs_bwd, _⟩
    by_cases h1 : r = r'
    · rw [if_pos h1]
      dsimp only
      exact ⟨by omega, by omega⟩
    · rw [if_neg h1]
      cases r <;> cases r' <;> dsimp only <;> exact ⟨by omega, by omega⟩

/-! ## 4. Main Theorems of Paper C (`paper_C_quantitative_transport_soundness`, `vType_transport_simulation`) -/

/-- **Main Quantitative Transport Soundness Theorem of Paper C (`paper_C_quantitative_transport_soundness`, Gate G5)**:
    For every modality `𝕄` on `ZeroOneMany`, every well-resourced Cartesian cubical term
    `ht : WellResourcedCubical 𝕄 t`, every Cartesian dimension substitution `σ : DimSubst`,
    and every input word `w : Word` with `w.length ≤ n`:
    1. **Polynomial Time Soundness**: `(evalCubical t w).steps ≤ (synthCubicalTime t).eval n`,
    2. **Polynomial Size Soundness**: `(evalCubical t w).output.length ≤ (synthCubicalSize t).eval n`,
    3. **Dimension-Substitution Stability**: `t.substDim σ` is also `WellResourcedCubical 𝕄`
       and satisfies the exact same synthesized polynomial bounds! -/
theorem paper_C_quantitative_transport_soundness
    {𝕄 : Modality ZeroOneMany} {t : CubicalTerm}
    (ht : WellResourcedCubical 𝕄 t)
    (w : Word) {n : Nat} (hn : w.length ≤ n) :
    (evalCubical t w).steps ≤ (synthCubicalTime t).eval n ∧
    (evalCubical t w).output.length ≤ (synthCubicalSize t).eval n := by
  induction ht generalizing w n with
  | baseProg hP =>
    rcases paper_B_polytime_soundness hP w hn with ⟨ht_p, hs_p, _⟩
    exact ⟨ht_p, hs_p⟩
  | pathLam _ ih =>
    exact ih w hn
  | pathApp _ _ ih =>
    rcases ih w hn with ⟨ht_p, hs_p⟩
    simp only [evalCubical, synthCubicalTime, synthCubicalSize, Poly.eval_add, Poly.eval_const]
    exact ⟨Nat.add_le_add_right ht_p 1, hs_p⟩
  | vIn r _ _ iha ihb =>
    rcases iha w hn with ⟨hta, hsa⟩
    rcases ihb w hn with ⟨htb, hsb⟩
    simp only [evalCubical, synthCubicalTime, synthCubicalSize, Poly.eval_add, Poly.eval_const]
    by_cases hr : r = .d0
    · rw [if_pos hr]; dsimp only; exact ⟨by omega, by omega⟩
    · rw [if_neg hr]; dsimp only; exact ⟨by omega, by omega⟩
  | vProj r eqv _ _ ih =>
    rcases ih w hn with ⟨htv, hsv⟩
    simp only [evalCubical, synthCubicalTime, synthCubicalSize,
      QuantEquiv.fwdTime, QuantEquiv.fwdSize,
      Poly.eval_add, Poly.eval_comp, Poly.eval_const]
    rcases paper_B_polytime_soundness eqv.fwdSafe (evalCubical _ w).output hsv with ⟨ht_fwd, hs_fwd, _⟩
    by_cases hr : r = .d0
    · rw [if_pos hr]; dsimp only; exact ⟨by omega, by omega⟩
    · rw [if_neg hr]; dsimp only; exact ⟨by omega, by omega⟩
  | coe r r' _ _ ih =>
    rcases ih w hn with ⟨ht_b, hs_b⟩
    exact evalCoeLine_bounds r r' _ (evalCubical _ w) ht_b hs_b
  | hcomp r r' _ _ _ ihc iht =>
    rcases ihc w hn with ⟨htc, hsc⟩
    rcases iht (evalCubical _ w).output hsc with ⟨htt, hst⟩
    simp only [evalCubical, synthCubicalTime, synthCubicalSize, Poly.eval_add, Poly.eval_comp, Poly.eval_const]
    by_cases hr : r = r'
    · rw [if_pos hr]; dsimp only; exact ⟨by omega, by omega⟩
    · rw [if_neg hr]; dsimp only; exact ⟨by omega, by omega⟩

/-- **Quantitative `V`-Type Transport Simulation Theorem (`vType_transport_simulation`, Gate G5)**:
    Coercing from `.d0` to `.d1` along a Cartesian `V`-type `.vType (.dvar 0) .wordTy .wordTy .one eqv`
    applied to `body : CubicalTerm`:
    1. Produces the **exact same output word** as applying `eqv.fwd` directly to `(evalCubical body w).output`,
    2. Preserves the equivalence's abstraction relation `eqv.rel (evalCubical body w).output (evalCubical coeTerm w).output`,
    3. Executes in `(evalCubical body w).steps + (evalProg eqv.fwd (evalCubical body w).output).steps + 2` steps,
       which is bounded by `(synthCubicalTime coeTerm).eval n`. -/
theorem vType_transport_simulation
    {𝕄 : Modality ZeroOneMany} (eqv : QuantEquiv) {body : CubicalTerm}
    (hbody : WellResourcedCubical 𝕄 body)
    (w : Word) {n : Nat} (hn : w.length ≤ n) :
    let line := CubicalType.vType (.dvar 0) .wordTy .wordTy .one eqv
    let coeTerm := CubicalTerm.coe .d0 .d1 line body
    WellResourcedCubical 𝕄 coeTerm ∧
    (evalCubical coeTerm w).output = (evalProg eqv.fwd (evalCubical body w).output).output ∧
    eqv.rel (evalCubical body w).output (evalCubical coeTerm w).output ∧
    (evalCubical coeTerm w).steps =
      (evalCubical body w).steps + (evalProg eqv.fwd (evalCubical body w).output).steps + 2 ∧
    (evalCubical coeTerm w).steps ≤ (synthCubicalTime coeTerm).eval n ∧
    (evalCubical coeTerm w).output.length ≤ (synthCubicalSize coeTerm).eval n := by
  intro line coeTerm
  have hline : ExecutableTypeLine line := ⟨by decide, trivial, trivial⟩
  have hcoe : WellResourcedCubical 𝕄 coeTerm := .coe .d0 .d1 hline hbody
  rcases paper_C_quantitative_transport_soundness hcoe w hn with ⟨ht, hs⟩
  refine ⟨hcoe, rfl, ?_, ?_, ht, hs⟩
  · exact eqv.fwd_preserves_rel (evalCubical body w).output
  · change (evalCubical body w).steps + 1 + (evalProg eqv.fwd (evalCubical body w).output).steps + 1 =
      (evalCubical body w).steps + (evalProg eqv.fwd (evalCubical body w).output).steps + 2
    omega

/-! ## 5. Gate G5 Failure Tests (`docs/proof-ideas.md` §4) -/

section FailureTests

/-- **Failure Test 1 (`erased_equiv_cannot_execute_at_runtime`, `docs/proof-ideas.md` §4)**:
    An equivalence with grade `.zero` (`eqvGrade = .zero`, specification-only) is
    **rejected** by `WellResourcedCubical` in both runtime coercion `coe` and runtime
    `V`-projection `vProj`. -/
theorem erased_equiv_cannot_execute_at_runtime
    (𝕄 : Modality ZeroOneMany) (r r' : Dim) (eqv : QuantEquiv) (body : CubicalTerm) :
    (¬ WellResourcedCubical 𝕄 (.coe r r' (.vType (.dvar 0) .wordTy .wordTy .zero eqv) body)) ∧
    (¬ WellResourcedCubical 𝕄 (.vProj r .zero eqv body)) := by
  refine ⟨?_, ?_⟩
  · intro h
    cases h with
    | coe _ _ hline _ =>
      exact hline.1 rfl
  · intro h
    cases h with
    | vProj _ _ hg _ =>
      exact hg rfl

/-- **Failure Test 2 (`hcomp_linear_duplication_rejected`, `docs/proof-ideas.md` §4)**:
    In `ZeroOneMany.linearityModality` (`1 + 1 = ω` and `¬ (1 ≤ ω)`), a cubical `hcomp`
    that attempts to use a `1`-graded linear resource at grade `.one` in both `cap`
    and `tube` (`cg = .one`, `tg = .one`) is **rejected** by `WellResourcedCubical`! -/
theorem hcomp_linear_duplication_rejected (r r' : Dim) (cap tube : CubicalTerm) :
    ¬ WellResourcedCubical ZeroOneMany.linearityModality (.hcomp r r' .one .one cap tube) := by
  intro h
  cases h with
  | hcomp _ _ hle _ _ =>
    dsimp [ZeroOneMany.linearityModality, Modality.le] at hle
    cases hle

/-- Every `FeasibleProg` takes at least `1` operational step on every input word `w`. -/
theorem evalProg_steps_pos (P : FeasibleProg) (w : Word) :
    1 ≤ (evalProg P w).steps := by
  cases P with
  | idProg | constWord _ | consBit _ | tailWord =>
    simp [evalProg]
  | wordIter _ step base =>
    simp only [evalProg]
    have h := (runSafeIter_bounds step w (evalProg base w).output (evalProg base w).steps).1
    omega
  | compProg g f =>
    simp only [evalProg]
    omega
  | idJ _ _ body =>
    simp only [evalProg]
    omega
  | erasedSpec _ body =>
    exact evalProg_steps_pos body w
  | dupIter =>
    simp only [evalProg]
    cases w <;> simp [runDupIter] <;> omega

/-- **Failure Test 3 (`zero_cost_cast_fallacy`, `docs/proof-ideas.md` §4)**:
    No certified `QuantEquiv` forward conversion `eqv.fwd` can execute in `0` steps
    (`(evalProg eqv.fwd w).steps ≠ 0`), and any non-degenerate `V`-type coercion
    `coe .d0 .d1` takes at least `3` operational steps — refuting any purported
    "zero-cost cast" for data conversion! -/
theorem zero_cost_cast_fallacy (eqv : QuantEquiv) (body : CubicalTerm) (w : Word) :
    (evalProg eqv.fwd w).steps ≠ 0 ∧
    3 ≤ (evalCubical (.coe .d0 .d1 (.vType (.dvar 0) .wordTy .wordTy .one eqv) body) w).steps := by
  have h1 := evalProg_steps_pos eqv.fwd w
  have h2 := evalProg_steps_pos eqv.fwd (evalCubical body w).output
  refine ⟨Nat.ne_of_gt h1, ?_⟩
  change 3 ≤ (evalCubical body w).steps + 1 + (evalProg eqv.fwd (evalCubical body w).output).steps + 1
  omega

end FailureTests

/-! ## 6. Finite-Map Representation Transfer Benchmark (`FinMapSpec`, `ListMap`, `TreeMap`, `docs/proof-ideas.md` §6)

As required by `docs/research-proposal.md` ("What the paper would contain" item 6) and
`docs/proof-ideas.md` §6 ("Transfer specifications across data implementations"):
- We specify finite-map behavior abstractly (`FinMapSpec := Nat → Option Nat`),
- Supply **association-list (`ListMap`)** and **binary-search-tree (`TreeMap`)** implementations
  connected through abstraction functions (`ListMap.denote`, `TreeMap.denote`) and
  structural invariants (`TreeMap.ValidBST`),
- Prove that multiple concrete representations denote the **same** abstract map
  (`listMap_abstraction_not_injective`), so representation transfer does not assume a
  bijection on carriers,
- Verify a batch lookup/insert client across both implementations, proving that the
  abstract specification transfers identically while the operational step-cost certificate
  adapts explicitly to each implementation (`ListMap` linear scan cost vs. `TreeMap`
  tree-depth cost)! -/

section FiniteMapBenchmark

/-- Abstract mathematical specification of a finite map from keys `Nat` to values `Nat`. -/
abbrev FinMapSpec := Nat → Option Nat

/-- Abstract empty map specification. -/
def emptySpec : FinMapSpec := fun _ ↦ none

/-- Abstract map update specification. -/
def insertSpec (k v : Nat) (m : FinMapSpec) : FinMapSpec :=
  fun q ↦ if q = k then some v else m q

/-! ### 6.1 Implementation 1: Association Lists (`ListMap`) -/

/-- Association-list implementation of finite maps. -/
abbrev ListMap := List (Nat × Nat)

namespace ListMap

def empty : ListMap := []

def insert (k v : Nat) (m : ListMap) : ListMap := (k, v) :: m

/-- Lookup a key `q` in an association list `m`. -/
def lookup (q : Nat) : ListMap → Option Nat
  | [] => none
  | (k, v) :: rest => if q = k then some v else lookup q rest

/-- Operational step cost of looking up `q` in `m` (counts key comparisons + base step). -/
def lookupCost (q : Nat) : ListMap → Nat
  | [] => 1
  | (k, _) :: rest => if q = k then 1 else lookupCost q rest + 1

/-- Abstraction function (`denote`) mapping a concrete `ListMap` to `FinMapSpec`. -/
def denote (m : ListMap) : FinMapSpec := fun q ↦ lookup q m

@[simp] theorem denote_empty : denote empty = emptySpec := rfl

theorem lookup_insert (k v q : Nat) (m : ListMap) :
    lookup q (insert k v m) = insertSpec k v (denote m) q := rfl

theorem denote_insert (k v : Nat) (m : ListMap) :
    denote (insert k v m) = insertSpec k v (denote m) := rfl

/-- Step-cost bound for `ListMap.lookup`: at most `m.length + 1` comparisons. -/
theorem lookupCost_le (q : Nat) : ∀ m : ListMap, lookupCost q m ≤ m.length + 1
  | [] => Nat.le_refl 1
  | (k, _) :: rest => by
    simp only [lookupCost, List.length_cons]
    have ih := lookupCost_le q rest
    split <;> omega

/-- Worst-case linear cost witness for `ListMap`: looking up a key `q` not present in
    `List.replicate n (k, v)` (where `q ≠ k`) takes **exactly `n + 1` steps**! -/
theorem lookupCost_replicate_miss {q k : Nat} (hne : q ≠ k) (v : Nat) :
    ∀ n : Nat, lookupCost q (List.replicate n (k, v)) = n + 1
  | 0 => rfl
  | n + 1 => by
    simp [List.replicate_succ, lookupCost, hne, lookupCost_replicate_miss hne v n]

/-- **Non-Bijectivity of Concrete Carriers (`listMap_abstraction_not_injective`, `docs/proof-ideas.md` §6)**:
    Two distinct concrete association lists `[(0, 42), (0, 99)]` (with shadowed duplicate key `0`)
    and `[(0, 42)]` are unequal as concrete values (`[(0, 42), (0, 99)] ≠ [(0, 42)]`),
    yet denote the **exact same** abstract finite map (`denote [(0, 42), (0, 99)] = denote [(0, 42)]`)! -/
theorem listMap_abstraction_not_injective :
    ([(0, 42), (0, 99)] : ListMap) ≠ [(0, 42)] ∧
    denote [(0, 42), (0, 99)] = denote [(0, 42)] := by
  refine ⟨by decide, ?_⟩
  funext q
  simp only [denote, lookup]
  by_cases h : q = 0 <;> simp [h]

end ListMap

/-! ### 6.2 Implementation 2: Binary Search Trees (`TreeMap`) -/

/-- Binary search tree implementation of finite maps. -/
inductive TreeMap : Type where
  | leaf : TreeMap
  | node (left : TreeMap) (key val : Nat) (right : TreeMap) : TreeMap
  deriving DecidableEq, Repr

namespace TreeMap

/-- Height / depth of a `TreeMap`. -/
def depth : TreeMap → Nat
  | .leaf => 0
  | .node l _ _ r => max l.depth r.depth + 1

/-- Total number of nodes in a `TreeMap`. -/
def size : TreeMap → Nat
  | .leaf => 0
  | .node l _ _ r => l.size + r.size + 1

/-- Binary-search-tree lookup of key `q : Nat`. -/
def lookup (q : Nat) : TreeMap → Option Nat
  | .leaf => none
  | .node l k v r =>
      if q = k then some v
      else if q < k then lookup q l
      else lookup q r

/-- Operational step cost of looking up `q` in a `TreeMap` (counts visited nodes + leaf check). -/
def lookupCost (q : Nat) : TreeMap → Nat
  | .leaf => 1
  | .node l k _ r =>
      if q = k then 1
      else if q < k then lookupCost q l + 1
      else lookupCost q r + 1

/-- Binary-search-tree insertion of `(k, v)`. -/
def insert (k v : Nat) : TreeMap → TreeMap
  | .leaf => .node .leaf k v .leaf
  | .node l k₀ v₀ r =>
      if k = k₀ then .node l k v r
      else if k < k₀ then .node (insert k v l) k₀ v₀ r
      else .node l k₀ v₀ (insert k v r)

/-- All keys in `t` satisfy predicate `P : Nat → Prop`. -/
def AllKeys (P : Nat → Prop) : TreeMap → Prop
  | .leaf => True
  | .node l k _ r => P k ∧ AllKeys P l ∧ AllKeys P r

/-- Binary Search Tree ordering invariant (`ValidBST`). -/
def ValidBST : TreeMap → Prop
  | .leaf => True
  | .node l k _ r =>
      AllKeys (fun x ↦ x < k) l ∧
      AllKeys (fun x ↦ k < x) r ∧
      ValidBST l ∧
      ValidBST r

/-- Abstraction function (`denote`) mapping a `TreeMap` to `FinMapSpec`. -/
def denote (t : TreeMap) : FinMapSpec := fun q ↦ lookup q t

@[simp] theorem denote_leaf : denote .leaf = emptySpec := rfl

/-- Step-cost bound for `TreeMap.lookup`: at most `t.depth + 1` steps! -/
theorem lookupCost_le_depth (q : Nat) : ∀ t : TreeMap, lookupCost q t ≤ t.depth + 1
  | .leaf => Nat.le_refl 1
  | .node l k _ r => by
    simp only [lookupCost, depth]
    have ihl := lookupCost_le_depth q l
    have ihr := lookupCost_le_depth q r
    split
    · omega
    · split <;> omega

theorem allKeys_insert (P : Nat → Prop) {k v : Nat} (hk : P k) :
    ∀ {t : TreeMap}, AllKeys P t → AllKeys P (insert k v t)
  | .leaf, _ => ⟨hk, trivial, trivial⟩
  | .node l k₀ v₀ r, ⟨hk₀, hl, hr⟩ => by
    simp only [insert]
    by_cases h1 : k = k₀
    · simp only [h1, ↓reduceIte]
      exact ⟨hk₀, hl, hr⟩
    · simp only [h1, ↓reduceIte]
      by_cases h2 : k < k₀
      · simp only [h2, ↓reduceIte]
        exact ⟨hk₀, allKeys_insert P hk hl, hr⟩
      · simp only [h2, ↓reduceIte]
        exact ⟨hk₀, hl, allKeys_insert P hk hr⟩

/-- `TreeMap.insert` preserves the `ValidBST` invariant. -/
theorem insert_preserves_bst (k v : Nat) :
    ∀ {t : TreeMap}, ValidBST t → ValidBST (insert k v t)
  | .leaf, _ => ⟨trivial, trivial, trivial, trivial⟩
  | .node l k₀ v₀ r, ⟨hl_keys, hr_keys, hl_bst, hr_bst⟩ => by
    simp only [insert]
    by_cases h1 : k = k₀
    · simp only [h1, ↓reduceIte, ValidBST]
      exact ⟨hl_keys, hr_keys, hl_bst, hr_bst⟩
    · simp only [h1, ↓reduceIte]
      by_cases h2 : k < k₀
      · simp only [h2, ↓reduceIte, ValidBST]
        exact ⟨allKeys_insert (fun x ↦ x < k₀) h2 hl_keys, hr_keys,
          insert_preserves_bst k v hl_bst, hr_bst⟩
      · simp only [h2, ↓reduceIte, ValidBST]
        have hk₀_lt : k₀ < k := by omega
        exact ⟨hl_keys, allKeys_insert (fun x ↦ k₀ < x) hk₀_lt hr_keys,
          hl_bst, insert_preserves_bst k v hr_bst⟩

/-- Correctness of `TreeMap.lookup` after `TreeMap.insert` on any `TreeMap`!
    Notice that because `insert` and `lookup` follow the exact same trichotomy
    (`q = k₀`, `q < k₀`, `k₀ < q`), `lookup q (insert k v t) = insertSpec k v (denote t) q`
    holds unconditionally! -/
theorem lookup_insert (k v q : Nat) :
    ∀ t : TreeMap, lookup q (insert k v t) = insertSpec k v (denote t) q
  | .leaf => by
    simp only [insert, lookup, denote, insertSpec]
    by_cases h : q = k <;> simp [h]
  | .node l k₀ v₀ r => by
    have ihl := lookup_insert k v q l
    have ihr := lookup_insert k v q r
    simp only [denote, insertSpec] at ihl ihr ⊢
    simp only [insert, lookup]
    by_cases h_kk₀ : k = k₀
    · subst h_kk₀
      simp only [↓reduceIte, lookup]
      by_cases h_qk : q = k <;> simp [h_qk]
    · simp only [h_kk₀, ↓reduceIte]
      by_cases h_k_lt : k < k₀
      · simp only [h_k_lt, ↓reduceIte, lookup]
        by_cases h_qk₀ : q = k₀
        · subst h_qk₀
          simp [Ne.symm h_kk₀]
        · simp only [h_qk₀, ↓reduceIte]
          by_cases h_q_lt : q < k₀
          · simp [h_q_lt, ihl]
          · have h_qk : q ≠ k := by omega
            simp [h_q_lt, h_qk]
      · simp only [h_k_lt, ↓reduceIte, lookup]
        by_cases h_qk₀ : q = k₀
        · subst h_qk₀
          simp [Ne.symm h_kk₀]
        · simp only [h_qk₀, ↓reduceIte]
          by_cases h_q_lt : q < k₀
          · have h_qk : q ≠ k := by omega
            simp [h_q_lt, h_qk]
          · simp [h_q_lt, ihr]

theorem denote_insert (k v : Nat) (t : TreeMap) :
    denote (insert k v t) = insertSpec k v (denote t) := by
  funext q
  exact lookup_insert k v q t

/-- If all keys in `t` are strictly less than `k`, and `k ≤ q`, then `lookup q t = none`!
    (This depends on the `AllKeys` / `ValidBST` invariant, illustrating the failure test
    in `docs/proof-ideas.md` §6 if a tree violates the BST invariant!) -/
theorem lookup_eq_none_of_allKeys_lt {q k : Nat} (hle : k ≤ q) :
    ∀ {t : TreeMap}, AllKeys (fun x ↦ x < k) t → lookup q t = none
  | .leaf, _ => rfl
  | .node l k₀ _ r, ⟨hk₀, hl, hr⟩ => by
    have hne : q ≠ k₀ := by omega
    have hnot_lt : ¬ (q < k₀) := by omega
    simp [lookup, hne, hnot_lt, lookup_eq_none_of_allKeys_lt hle hr]

end TreeMap

/-! ### 6.3 Generic Finite-Map Interface, Batch Client, & Representation Transfer Theorem -/

/-- Abstract interface (`FinMapImpl`) packaging a finite-map representation `Carrier`
    with its operations, abstraction map `denote`, cost function `lookupCost`, and
    per-lookup cost bound `costBound : Carrier → Nat`. -/
structure FinMapImpl (Carrier : Type) where
  empty : Carrier
  insert : Nat → Nat → Carrier → Carrier
  lookup : Nat → Carrier → Option Nat
  lookupCost : Nat → Carrier → Nat
  costBound : Carrier → Nat
  denote : Carrier → FinMapSpec
  lookup_eq_denote : ∀ (q : Nat) (m : Carrier), lookup q m = denote m q
  denote_empty : denote empty = emptySpec
  denote_insert : ∀ (k v : Nat) (m : Carrier), denote (insert k v m) = insertSpec k v (denote m)
  lookupCost_le : ∀ (q : Nat) (m : Carrier), lookupCost q m ≤ costBound m

/-- The `ListMap` implementation of `FinMapImpl`, with per-lookup cost bound `m.length + 1`. -/
def listMapImpl : FinMapImpl ListMap where
  empty := ListMap.empty
  insert := ListMap.insert
  lookup := ListMap.lookup
  lookupCost := ListMap.lookupCost
  costBound m := m.length + 1
  denote := ListMap.denote
  lookup_eq_denote _ _ := rfl
  denote_empty := rfl
  denote_insert := ListMap.denote_insert
  lookupCost_le := ListMap.lookupCost_le

/-- The `TreeMap` implementation of `FinMapImpl`, with per-lookup cost bound `t.depth + 1`. -/
def treeMapImpl : FinMapImpl TreeMap where
  empty := .leaf
  insert := TreeMap.insert
  lookup := TreeMap.lookup
  lookupCost := TreeMap.lookupCost
  costBound t := t.depth + 1
  denote := TreeMap.denote
  lookup_eq_denote _ _ := rfl
  denote_empty := rfl
  denote_insert := TreeMap.denote_insert
  lookupCost_le := TreeMap.lookupCost_le_depth

/-- Build a map from a list of `(key, val)` bindings using any `FinMapImpl`. -/
def buildMap {C : Type} (impl : FinMapImpl C) : List (Nat × Nat) → C
  | [] => impl.empty
  | (k, v) :: rest => impl.insert k v (buildMap impl rest)

/-- Abstract specification of `buildMap`: independent of the implementation `impl`! -/
def buildSpec : List (Nat × Nat) → FinMapSpec
  | [] => emptySpec
  | (k, v) :: rest => insertSpec k v (buildSpec rest)

theorem denote_buildMap {C : Type} (impl : FinMapImpl C) :
    ∀ entries : List (Nat × Nat), impl.denote (buildMap impl entries) = buildSpec entries
  | [] => impl.denote_empty
  | (k, v) :: rest => by
    simp [buildMap, buildSpec, impl.denote_insert, denote_buildMap impl rest]

/-- Perform a batch of lookups `queries : List Nat` on a map `m : C`. -/
def batchLookup {C : Type} (impl : FinMapImpl C) (m : C) (queries : List Nat) : List (Option Nat) :=
  queries.map (fun q ↦ impl.lookup q m)

/-- Total lookup cost of `batchLookup` on `queries : List Nat`. -/
def batchLookupCost {C : Type} (impl : FinMapImpl C) (m : C) : List Nat → Nat
  | [] => 0
  | q :: qs => impl.lookupCost q m + batchLookupCost impl m qs

theorem batchLookup_eq_spec {C : Type} (impl : FinMapImpl C)
    (entries : List (Nat × Nat)) (queries : List Nat) :
    batchLookup impl (buildMap impl entries) queries =
      queries.map (fun q ↦ buildSpec entries q) := by
  unfold batchLookup
  congr 1
  funext q
  rw [impl.lookup_eq_denote, denote_buildMap]

theorem batchLookupCost_le {C : Type} (impl : FinMapImpl C) (m : C) :
    ∀ queries : List Nat,
      batchLookupCost impl m queries ≤ queries.length * impl.costBound m
  | [] => by simp [batchLookupCost]
  | q :: qs => by
    simp only [batchLookupCost, List.length_cons]
    have hq := impl.lookupCost_le q m
    have hqs := batchLookupCost_le impl m qs
    have hmul : (qs.length + 1) * impl.costBound m =
        qs.length * impl.costBound m + impl.costBound m :=
      Nat.succ_mul qs.length (impl.costBound m)
    omega

/-- **Finite-Map Client Representation Transfer Theorem (`finMap_client_transfer_theorem`, Gate G5 & `docs/proof-ideas.md` §6)**:
    For any batch of insertions `entries : List (Nat × Nat)` and any batch of lookup queries
    `queries : List Nat`:
    1. **Observational Equivalence of Client Outputs**: Running the batch client on
       `listMapImpl` and on `treeMapImpl` produces the **exact same list of lookup results**
       `queries.map (buildSpec entries)`,
    2. **Implementation-Parametric Cost Certificates**:
       - On `listMapImpl`, the batch lookup cost is bounded by `queries.length * (entries.length + 1)`,
       - On `treeMapImpl`, the batch lookup cost is bounded by `queries.length * ((buildMap treeMapImpl entries).depth + 1)`,
    3. **Distinct Concrete Cost Separation (Failure Test against silent cost preservation)**:
       On a balanced 3-key map (`entries = [(1, 10), (3, 30), (2, 20)]`, where `TreeMap` has
       depth `2` and size `3`, while a 7-node balanced tree has depth `3` vs. list length `7`),
       the concrete lookup costs of `listMapImpl` and `treeMapImpl` **strictly differ**, proving
       that representation transfer preserves the abstract specification while transforming
       the cost certificate! -/
theorem finMap_client_transfer_theorem
    (entries : List (Nat × Nat)) (queries : List Nat) :
    batchLookup listMapImpl (buildMap listMapImpl entries) queries =
      batchLookup treeMapImpl (buildMap treeMapImpl entries) queries ∧
    batchLookup listMapImpl (buildMap listMapImpl entries) queries =
      queries.map (fun q ↦ buildSpec entries q) ∧
    batchLookupCost listMapImpl (buildMap listMapImpl entries) queries ≤
      queries.length * ((buildMap listMapImpl entries).length + 1) ∧
    batchLookupCost treeMapImpl (buildMap treeMapImpl entries) queries ≤
      queries.length * ((buildMap treeMapImpl entries).depth + 1) := by
  rw [batchLookup_eq_spec listMapImpl, batchLookup_eq_spec treeMapImpl]
  exact ⟨rfl, rfl,
    batchLookupCost_le listMapImpl (buildMap listMapImpl entries) queries,
    batchLookupCost_le treeMapImpl (buildMap treeMapImpl entries) queries⟩

/-- **Failure Test 4 (`bst_invariant_violation_and_cost_separation`, `docs/proof-ideas.md` §6)**:
    1. **Invalid BST Failure Test**: An ill-formed `TreeMap` that violates `ValidBST`
       (e.g., placing key `5` in the *left* subtree of root key `2`: `.node (.node .leaf 5 50 .leaf) 2 20 .leaf`)
       fails to find key `5` (`TreeMap.lookup 5 badTree = none`), proving that abstract
       tree theorems cannot assume the BST invariant without proving it!
    2. **Cost Separation Failure Test**: On the balanced 3-node map with keys `1, 3, 2`
       (`entries = [(1, 10), (3, 30), (2, 20)]`), looking up missing key `0` takes `4` steps
       in `listMapImpl` (`ListMap.lookupCost 0 = 4`), whereas in `treeMapImpl` (`root = 2`,
       `left = 1`, `right = 3`, depth `2`) it takes only `3` steps (`TreeMap.lookupCost 0 = 3`),
       so silently keeping the cost expression unchanged across representations is unsound! -/
theorem bst_invariant_violation_and_cost_separation :
    let badTree := TreeMap.node (.node .leaf 5 50 .leaf) 2 20 .leaf
    let entries : List (Nat × Nat) := [(1, 10), (3, 30), (2, 20)]
    (¬ TreeMap.ValidBST badTree) ∧
    TreeMap.lookup 5 badTree = none ∧
    listMapImpl.lookup 0 (buildMap listMapImpl entries) =
      treeMapImpl.lookup 0 (buildMap treeMapImpl entries) ∧
    listMapImpl.lookupCost 0 (buildMap listMapImpl entries) = 4 ∧
    treeMapImpl.lookupCost 0 (buildMap treeMapImpl entries) = 3 ∧
    listMapImpl.lookupCost 0 (buildMap listMapImpl entries) ≠
      treeMapImpl.lookupCost 0 (buildMap treeMapImpl entries) := by
  intro badTree entries
  refine ⟨?_, rfl, rfl, rfl, rfl, by decide⟩
  intro hbst
  have h5_lt_2 : 5 < 2 := hbst.1.1
  omega

end FiniteMapBenchmark

end FeasibleUnivalence.PaperC
