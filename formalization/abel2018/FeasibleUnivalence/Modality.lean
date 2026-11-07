/-
Copyright (c) 2023–2026 Andreas Abel, Nils Anders Danielsson, Oskar Eriksson.
Lean 4 translation and extension prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Sources:
- M2: Graded Modal Dependent Type Theory with a Universe and Erasure, Formalized
  (arXiv:2603.29716v2 / ICFP 2023), Agda tag `jfp-submission-2026-04-30`
  (`75c23df3b1421184cffe35ffd492bb9743dff240`), `Graded/Modality.agda` and
  `Graded/Modality/Properties/Has-well-behaved-zero.agda`.
- M3: On Recursion in Graded Modal Type Theory (ICFP 2026, DOI 10.1145/3828677),
  Agda tag `icfp26` (`93987e3ddc11f583fc3ecdc05472e1dac4094c4f`),
  `Graded/Modality/Properties/Subtraction.agda`, `Graded/Modality/Properties/Natrec.agda`,
  `Graded/Modality/Instances/Erasure/Modality.agda`, `Linearity.agda`, `Affine.agda`,
  `Nat-plus-infinity.agda`, and `Nat.agda`.
-/
import Init

namespace FeasibleUnivalence

/-- M2 Definition 3.1 (`Graded.Modality.Modality`):
    A modality is a semiring `(M, +, ·, 𝟘, 𝟙)` equipped with a meet-semilattice `(M, ∧)`
    such that `+` and `·` distribute over `∧`, together with a grade `ω` satisfying
    `ω ≤ 𝟙` and `ω · (p + q) ≤ ω · q`, and decidable equality with `𝟘`.
    As in the Agda artifact, the partial order `p ≤ q` is defined by `p = p ∧ q`
    (the subsumption order: `p ≤ q` means budget `p` can be subsumed to `q`). -/
structure Modality (M : Type) where
  zero : M
  one : M
  omega : M
  add : M → M → M
  mul : M → M → M
  meet : M → M → M
  decEqZero : (p : M) → Decidable (p = zero)
  -- Semiring laws
  add_assoc : ∀ p q r, add (add p q) r = add p (add q r)
  add_comm : ∀ p q, add p q = add q p
  zero_add : ∀ p, add zero p = p
  add_zero : ∀ p, add p zero = p
  mul_assoc : ∀ p q r, mul (mul p q) r = mul p (mul q r)
  one_mul : ∀ p, mul one p = p
  mul_one : ∀ p, mul p one = p
  zero_mul : ∀ p, mul zero p = zero
  mul_zero : ∀ p, mul p zero = zero
  left_distrib : ∀ p q r, mul p (add q r) = add (mul p q) (mul p r)
  right_distrib : ∀ p q r, mul (add p q) r = add (mul p r) (mul q r)
  -- Meet-semilattice laws
  meet_assoc : ∀ p q r, meet (meet p q) r = meet p (meet q r)
  meet_comm : ∀ p q, meet p q = meet q p
  meet_idem : ∀ p, meet p p = p
  -- Distributivity over meet
  mul_left_distrib_meet : ∀ p q r, mul p (meet q r) = meet (mul p q) (mul p r)
  mul_right_distrib_meet : ∀ p q r, mul (meet p q) r = meet (mul p r) (mul q r)
  add_left_distrib_meet : ∀ p q r, add p (meet q r) = meet (add p q) (add p r)
  add_right_distrib_meet : ∀ p q r, add (meet p q) r = meet (add p r) (add q r)
  -- ω laws (stated in terms of `p = meet p q`)
  omega_le_one : omega = meet omega one
  omega_mul_add_le : ∀ p q,
    mul omega (add p q) = meet (mul omega (add p q)) (mul omega q)

namespace Modality

variable {M : Type} (𝕄 : Modality M)

/-- Subsumption partial order: `p ≤ q` iff `p = p ∧ q`. -/
def le (p q : M) : Prop := p = 𝕄.meet p q

/-- Strict subsumption order: `p < q` iff `p ≤ q` and `p ≠ q`. -/
def lt (p q : M) : Prop := 𝕄.le p q ∧ p ≠ q

/-- A modality is trivial when `𝟙 = 𝟘`. -/
def Trivial : Prop := 𝕄.one = 𝕄.zero

theorem le_refl (p : M) : 𝕄.le p p := (𝕄.meet_idem p).symm

theorem le_antisymm {p q : M} (hpq : 𝕄.le p q) (hqp : 𝕄.le q p) : p = q := by
  calc
    p = 𝕄.meet p q := hpq
    _ = 𝕄.meet q p := 𝕄.meet_comm p q
    _ = q := hqp.symm

theorem le_trans {p q r : M} (hpq : 𝕄.le p q) (hqr : 𝕄.le q r) : 𝕄.le p r := by
  unfold le at *
  calc
    p = 𝕄.meet p q := hpq
    _ = 𝕄.meet p (𝕄.meet q r) := by rw [← hqr]
    _ = 𝕄.meet (𝕄.meet p q) r := (𝕄.meet_assoc p q r).symm
    _ = 𝕄.meet p r := by rw [← hpq]

theorem meet_le_left (p q : M) : 𝕄.le (𝕄.meet p q) p := by
  unfold le
  calc
    𝕄.meet p q = 𝕄.meet q p := 𝕄.meet_comm p q
    _ = 𝕄.meet q (𝕄.meet p p) := by rw [𝕄.meet_idem p]
    _ = 𝕄.meet (𝕄.meet q p) p := (𝕄.meet_assoc q p p).symm
    _ = 𝕄.meet (𝕄.meet p q) p := by rw [𝕄.meet_comm q p]

theorem meet_le_right (p q : M) : 𝕄.le (𝕄.meet p q) q := by
  unfold le
  rw [𝕄.meet_assoc, 𝕄.meet_idem]

theorem le_meet {p q r : M} (hpq : 𝕄.le p q) (hpr : 𝕄.le p r) :
    𝕄.le p (𝕄.meet q r) := by
  unfold le at *
  calc
    p = 𝕄.meet p r := hpr
    _ = 𝕄.meet (𝕄.meet p q) r := by rw [← hpq]
    _ = 𝕄.meet p (𝕄.meet q r) := 𝕄.meet_assoc p q r

theorem add_mono_left {p q : M} (r : M) (hpq : 𝕄.le p q) :
    𝕄.le (𝕄.add p r) (𝕄.add q r) := by
  unfold le at *
  rw [← 𝕄.add_right_distrib_meet, ← hpq]

theorem add_mono_right (p : M) {q r : M} (hqr : 𝕄.le q r) :
    𝕄.le (𝕄.add p q) (𝕄.add p r) := by
  unfold le at *
  rw [← 𝕄.add_left_distrib_meet, ← hqr]

theorem add_mono {p₁ p₂ q₁ q₂ : M} (hp : 𝕄.le p₁ p₂) (hq : 𝕄.le q₁ q₂) :
    𝕄.le (𝕄.add p₁ q₁) (𝕄.add p₂ q₂) :=
  𝕄.le_trans (𝕄.add_mono_left q₁ hp) (𝕄.add_mono_right p₂ hq)

theorem mul_mono_left {p q : M} (r : M) (hpq : 𝕄.le p q) :
    𝕄.le (𝕄.mul p r) (𝕄.mul q r) := by
  unfold le at *
  rw [← 𝕄.mul_right_distrib_meet, ← hpq]

theorem mul_mono_right (p : M) {q r : M} (hqr : 𝕄.le q r) :
    𝕄.le (𝕄.mul p q) (𝕄.mul p r) := by
  unfold le at *
  rw [← 𝕄.mul_left_distrib_meet, ← hqr]

theorem mul_mono {p₁ p₂ q₁ q₂ : M} (hp : 𝕄.le p₁ p₂) (hq : 𝕄.le q₁ q₂) :
    𝕄.le (𝕄.mul p₁ q₁) (𝕄.mul p₂ q₂) :=
  𝕄.le_trans (𝕄.mul_mono_left q₁ hp) (𝕄.mul_mono_right p₂ hq)

theorem meet_mono {p₁ p₂ q₁ q₂ : M} (hp : 𝕄.le p₁ p₂) (hq : 𝕄.le q₁ q₂) :
    𝕄.le (𝕄.meet p₁ q₁) (𝕄.meet p₂ q₂) :=
  𝕄.le_meet
    (𝕄.le_trans (𝕄.meet_le_left p₁ q₁) hp)
    (𝕄.le_trans (𝕄.meet_le_right p₁ q₁) hq)

/-- M2 Definition 6.1 (`Graded.Modality.Has-well-behaved-zero`):
    The zero grade `𝟘` is well-behaved if the modality is non-trivial (`𝟙 ≠ 𝟘`),
    has no zero divisors (`p · q = 𝟘 → p = 𝟘 ∨ q = 𝟘`), and `+` and `∧` are positive
    (`p + q = 𝟘 → p = 𝟘` and `p ∧ q = 𝟘 → p = 𝟘`). -/
structure HasWellBehavedZero : Prop where
  nonTrivial : 𝕄.one ≠ 𝕄.zero
  zero_product : ∀ {p q}, 𝕄.mul p q = 𝕄.zero → p = 𝕄.zero ∨ q = 𝕄.zero
  add_positive_left : ∀ {p q}, 𝕄.add p q = 𝕄.zero → p = 𝕄.zero
  meet_positive_left : ∀ {p q}, 𝕄.meet p q = 𝕄.zero → p = 𝕄.zero

theorem HasWellBehavedZero.add_positive_right {𝕄 : Modality M}
    (hw : 𝕄.HasWellBehavedZero) {p q : M} (h : 𝕄.add p q = 𝕄.zero) :
    q = 𝕄.zero :=
  hw.add_positive_left (by rw [𝕄.add_comm]; exact h)

theorem HasWellBehavedZero.add_positive {𝕄 : Modality M}
    (hw : 𝕄.HasWellBehavedZero) {p q : M} (h : 𝕄.add p q = 𝕄.zero) :
    p = 𝕄.zero ∧ q = 𝕄.zero :=
  ⟨hw.add_positive_left h, hw.add_positive_right h⟩

theorem HasWellBehavedZero.meet_positive_right {𝕄 : Modality M}
    (hw : 𝕄.HasWellBehavedZero) {p q : M} (h : 𝕄.meet p q = 𝕄.zero) :
    q = 𝕄.zero :=
  hw.meet_positive_left (by rw [𝕄.meet_comm]; exact h)

/-- Agda `𝟘≮`: if `𝟘 ≤ p`, then `p = 𝟘`. -/
theorem HasWellBehavedZero.zero_le_eq_zero {𝕄 : Modality M}
    (hw : 𝕄.HasWellBehavedZero) {p : M} (h : 𝕄.le 𝕄.zero p) :
    p = 𝕄.zero := by
  have hm : 𝕄.meet p 𝕄.zero = 𝕄.zero := by
    rw [𝕄.meet_comm]
    exact h.symm
  exact hw.meet_positive_left hm

/-- Agda `𝟘≰𝟙`: `¬ (𝟘 ≤ 𝟙)`. -/
theorem HasWellBehavedZero.zero_not_le_one {𝕄 : Modality M}
    (hw : 𝕄.HasWellBehavedZero) : ¬ 𝕄.le 𝕄.zero 𝕄.one :=
  fun h ↦ hw.nonTrivial (hw.zero_le_eq_zero h)

/-- Agda `ω≢𝟘`: `ω ≠ 𝟘`. -/
theorem HasWellBehavedZero.omega_ne_zero {𝕄 : Modality M}
    (hw : 𝕄.HasWellBehavedZero) : 𝕄.omega ≠ 𝕄.zero := by
  intro hω
  have h1 : 𝕄.le 𝕄.zero 𝕄.one := by
    unfold le
    rw [← hω]
    exact 𝕄.omega_le_one
  exact hw.zero_not_le_one h1

/-! ## Greatest Lower Bounds and `nrᵢ` Sequences (M3 Section 5) -/

/-- `LeastSuchThat P p`: `p` satisfies `P` and `p ≤ q` for every `q` satisfying `P`. -/
def LeastSuchThat (P : M → Prop) (p : M) : Prop :=
  P p ∧ ∀ q, P q → 𝕄.le p q

/-- `GreatestSuchThat P p`: `p` satisfies `P` and `q ≤ p` for every `q` satisfying `P`. -/
def GreatestSuchThat (P : M → Prop) (p : M) : Prop :=
  P p ∧ ∀ q, P q → 𝕄.le q p

/-- `GreatestLowerBound p seq`: `p` is the greatest lower bound of `seq : Nat → M`. -/
def GreatestLowerBound (p : M) (seq : Nat → M) : Prop :=
  𝕄.GreatestSuchThat (fun r ↦ ∀ i, 𝕄.le r (seq i)) p

/-- M3 `nrᵢ r z s`: unfolding sequence for `natrec` usage. -/
def nrᵢ (r z s : M) : Nat → M
  | 0 => z
  | i + 1 => 𝕄.add s (𝕄.mul r (nrᵢ r z s i))

theorem GLB_unique {p q : M} {seq : Nat → M}
    (hp : 𝕄.GreatestLowerBound p seq) (hq : 𝕄.GreatestLowerBound q seq) :
    p = q :=
  𝕄.le_antisymm (hq.2 p hp.1) (hp.2 q hq.1)

theorem GLB_const (p : M) {seq : Nat → M} (h : ∀ i, seq i = p) :
    𝕄.GreatestLowerBound p seq := by
  refine ⟨fun i ↦ ?_, fun q hq ↦ ?_⟩
  · rw [h i]; exact 𝕄.le_refl p
  · have h0 := hq 0
    rw [h 0] at h0
    exact h0

theorem nrᵢ_zero (r : M) : ∀ i, 𝕄.nrᵢ r 𝕄.zero 𝕄.zero i = 𝕄.zero
  | 0 => rfl
  | i + 1 => by
      simp only [nrᵢ, nrᵢ_zero r i, 𝕄.mul_zero, 𝕄.add_zero]

theorem GLB_nrᵢ_zero (r : M) :
    𝕄.GreatestLowerBound 𝕄.zero (𝕄.nrᵢ r 𝕄.zero 𝕄.zero) :=
  𝕄.GLB_const 𝕄.zero (𝕄.nrᵢ_zero r)

theorem nrᵢ_mono (r : M) {z z' s s' : M} (hz : 𝕄.le z z') (hs : 𝕄.le s s') :
    ∀ i, 𝕄.le (𝕄.nrᵢ r z s i) (𝕄.nrᵢ r z' s' i)
  | 0 => hz
  | i + 1 => 𝕄.add_mono hs (𝕄.mul_mono_right r (nrᵢ_mono r hz hs i))

theorem nrᵢ_zero_GLB (p q : M) :
    𝕄.GreatestLowerBound (𝕄.meet p q) (𝕄.nrᵢ 𝕄.zero p q) := by
  refine ⟨?_, ?_⟩
  · intro i
    cases i with
    | zero => exact 𝕄.meet_le_left p q
    | succ i =>
        simp only [nrᵢ, 𝕄.zero_mul, 𝕄.add_zero]
        exact 𝕄.meet_le_right p q
  · intro r hr
    have h0 : 𝕄.le r p := hr 0
    have h1 : 𝕄.le r q := by
      have h1' := hr 1
      simp only [nrᵢ, 𝕄.zero_mul, 𝕄.add_zero] at h1'
      exact h1'
    exact 𝕄.le_meet h0 h1

theorem nrᵢ_const_one (z : M) : ∀ i, 𝕄.nrᵢ 𝕄.one z 𝕄.zero i = z
  | 0 => rfl
  | i + 1 => by
      simp only [nrᵢ, 𝕄.zero_add, 𝕄.one_mul, nrᵢ_const_one z i]

theorem nrᵢ_const_GLB_one (z : M) :
    𝕄.GreatestLowerBound z (𝕄.nrᵢ 𝕄.one z 𝕄.zero) :=
  𝕄.GLB_const z (𝕄.nrᵢ_const_one z)

theorem nrᵢ_const_step_zero (z : M) : ∀ i, 𝕄.nrᵢ 𝕄.zero z z i = z
  | 0 => rfl
  | _ + 1 => by
      simp only [nrᵢ, 𝕄.zero_mul, 𝕄.add_zero]

theorem nrᵢ_const_GLB_step_zero (z : M) :
    𝕄.GreatestLowerBound z (𝕄.nrᵢ 𝕄.zero z z) :=
  𝕄.GLB_const z (𝕄.nrᵢ_const_step_zero z)

/-- M3 Section 5.2 (`Graded.Modality.Properties.Natrec.≤-nrᵢ-GLB`):
    The greatest lower bound of `nrᵢ r z s` is the greatest solution `x` to the
    characteristic inequalities `x ≤ z` and `x ≤ s + r · x`. -/
theorem le_nrᵢ_GLB {x y r z s : M}
    (hle₀ : 𝕄.le x z) (hle_step : 𝕄.le x (𝕄.add s (𝕄.mul r x)))
    (hglb : 𝕄.GreatestLowerBound y (𝕄.nrᵢ r z s)) :
    𝕄.le x y := by
  have hbound : ∀ i, 𝕄.le x (𝕄.nrᵢ r z s i) := by
    intro i
    induction i with
    | zero => exact hle₀
    | succ i ih =>
        exact 𝕄.le_trans hle_step (𝕄.add_mono_right s (𝕄.mul_mono_right r ih))
  exact hglb.2 x hbound

theorem nrᵢ_GLB_le₀ {p r z s : M} (hglb : 𝕄.GreatestLowerBound p (𝕄.nrᵢ r z s)) :
    𝕄.le p z :=
  hglb.1 0

/-- M3 Definition 5.1 (`Graded.Modality.Has-well-behaved-GLBs`):
    Greatest lower bounds distribute over addition and multiplication and compose
    across `nrᵢ` sequences. -/
structure HasWellBehavedGLBs : Prop where
  add_GLB_left : ∀ {p q : M} {seq : Nat → M},
    𝕄.GreatestLowerBound p seq →
    𝕄.GreatestLowerBound (𝕄.add q p) (fun i ↦ 𝕄.add q (seq i))
  mul_GLB_left : ∀ {p q : M} {seq : Nat → M},
    𝕄.GreatestLowerBound p seq →
    𝕄.GreatestLowerBound (𝕄.mul q p) (fun i ↦ 𝕄.mul q (seq i))
  mul_GLB_right : ∀ {p q : M} {seq : Nat → M},
    𝕄.GreatestLowerBound p seq →
    𝕄.GreatestLowerBound (𝕄.mul p q) (fun i ↦ 𝕄.mul (seq i) q)
  add_nrᵢ_GLB : ∀ {p q r z₁ s₁ z₂ s₂ : M},
    𝕄.GreatestLowerBound p (𝕄.nrᵢ r z₁ s₁) →
    𝕄.GreatestLowerBound q (𝕄.nrᵢ r z₂ s₂) →
    ∃ r', 𝕄.GreatestLowerBound r' (𝕄.nrᵢ r (𝕄.add z₁ z₂) (𝕄.add s₁ s₂)) ∧
      𝕄.le (𝕄.add p q) r'

/-- Under `HasWellBehavedGLBs`, if `p` is the GLB of `nrᵢ r z s`, then `p ≤ s + r · p`. -/
theorem nrᵢ_GLB_le_step {𝕄 : Modality M} (hwb : 𝕄.HasWellBehavedGLBs) {p r z s : M}
    (hglb : 𝕄.GreatestLowerBound p (𝕄.nrᵢ r z s)) :
    𝕄.le p (𝕄.add s (𝕄.mul r p)) := by
  have hmul := hwb.mul_GLB_left (q := r) hglb
  have hadd := hwb.add_GLB_left (q := s) hmul
  exact hadd.2 p (fun i ↦ hglb.1 (i + 1))

/-! ## Grade Subtraction (M3 Section 4.1, `Graded.Modality.Properties.Subtraction`) -/

/-- `SubLe 𝕄 p q r` (`p - q ≤ r`): `p ≤ r + q`.
    In quantitative modalities, if `p` copies are available, `q` copies can be consumed
    leaving at least `r` copies. -/
def SubLe (p q r : M) : Prop := 𝕄.le p (𝕄.add r q)

/-- `SubEq 𝕄 p q r` (`p - q ≡ r`): `r` is the least grade (most permissive remaining budget)
    such that `p - q ≤ r`. -/
def SubEq (p q r : M) : Prop := 𝕄.LeastSuchThat (𝕄.SubLe p q) r

/-- M3 Section 4.1 (`Supports-subtraction`): whenever `p - q ≤ r` has a witness,
    there is a canonical least witness `r'` with `p - q ≡ r'`. -/
def SupportsSubtraction : Prop :=
  ∀ {p q r : M}, 𝕄.SubLe p q r → ∃ r', 𝕄.SubEq p q r'

theorem subEq_unique {p q r r' : M} (h1 : 𝕄.SubEq p q r) (h2 : 𝕄.SubEq p q r') :
    r = r' :=
  𝕄.le_antisymm (h1.2 r' h2.1) (h2.2 r h1.1)

theorem subEq_mono_left {p p' q r r' : M}
    (hpp' : 𝕄.le p p') (h1 : 𝕄.SubEq p q r) (h2 : 𝕄.SubEq p' q r') :
    𝕄.le r r' :=
  h1.2 r' (𝕄.le_trans hpp' h2.1)

theorem subEq_antitone_right {p q q' r r' : M}
    (hqq' : 𝕄.le q q') (h1 : 𝕄.SubEq p q r) (h2 : 𝕄.SubEq p q' r') :
    𝕄.le r' r :=
  h2.2 r (𝕄.le_trans h1.1 (𝕄.add_mono_right r hqq'))

theorem sub_zero_le (p : M) : 𝕄.SubLe p 𝕄.zero p := by
  unfold SubLe
  rw [𝕄.add_zero]
  exact 𝕄.le_refl p

theorem sub_zero_eq (p : M) : 𝕄.SubEq p 𝕄.zero p := by
  refine ⟨𝕄.sub_zero_le p, fun q hq ↦ ?_⟩
  unfold SubLe at hq
  rw [𝕄.add_zero] at hq
  exact hq

theorem sub_self_le_zero (p : M) : 𝕄.SubLe p p 𝕄.zero := by
  unfold SubLe
  rw [𝕄.zero_add]
  exact 𝕄.le_refl p

theorem HasWellBehavedZero.zero_sub_le {𝕄 : Modality M}
    (hw : 𝕄.HasWellBehavedZero) {p q : M} (h : 𝕄.SubLe 𝕄.zero p q) :
    q = 𝕄.zero ∧ p = 𝕄.zero :=
  hw.add_positive (hw.zero_le_eq_zero h)

theorem HasWellBehavedZero.zero_sub_eq {𝕄 : Modality M}
    (hw : 𝕄.HasWellBehavedZero) {p q : M} (h : 𝕄.SubEq 𝕄.zero p q) :
    q = 𝕄.zero ∧ p = 𝕄.zero :=
  hw.zero_sub_le h.1

theorem HasWellBehavedZero.zero_sub_not_le {𝕄 : Modality M}
    (hw : 𝕄.HasWellBehavedZero) {p q : M} (hp : p ≠ 𝕄.zero) :
    ¬ 𝕄.SubLe 𝕄.zero p q :=
  fun h ↦ hp (hw.zero_sub_le h).2

/-- M3 `Addition≡Meet`: any modality where `+` and `∧` coincide supports subtraction,
    with `p - q ≡ p` whenever `p ≤ q`. -/
theorem addEqMeet_subEq (hAddMeet : ∀ x y : M, 𝕄.add x y = 𝕄.meet x y)
    {p q : M} (hpq : 𝕄.le p q) : 𝕄.SubEq p q p := by
  refine ⟨?_, ?_⟩
  · unfold SubLe
    have h1 : 𝕄.le p (𝕄.add p p) := by
      unfold le
      rw [hAddMeet p p, 𝕄.meet_idem, 𝕄.meet_idem]
    exact 𝕄.le_trans h1 (𝕄.add_mono_right p hpq)
  · intro r hr
    unfold SubLe at hr
    rw [hAddMeet r q] at hr
    exact 𝕄.le_trans hr (𝕄.meet_le_left r q)

theorem addEqMeet_supports_subtraction
    (hAddMeet : ∀ x y : M, 𝕄.add x y = 𝕄.meet x y) :
    𝕄.SupportsSubtraction := by
  intro p q r hr
  have hpq : 𝕄.le p q := by
    unfold SubLe at hr
    rw [hAddMeet r q] at hr
    exact 𝕄.le_trans hr (𝕄.meet_le_right r q)
  exact ⟨p, 𝕄.addEqMeet_subEq hAddMeet hpq⟩

end Modality

/-! ## Concrete Modality Instances (M2 & M3) -/

/-- 1. The two-element Erasure modality (`𝟘`, `ω` where `𝟙 = ω`). -/
inductive ErasureGrade where
  | zero : ErasureGrade
  | omega : ErasureGrade
  deriving DecidableEq, Repr

namespace ErasureGrade

def add : ErasureGrade → ErasureGrade → ErasureGrade
  | .zero, .zero => .zero
  | _, _ => .omega

def mul : ErasureGrade → ErasureGrade → ErasureGrade
  | .omega, .omega => .omega
  | _, _ => .zero

def erasureModality : Modality ErasureGrade where
  zero := .zero
  one := .omega
  omega := .omega
  add := add
  mul := mul
  meet := add
  decEqZero p := decEq p .zero
  add_assoc p q r := by cases p <;> cases q <;> cases r <;> rfl
  add_comm p q := by cases p <;> cases q <;> rfl
  zero_add p := by cases p <;> rfl
  add_zero p := by cases p <;> rfl
  mul_assoc p q r := by cases p <;> cases q <;> cases r <;> rfl
  one_mul p := by cases p <;> rfl
  mul_one p := by cases p <;> rfl
  zero_mul p := by cases p <;> rfl
  mul_zero p := by cases p <;> rfl
  left_distrib p q r := by cases p <;> cases q <;> cases r <;> rfl
  right_distrib p q r := by cases p <;> cases q <;> cases r <;> rfl
  meet_assoc p q r := by cases p <;> cases q <;> cases r <;> rfl
  meet_comm p q := by cases p <;> cases q <;> rfl
  meet_idem p := by cases p <;> rfl
  mul_left_distrib_meet p q r := by cases p <;> cases q <;> cases r <;> rfl
  mul_right_distrib_meet p q r := by cases p <;> cases q <;> cases r <;> rfl
  add_left_distrib_meet p q r := by cases p <;> cases q <;> cases r <;> rfl
  add_right_distrib_meet p q r := by cases p <;> cases q <;> cases r <;> rfl
  omega_le_one := rfl
  omega_mul_add_le p q := by cases p <;> cases q <;> rfl

theorem erasureHasWellBehavedZero : erasureModality.HasWellBehavedZero where
  nonTrivial := by decide
  zero_product {p q} h := by
    cases p <;> cases q
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · contradiction
  add_positive_left {p q} h := by
    cases p <;> cases q <;> first | rfl | contradiction
  meet_positive_left {p q} h := by
    cases p <;> cases q <;> first | rfl | contradiction

theorem erasureSupportsSubtraction : erasureModality.SupportsSubtraction :=
  erasureModality.addEqMeet_supports_subtraction (fun _ _ ↦ rfl)

end ErasureGrade

/-- 2. The three-element `ZeroOneMany` grades (`𝟘`, `𝟙`, `ω`), supporting both:
    - `Linearity` (`ω ≤ 𝟙`, `ω ≤ 𝟘`, and `𝟙 ∧ 𝟘 = ω`)
    - `Affine` (`ω ≤ 𝟙 ≤ 𝟘`, so `𝟙 ∧ 𝟘 = 𝟙`) -/
inductive ZeroOneMany where
  | zero : ZeroOneMany
  | one : ZeroOneMany
  | omega : ZeroOneMany
  deriving DecidableEq, Repr

namespace ZeroOneMany

def add : ZeroOneMany → ZeroOneMany → ZeroOneMany
  | .zero, q => q
  | p, .zero => p
  | _, _ => .omega

def mul : ZeroOneMany → ZeroOneMany → ZeroOneMany
  | .zero, _ => .zero
  | _, .zero => .zero
  | .one, q => q
  | p, .one => p
  | .omega, .omega => .omega

/-- Meet for Linearity (`ω` is bottom; `𝟘` and `𝟙` are incomparable). -/
def meetLin : ZeroOneMany → ZeroOneMany → ZeroOneMany
  | .zero, .zero => .zero
  | .one, .one => .one
  | _, _ => .omega

/-- Meet for Affine (`ω ≤ 𝟙 ≤ 𝟘`). -/
def meetAff : ZeroOneMany → ZeroOneMany → ZeroOneMany
  | .zero, q => q
  | p, .zero => p
  | .one, .one => .one
  | _, _ => .omega

def linearityModality : Modality ZeroOneMany where
  zero := .zero
  one := .one
  omega := .omega
  add := add
  mul := mul
  meet := meetLin
  decEqZero p := decEq p .zero
  add_assoc p q r := by cases p <;> cases q <;> cases r <;> rfl
  add_comm p q := by cases p <;> cases q <;> rfl
  zero_add p := by cases p <;> rfl
  add_zero p := by cases p <;> rfl
  mul_assoc p q r := by cases p <;> cases q <;> cases r <;> rfl
  one_mul p := by cases p <;> rfl
  mul_one p := by cases p <;> rfl
  zero_mul p := by cases p <;> rfl
  mul_zero p := by cases p <;> rfl
  left_distrib p q r := by cases p <;> cases q <;> cases r <;> rfl
  right_distrib p q r := by cases p <;> cases q <;> cases r <;> rfl
  meet_assoc p q r := by cases p <;> cases q <;> cases r <;> rfl
  meet_comm p q := by cases p <;> cases q <;> rfl
  meet_idem p := by cases p <;> rfl
  mul_left_distrib_meet p q r := by cases p <;> cases q <;> cases r <;> rfl
  mul_right_distrib_meet p q r := by cases p <;> cases q <;> cases r <;> rfl
  add_left_distrib_meet p q r := by cases p <;> cases q <;> cases r <;> rfl
  add_right_distrib_meet p q r := by cases p <;> cases q <;> cases r <;> rfl
  omega_le_one := rfl
  omega_mul_add_le p q := by cases p <;> cases q <;> rfl

def affineModality : Modality ZeroOneMany where
  zero := .zero
  one := .one
  omega := .omega
  add := add
  mul := mul
  meet := meetAff
  decEqZero p := decEq p .zero
  add_assoc p q r := by cases p <;> cases q <;> cases r <;> rfl
  add_comm p q := by cases p <;> cases q <;> rfl
  zero_add p := by cases p <;> rfl
  add_zero p := by cases p <;> rfl
  mul_assoc p q r := by cases p <;> cases q <;> cases r <;> rfl
  one_mul p := by cases p <;> rfl
  mul_one p := by cases p <;> rfl
  zero_mul p := by cases p <;> rfl
  mul_zero p := by cases p <;> rfl
  left_distrib p q r := by cases p <;> cases q <;> cases r <;> rfl
  right_distrib p q r := by cases p <;> cases q <;> cases r <;> rfl
  meet_assoc p q r := by cases p <;> cases q <;> cases r <;> rfl
  meet_comm p q := by cases p <;> cases q <;> rfl
  meet_idem p := by cases p <;> rfl
  mul_left_distrib_meet p q r := by cases p <;> cases q <;> cases r <;> rfl
  mul_right_distrib_meet p q r := by cases p <;> cases q <;> cases r <;> rfl
  add_left_distrib_meet p q r := by cases p <;> cases q <;> cases r <;> rfl
  add_right_distrib_meet p q r := by cases p <;> cases q <;> cases r <;> rfl
  omega_le_one := rfl
  omega_mul_add_le p q := by cases p <;> cases q <;> rfl

theorem linearityHasWellBehavedZero : linearityModality.HasWellBehavedZero where
  nonTrivial := by decide
  zero_product {p q} h := by
    cases p <;> cases q <;> first | exact Or.inl rfl | exact Or.inr rfl | contradiction
  add_positive_left {p q} h := by
    cases p <;> cases q <;> first | rfl | contradiction
  meet_positive_left {p q} h := by
    cases p <;> cases q <;> first | rfl | contradiction

theorem affineHasWellBehavedZero : affineModality.HasWellBehavedZero where
  nonTrivial := by decide
  zero_product {p q} h := by
    cases p <;> cases q <;> first | exact Or.inl rfl | exact Or.inr rfl | contradiction
  add_positive_left {p q} h := by
    cases p <;> cases q <;> first | rfl | contradiction
  meet_positive_left {p q} h := by
    cases p <;> cases q <;> first | rfl | contradiction

/-- Explicit subtraction function for `ZeroOneMany` (for both Linearity and Affine):
    - `p - 𝟘 = p`
    - `𝟙 - 𝟙 = 𝟘`
    - `ω - q = ω` -/
def subCandidate : ZeroOneMany → ZeroOneMany → ZeroOneMany
  | p, .zero => p
  | .one, .one => .zero
  | .omega, _ => .omega
  | _, _ => .omega

theorem linearitySupportsSubtraction : linearityModality.SupportsSubtraction := by
  intro p q r h
  refine ⟨subCandidate p q, ?_, ?_⟩
  · cases p <;> cases q <;> cases r <;> first | rfl | contradiction
  · intro r' hr'
    cases p <;> cases q <;> cases r <;> cases r' <;>
      first | rfl | contradiction

theorem affineSupportsSubtraction : affineModality.SupportsSubtraction := by
  intro p q r h
  refine ⟨subCandidate p q, ?_, ?_⟩
  · cases p <;> cases q <;> cases r <;> first | rfl | contradiction
  · intro r' hr'
    cases p <;> cases q <;> cases r <;> cases r' <;>
      first | rfl | contradiction

/-- M3 Section 5.4 (`Graded.Modality.Instances.Linearity.nrᵢ-r𝟙p-GLB-𝟙-inv`):
    In `linearityModality`, `𝟙` is the GLB of `nrᵢ r 𝟙 p` iff
    `(p = 𝟘 ∧ r = 𝟙) ∨ (p = 𝟙 ∧ r = 𝟘)`. -/
theorem linearity_nrᵢ_GLB_one_iff (p r : ZeroOneMany) :
    linearityModality.GreatestLowerBound .one (linearityModality.nrᵢ r .one p) ↔
      ((p = .zero ∧ r = .one) ∨ (p = .one ∧ r = .zero)) := by
  constructor
  · intro ⟨hle, hgreat⟩
    have h1 : linearityModality.le .one (linearityModality.nrᵢ r .one p 1) := hle 1
    have h2 : linearityModality.le .one (linearityModality.nrᵢ r .one p 2) := hle 2
    have hnotω : (∀ i, linearityModality.nrᵢ r .one p i = .one) := by
      intro i
      cases i with
      | zero => rfl
      | succ i =>
        have hi := hle (i + 1)
        cases hval : linearityModality.nrᵢ r .one p (i + 1) <;>
          rw [hval] at hi <;> first | rfl | contradiction
    have hstep1 := hnotω 1
    have hstep2 := hnotω 2
    cases p <;> cases r
    · contradiction
    · exact Or.inl ⟨rfl, rfl⟩
    · contradiction
    · exact Or.inr ⟨rfl, rfl⟩
    · contradiction
    · contradiction
    · contradiction
    · contradiction
    · contradiction
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact linearityModality.nrᵢ_const_GLB_one .one
    · exact linearityModality.nrᵢ_const_GLB_step_zero .one

/-- M3 Section 5.4 (`Graded.Modality.Instances.Affine.nrᵢ-r𝟙p-GLB-𝟙-inv`):
    In `affineModality`, `𝟙` is the GLB of `nrᵢ r 𝟙 p` iff
    `(p = 𝟘 ∧ r = 𝟙) ∨ (p = 𝟙 ∧ r = 𝟘) ∨ (p = 𝟘 ∧ r = 𝟘)`. -/
theorem affine_nrᵢ_GLB_one_iff (p r : ZeroOneMany) :
    affineModality.GreatestLowerBound .one (affineModality.nrᵢ r .one p) ↔
      ((p = .zero ∧ r = .one) ∨ (p = .one ∧ r = .zero) ∨ (p = .zero ∧ r = .zero)) := by
  constructor
  · intro ⟨hle, _⟩
    have hnotω : ∀ i, affineModality.nrᵢ r .one p i ≠ .omega := by
      intro i hω
      have hi := hle i
      rw [hω] at hi
      contradiction
    have h1 := hnotω 1
    have h2 := hnotω 2
    cases p <;> cases r
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exfalso; exact h1 rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exfalso; exact h1 rfl
    · exfalso; exact h1 rfl
    · exfalso; exact h1 rfl
    · exfalso; exact h1 rfl
    · exfalso; exact h1 rfl
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact affineModality.nrᵢ_const_GLB_one .one
    · exact affineModality.nrᵢ_const_GLB_step_zero .one
    · exact affineModality.nrᵢ_zero_GLB .one .zero

end ZeroOneMany

/-! ## 3. The `Nat` Modality without `∞` (`Graded.Modality.Instances.Nat`) -/

namespace NatModality

/-- Max operation on `Nat` defined via `if ... then ... else ...` so `omega` unfolds it directly. -/
def natMax (p q : Nat) : Nat := if p ≤ q then q else p

theorem natMax_assoc (p q r : Nat) : natMax (natMax p q) r = natMax p (natMax q r) := by
  by_cases hpq : p ≤ q <;> by_cases hqr : q ≤ r <;> by_cases hpr : p ≤ r <;>
    simp [natMax, hpq, hqr, hpr] <;> omega

theorem natMax_comm (p q : Nat) : natMax p q = natMax q p := by
  by_cases hpq : p ≤ q <;> by_cases hqp : q ≤ p <;>
    simp [natMax, hpq, hqp] <;> omega

theorem natMax_idem (p : Nat) : natMax p p = p := by
  simp [natMax]

theorem mul_left_distrib_natMax (p q r : Nat) :
    p * natMax q r = natMax (p * q) (p * r) := by
  unfold natMax
  by_cases hqr : q ≤ r
  · have hpqr : p * q ≤ p * r := Nat.mul_le_mul_left p hqr
    simp [hqr, hpqr]
  · have hrq : r ≤ q := by omega
    have hprq : p * r ≤ p * q := Nat.mul_le_mul_left p hrq
    simp [hqr]
    intro hpqr
    exact Nat.le_antisymm hpqr hprq

theorem mul_right_distrib_natMax (p q r : Nat) :
    natMax p q * r = natMax (p * r) (q * r) := by
  rw [Nat.mul_comm, Nat.mul_comm p r, Nat.mul_comm q r]
  exact mul_left_distrib_natMax r p q

theorem add_left_distrib_natMax (p q r : Nat) :
    p + natMax q r = natMax (p + q) (p + r) := by
  by_cases hqr : q ≤ r <;> by_cases hpqr : p + q ≤ p + r <;>
    simp [natMax, hqr, hpqr] <;> omega

theorem add_right_distrib_natMax (p q r : Nat) :
    natMax p q + r = natMax (p + r) (q + r) := by
  by_cases hpq : p ≤ q <;> by_cases hpqr : p + r ≤ q + r <;>
    simp [natMax, hpq, hpqr] <;> omega

def natModality : Modality Nat where
  zero := 0
  one := 1
  omega := 1
  add := (· + ·)
  mul := (· * ·)
  meet := natMax
  decEqZero p := decEq p 0
  add_assoc := Nat.add_assoc
  add_comm := Nat.add_comm
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  mul_assoc := Nat.mul_assoc
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  left_distrib := Nat.mul_add
  right_distrib := Nat.add_mul
  meet_assoc := natMax_assoc
  meet_comm := natMax_comm
  meet_idem := natMax_idem
  mul_left_distrib_meet := mul_left_distrib_natMax
  mul_right_distrib_meet := mul_right_distrib_natMax
  add_left_distrib_meet := add_left_distrib_natMax
  add_right_distrib_meet := add_right_distrib_natMax
  omega_le_one := rfl
  omega_mul_add_le p q := by
    simp only [Nat.one_mul, natMax]
    split <;> omega

/-- In `natModality`, `le p q` (`p = natMax p q`) is equivalent to `q ≤ p` in `Nat`. -/
theorem le_iff_ge (p q : Nat) : natModality.le p q ↔ q ≤ p := by
  change p = natMax p q ↔ q ≤ p
  unfold natMax
  -- Case split on the decidable `Nat` order (a bare `split` here pulled in `Classical.choice`).
  -- `omega` on an `↔` goal also pulled in `Classical.choice`, so both directions are explicit.
  by_cases h : p ≤ q
  · rw [if_pos h]
    exact ⟨fun e => e ▸ Nat.le_refl p, fun hqp => Nat.le_antisymm h hqp⟩
  · rw [if_neg h]
    exact ⟨fun _ => Nat.le_of_lt (Nat.gt_of_not_le h), fun _ => rfl⟩

theorem natHasWellBehavedZero : natModality.HasWellBehavedZero where
  nonTrivial := by decide
  zero_product {p q} h := by
    cases p with
    | zero => exact Or.inl rfl
    | succ p =>
      cases q with
      | zero => exact Or.inr rfl
      | succ q =>
        change (p + 1) * (q + 1) = 0 at h
        have : (p + 1) * (q + 1) > 0 := Nat.mul_pos (Nat.succ_pos p) (Nat.succ_pos q)
        omega
  add_positive_left {p q} h := by
    change p + q = 0 at h
    change p = 0
    omega
  meet_positive_left {p q} h := by
    change natMax p q = 0 at h
    unfold natMax at h
    change p = 0
    split at h <;> omega

theorem natSupportsSubtraction : natModality.SupportsSubtraction := by
  intro p q r h
  have hge : r + q ≤ p := (le_iff_ge p (r + q)).mp h
  refine ⟨p - q, ?_, ?_⟩
  · rw [Modality.SubLe, le_iff_ge]
    change (p - q) + q ≤ p
    omega
  · intro r' hr'
    rw [Modality.SubLe, le_iff_ge] at hr'
    change r' + q ≤ p at hr'
    rw [le_iff_ge]
    omega

theorem nrᵢ_one_one_one (i : Nat) : natModality.nrᵢ 1 1 1 i = i + 1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change 1 + 1 * natModality.nrᵢ 1 1 1 i = i + 1 + 1
    rw [ih]
    omega

/-- M3 Section 5.6 (`Graded.Modality.Instances.Nat.¬nrᵢ-GLB`):
    In `Nat` without `∞`, the sequence `nrᵢ 1 1 1` (`i ↦ i + 1`) has no greatest lower bound
    (in the modality order `p ≤ q ↔ q ≤_Nat p`). -/
theorem nat_no_nrᵢ_GLB :
    ¬ ∃ p, natModality.GreatestLowerBound p (natModality.nrᵢ 1 1 1) := by
  rintro ⟨p, hle, _⟩
  have hp := hle p
  rw [nrᵢ_one_one_one p, le_iff_ge] at hp
  omega

end NatModality

/-! ## 4. `NatPlusInfinity` (`ℕ ⊎ {∞}`, M3 `Graded.Modality.Instances.Nat-plus-infinity`) -/

inductive NatPlusInfinity where
  | fin : Nat → NatPlusInfinity
  | inf : NatPlusInfinity
  deriving DecidableEq, Repr

namespace NatPlusInfinity

def add : NatPlusInfinity → NatPlusInfinity → NatPlusInfinity
  | .fin m, .fin n => .fin (m + n)
  | _, _ => .inf

def mul : NatPlusInfinity → NatPlusInfinity → NatPlusInfinity
  | .fin 0, _ => .fin 0
  | _, .fin 0 => .fin 0
  | .fin m, .fin n => .fin (m * n)
  | _, _ => .inf

def meet : NatPlusInfinity → NatPlusInfinity → NatPlusInfinity
  | .fin m, .fin n => .fin (NatModality.natMax m n)
  | _, _ => .inf

@[simp] theorem mul_fin_zero_left (q : NatPlusInfinity) : mul (.fin 0) q = .fin 0 := by
  cases q <;> rfl

@[simp] theorem mul_fin_zero_right (p : NatPlusInfinity) : mul p (.fin 0) = .fin 0 := by
  cases p with
  | inf => rfl
  | fin m => cases m <;> rfl

@[simp] theorem mul_fin_fin (m n : Nat) : mul (.fin m) (.fin n) = .fin (m * n) := by
  cases m with
  | zero => simp [mul]
  | succ m =>
    cases n with
    | zero => simp [mul]
    | succ n => rfl

@[simp] theorem mul_inf_succ (n : Nat) : mul .inf (.fin (n + 1)) = .inf := rfl
@[simp] theorem mul_succ_inf (m : Nat) : mul (.fin (m + 1)) .inf = .inf := rfl
@[simp] theorem mul_inf_inf : mul .inf .inf = .inf := rfl

def natPlusInfinityModality : Modality NatPlusInfinity where
  zero := .fin 0
  one := .fin 1
  omega := .inf
  add := add
  mul := mul
  meet := meet
  decEqZero p := decEq p (.fin 0)
  add_assoc p q r := by
    cases p <;> cases q <;> cases r <;> simp [add, Nat.add_assoc]
  add_comm p q := by
    cases p <;> cases q <;> simp [add, Nat.add_comm]
  zero_add p := by
    cases p <;> simp [add]
  add_zero p := by
    cases p <;> simp [add]
  mul_assoc p q r := by
    cases p with
    | fin m =>
      cases m with
      | zero => simp
      | succ m =>
        cases q with
        | fin n =>
          cases n with
          | zero => simp
          | succ n =>
            cases r with
            | fin k => simp [Nat.mul_assoc]
            | inf =>
              have hmn : (m + 1) * (n + 1) = (m * (n + 1) + n) + 1 := by
                rw [Nat.succ_mul]; omega
              rw [mul_fin_fin, hmn, mul_succ_inf, mul_succ_inf, mul_succ_inf]
        | inf =>
          cases r with
          | fin k =>
            cases k with
            | zero => simp
            | succ k => rfl
          | inf => rfl
    | inf =>
      cases q with
      | fin n =>
        cases n with
        | zero => simp
        | succ n =>
          cases r with
          | fin k =>
            cases k with
            | zero => simp
            | succ k =>
              have hnk : (n + 1) * (k + 1) = (n * (k + 1) + k) + 1 := by
                rw [Nat.succ_mul]; omega
              rw [mul_fin_fin, hnk, mul_inf_succ, mul_inf_succ, mul_inf_succ]
          | inf => rfl
      | inf =>
        cases r with
        | fin k => cases k <;> rfl
        | inf => rfl
  one_mul p := by
    cases p with
    | inf => rfl
    | fin n => simp [Nat.one_mul]
  mul_one p := by
    cases p with
    | inf => rfl
    | fin n => simp [Nat.mul_one]
  zero_mul := mul_fin_zero_left
  mul_zero := mul_fin_zero_right
  left_distrib p q r := by
    cases p with
    | fin m =>
      cases m with
      | zero => simp [add]
      | succ m =>
        cases q with
        | fin n =>
          cases r with
          | fin k => simp [add, Nat.mul_add]
          | inf => cases n <;> rfl
        | inf =>
          cases r with
          | fin k => cases k <;> rfl
          | inf => rfl
    | inf =>
      cases q with
      | fin n =>
        cases n with
        | zero =>
          cases r with
          | fin k => cases k <;> rfl
          | inf => rfl
        | succ n =>
          cases r with
          | fin k =>
            have hnk : (n + 1) + k = (n + k) + 1 := by omega
            cases k <;> simp [add, hnk]
          | inf => rfl
      | inf =>
        cases r with
        | fin k => cases k <;> rfl
        | inf => rfl
  right_distrib p q r := by
    cases r with
    | fin k =>
      cases k with
      | zero => simp [add]
      | succ k =>
        cases p with
        | fin m =>
          cases q with
          | fin n => simp [add, Nat.add_mul]
          | inf => cases m <;> rfl
        | inf =>
          cases q with
          | fin n => cases n <;> rfl
          | inf => rfl
    | inf =>
      cases p with
      | fin m =>
        cases m with
        | zero =>
          cases q with
          | fin n => cases n <;> rfl
          | inf => rfl
        | succ m =>
          cases q with
          | fin n =>
            have hmn : (m + 1) + n = (m + n) + 1 := by omega
            cases n <;> simp [add, hmn]
          | inf => rfl
      | inf =>
        cases q with
        | fin n => cases n <;> rfl
        | inf => rfl
  meet_assoc p q r := by
    cases p <;> cases q <;> cases r <;> simp [meet, NatModality.natMax_assoc]
  meet_comm p q := by
    cases p <;> cases q <;> simp [meet, NatModality.natMax_comm]
  meet_idem p := by
    cases p <;> simp [meet, NatModality.natMax_idem]
  mul_left_distrib_meet p q r := by
    cases p with
    | fin m =>
      cases m with
      | zero => simp [meet, NatModality.natMax]
      | succ m =>
        cases q with
        | fin n =>
          cases r with
          | fin k => simp [meet, NatModality.mul_left_distrib_natMax]
          | inf => cases n <;> rfl
        | inf =>
          cases r with
          | fin k => cases k <;> rfl
          | inf => rfl
    | inf =>
      cases q with
      | fin n =>
        cases n with
        | zero =>
          cases r with
          | fin k =>
            cases k with
            | zero => rfl
            | succ k =>
              have hmax : NatModality.natMax 0 (k + 1) = k + 1 := by
                unfold NatModality.natMax; split <;> omega
              simp [meet, hmax]
          | inf => rfl
        | succ n =>
          cases r with
          | fin k =>
            have hmax : ∃ u, NatModality.natMax (n + 1) k = u + 1 := by
              refine ⟨NatModality.natMax (n + 1) k - 1, ?_⟩
              unfold NatModality.natMax; split <;> omega
            rcases hmax with ⟨u, hu⟩
            cases k <;> simp [meet, hu]
          | inf => rfl
      | inf =>
        cases r with
        | fin k => cases k <;> rfl
        | inf => rfl
  mul_right_distrib_meet p q r := by
    cases r with
    | fin k =>
      cases k with
      | zero => simp [meet, NatModality.natMax]
      | succ k =>
        cases p with
        | fin m =>
          cases q with
          | fin n => simp [meet, NatModality.mul_right_distrib_natMax]
          | inf => cases m <;> rfl
        | inf =>
          cases q with
          | fin n => cases n <;> rfl
          | inf => rfl
    | inf =>
      cases p with
      | fin m =>
        cases m with
        | zero =>
          cases q with
          | fin n =>
            cases n with
            | zero => rfl
            | succ n =>
              have hmax : NatModality.natMax 0 (n + 1) = n + 1 := by
                unfold NatModality.natMax; split <;> omega
              simp [meet, hmax]
          | inf => rfl
        | succ m =>
          cases q with
          | fin n =>
            have hmax : ∃ u, NatModality.natMax (m + 1) n = u + 1 := by
              refine ⟨NatModality.natMax (m + 1) n - 1, ?_⟩
              unfold NatModality.natMax; split <;> omega
            rcases hmax with ⟨u, hu⟩
            cases n <;> simp [meet, hu]
          | inf => rfl
      | inf =>
        cases q with
        | fin n => cases n <;> rfl
        | inf => rfl
  add_left_distrib_meet p q r := by
    cases p <;> cases q <;> cases r <;> simp [add, meet, NatModality.add_left_distrib_natMax]
  add_right_distrib_meet p q r := by
    cases p <;> cases q <;> cases r <;> simp [add, meet, NatModality.add_right_distrib_natMax]
  omega_le_one := rfl
  omega_mul_add_le p q := by
    cases p with
    | inf =>
      cases q with
      | inf => rfl
      | fin n => cases n <;> rfl
    | fin m =>
      cases q with
      | inf => rfl
      | fin n =>
        cases m with
        | zero =>
          cases n with
          | zero => rfl
          | succ n =>
            have h : (0 : Nat) + (n + 1) = n + 1 := Nat.zero_add (n + 1)
            simp [add, h, meet]
        | succ m =>
          have h : (m + 1) + n = (m + n) + 1 := by omega
          cases n <;> simp [add, h, meet]

theorem natPlusInfinityHasWellBehavedZero :
    natPlusInfinityModality.HasWellBehavedZero where
  nonTrivial := by decide
  zero_product {p q} h := by
    cases p with
    | inf =>
      cases q with
      | inf => contradiction
      | fin n =>
        cases n with
        | zero => exact Or.inr rfl
        | succ n => contradiction
    | fin m =>
      cases m with
      | zero => exact Or.inl rfl
      | succ m =>
        cases q with
        | inf => contradiction
        | fin n =>
          cases n with
          | zero => exact Or.inr rfl
          | succ n =>
            change NatPlusInfinity.fin ((m + 1) * (n + 1)) = .fin 0 at h
            injection h with h'
            have : (m + 1) * (n + 1) > 0 := Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos n)
            omega
  add_positive_left {p q} h := by
    cases p with
    | inf => contradiction
    | fin m =>
      cases q with
      | inf => contradiction
      | fin n =>
        change NatPlusInfinity.fin (m + n) = .fin 0 at h
        injection h with h'
        have : m = 0 := by omega
        subst this
        rfl
  meet_positive_left {p q} h := by
    cases p with
    | inf => contradiction
    | fin m =>
      cases q with
      | inf => contradiction
      | fin n =>
        change NatPlusInfinity.fin (NatModality.natMax m n) = .fin 0 at h
        injection h with h'
        unfold NatModality.natMax at h'
        have : m = 0 := by split at h' <;> omega
        subst this
        rfl

def subNatPlusInf : NatPlusInfinity → NatPlusInfinity → NatPlusInfinity
  | .inf, _ => .inf
  | .fin _, .inf => .inf
  | .fin m, .fin n => .fin (m - n)

theorem natPlusInfinitySupportsSubtraction :
    natPlusInfinityModality.SupportsSubtraction := by
  intro p q r h
  refine ⟨subNatPlusInf p q, ?_, ?_⟩
  · cases p with
    | inf => rfl
    | fin m =>
      cases q with
      | inf =>
        cases r <;> contradiction
      | fin n =>
        cases r with
        | inf => contradiction
        | fin k =>
          change NatPlusInfinity.fin m = .fin (NatModality.natMax m (k + n)) at h
          injection h with h'
          change NatPlusInfinity.fin m = .fin (NatModality.natMax m ((m - n) + n))
          congr 1
          unfold NatModality.natMax at h' ⊢
          split at h' <;> split <;> omega
  · intro r' hr'
    cases p with
    | inf => rfl
    | fin m =>
      cases q with
      | inf =>
        cases r <;> contradiction
      | fin n =>
        cases r with
        | inf => contradiction
        | fin k =>
          cases r' with
          | inf => contradiction
          | fin k' =>
            change NatPlusInfinity.fin m = .fin (NatModality.natMax m (k' + n)) at hr'
            injection hr' with hr''
            change NatPlusInfinity.fin (m - n) = .fin (NatModality.natMax (m - n) k')
            congr 1
            unfold NatModality.natMax at hr'' ⊢
            split at hr'' <;> split <;> omega

end NatPlusInfinity

/-- 5. Two-point Bounded Distributive Security Lattice (`Public`, `Secret`)
    used for M3 Section 6 Non-Interference (`Graded.Heap.Non-interference`):
    - `Public` (`⊥`) is `𝟙` and `ω`
    - `Secret` (`⊤`) is `𝟘`
    - `add = meet = join` (so `Public ≤ Secret`, i.e., `Public = meet Public Secret`). -/
inductive SecurityLevel where
  | publicLvl : SecurityLevel
  | secretLvl : SecurityLevel
  deriving DecidableEq, Repr

namespace SecurityLevel

def join : SecurityLevel → SecurityLevel → SecurityLevel
  | .publicLvl, .publicLvl => .publicLvl
  | _, _ => .secretLvl

def meetLat : SecurityLevel → SecurityLevel → SecurityLevel
  | .secretLvl, .secretLvl => .secretLvl
  | _, _ => .publicLvl

def securityModality : Modality SecurityLevel where
  zero := .secretLvl
  one := .publicLvl
  omega := .publicLvl
  add := meetLat
  mul := join
  meet := meetLat
  decEqZero p := decEq p .secretLvl
  add_assoc p q r := by cases p <;> cases q <;> cases r <;> rfl
  add_comm p q := by cases p <;> cases q <;> rfl
  zero_add p := by cases p <;> rfl
  add_zero p := by cases p <;> rfl
  mul_assoc p q r := by cases p <;> cases q <;> cases r <;> rfl
  one_mul p := by cases p <;> rfl
  mul_one p := by cases p <;> rfl
  zero_mul p := by cases p <;> rfl
  mul_zero p := by cases p <;> rfl
  left_distrib p q r := by cases p <;> cases q <;> cases r <;> rfl
  right_distrib p q r := by cases p <;> cases q <;> cases r <;> rfl
  meet_assoc p q r := by cases p <;> cases q <;> cases r <;> rfl
  meet_comm p q := by cases p <;> cases q <;> rfl
  meet_idem p := by cases p <;> rfl
  mul_left_distrib_meet p q r := by cases p <;> cases q <;> cases r <;> rfl
  mul_right_distrib_meet p q r := by cases p <;> cases q <;> cases r <;> rfl
  add_left_distrib_meet p q r := by cases p <;> cases q <;> cases r <;> rfl
  add_right_distrib_meet p q r := by cases p <;> cases q <;> cases r <;> rfl
  omega_le_one := rfl
  omega_mul_add_le p q := by cases p <;> cases q <;> rfl

theorem securitySupportsSubtraction : securityModality.SupportsSubtraction :=
  securityModality.addEqMeet_supports_subtraction (fun _ _ ↦ rfl)

end SecurityLevel

end FeasibleUnivalence
