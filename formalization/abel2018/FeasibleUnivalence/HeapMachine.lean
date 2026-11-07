/-
Copyright (c) 2025–2026 Andreas Abel, Nils Anders Danielsson, Oskar Eriksson.
Lean 4 translation and extension prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Sources:
- M3: On Recursion in Graded Modal Type Theory (ICFP 2026, DOI 10.1145/3828677),
  Agda tag `icfp26` (`93987e3ddc11f583fc3ecdc05472e1dac4094c4f`):
  - `Graded/Heap/Untyped.agda` & `Graded/Heap/Untyped/Properties.agda`
  - `Graded/Heap/Usage.agda`, `Graded/Heap/Usage/Inversion.agda`,
    `Graded/Heap/Usage/Properties.agda` (Lemmas 4.1 & 4.2)
  - `Graded/Heap/Reduction.agda` & `Graded/Heap/Usage/Reduction.agda`
    (Theorem 4.3 `usage_pres_step` and `¬▸-⇒ₙ`)
  - `Graded/Heap/Bisimilarity.agda` & `Graded/Heap/Soundness.agda`
    (Theorems 4.6–4.10)
  - `Graded/Heap/Non-interference.agda` (Section 6, Theorem 6.1 `non_interference`)
-/
import FeasibleUnivalence.Modality
import FeasibleUnivalence.Usage
import FeasibleUnivalence.Erasure

namespace FeasibleUnivalence

open Abel2018

/-! ## 1. Context Update (`Conₘ.update`) and Mode Identities (`Graded.Context.Properties`) -/

namespace Mode

variable {M : Type} (𝕄 : Modality M)

/-- Right identity `p · ⌜ ⌞ p ⌟ ⌝ = p` (`·⌜⌞⌟⌝` in `Graded/Mode.agda`). -/
@[simp] theorem mul_toGrade_ofGrade (p : M) :
    𝕄.mul p (toGrade 𝕄 (ofGrade 𝕄 p)) = p := by
  by_cases hp : p = 𝕄.zero <;> simp [ofGrade, toGrade, hp, 𝕄.mul_zero, 𝕄.mul_one]

/-- Left identity `⌜ ⌞ p ⌟ ⌝ · p = p` (`⌜⌞⌟⌝·` in `Graded/Mode.agda`). -/
@[simp] theorem toGrade_ofGrade_mul (p : M) :
    𝕄.mul (toGrade 𝕄 (ofGrade 𝕄 p)) p = p := by
  by_cases hp : p = 𝕄.zero <;> simp [ofGrade, toGrade, hp, 𝕄.zero_mul, 𝕄.one_mul]

/-- Mode scaling of `ofGrade`: under `HasWellBehavedZero`, `⌞ p ⌟ ᵐ· q = ⌞ p · q ⌟`
    (`⌞⌟ᵐ·` in `Graded/Mode.agda`). -/
theorem scale_ofGrade {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero) (p q : M) :
    scale 𝕄 (ofGrade 𝕄 p) q = ofGrade 𝕄 (𝕄.mul p q) := by
  by_cases hp : p = 𝕄.zero
  · subst hp
    simp [ofGrade, scale, 𝕄.zero_mul]
  · by_cases hq : q = 𝕄.zero
    · subst hq
      simp [ofGrade, scale, hp, 𝕄.mul_zero]
    · have hpq : 𝕄.mul p q ≠ 𝕄.zero := by
        intro h0
        rcases hw.zero_product h0 with h | h
        · exact hp h
        · exact hq h
      simp [ofGrade, scale, hp, hq, hpq]

end Mode

namespace Usage

variable {M : Type} {𝕄 : Modality M}

/-- Changing the grade of `Mode.ofGrade` when zero-preservation holds (`▸-≤ᵐ` in M3):
    if `δ ▸[ ⌞ p ⌟ ] t` and `(p = 𝟘 → q = 𝟘)`, then there exists `δ'` such that
    `δ' ▸[ ⌞ q ⌟ ] t`, `q ·ᶜ δ' = q ·ᶜ δ`, and `Conₘ.le 𝕄 δ' δ`. -/
theorem change_ofGrade {δ : Conₘ M} {p q : M} {t : GTerm M}
    (ht : Usage 𝕄 δ (Mode.ofGrade 𝕄 p) t)
    (hpq : p = 𝕄.zero → q = 𝕄.zero) :
    ∃ δ' : Conₘ M,
      Usage 𝕄 δ' (Mode.ofGrade 𝕄 q) t ∧
      Conₘ.scale 𝕄 q δ' = Conₘ.scale 𝕄 q δ ∧
      (q ≠ 𝕄.zero → δ' = δ) := by
  by_cases hq : q = 𝕄.zero
  · subst hq
    refine ⟨Conₘ.zero 𝕄, ?_, ?_, ?_⟩
    · rw [Mode.ofGrade_zero]
      exact zeroMode_usage t
    · simp only [Conₘ.zero_scale]
    · intro hne; exact False.elim (hne rfl)
  · have hp : p ≠ 𝕄.zero := fun hp0 ↦ hq (hpq hp0)
    refine ⟨δ, ?_, rfl, fun _ ↦ rfl⟩
    rw [Mode.ofGrade_ne_zero 𝕄 hq]
    rw [Mode.ofGrade_ne_zero 𝕄 hp] at ht
    exact ht

/-- Canonical mode-scaled usage context `⌜ ⌞ q ⌟ ⌝ ·ᶜ δ` (`▸-≤ᵐ` with explicit witness):
    if `δ ▸[ ⌞ p ⌟ ] t` and `(p = 𝟘 → q = 𝟘)`, then `(⌜ ⌞ q ⌟ ⌝ ·ᶜ δ) ▸[ ⌞ q ⌟ ] t`
    and `q ·ᶜ (⌜ ⌞ q ⌟ ⌝ ·ᶜ δ) = q ·ᶜ δ`. -/
theorem ofGrade_scale_self {δ : Conₘ M} {p q : M} {t : GTerm M}
    (ht : Usage 𝕄 δ (Mode.ofGrade 𝕄 p) t)
    (hpq : p = 𝕄.zero → q = 𝕄.zero) :
    Usage 𝕄 (Conₘ.scale 𝕄 (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 q)) δ) (Mode.ofGrade 𝕄 q) t := by
  by_cases hq : q = 𝕄.zero
  · subst hq
    simp only [Mode.ofGrade_zero, Mode.toGrade, Conₘ.zero_scale]
    exact zeroMode_usage t
  · have hp : p ≠ 𝕄.zero := fun hp0 ↦ hq (hpq hp0)
    simp only [Mode.ofGrade_ne_zero 𝕄 hq, Mode.toGrade, Conₘ.one_scale]
    rw [Mode.ofGrade_ne_zero 𝕄 hp] at ht
    exact ht

/-- Under `HasWellBehavedZero`, `p ≤ q` implies `(p = 𝟘 → q = 𝟘)`. -/
theorem zero_imp_of_le (hw : 𝕄.HasWellBehavedZero) {p q : M}
    (hle : 𝕄.le p q) (hp : p = 𝕄.zero) : q = 𝕄.zero := by
  rw [hp] at hle
  exact hw.zero_le_eq_zero hle

/-- Under `HasWellBehavedZero`, `p ≤ r + q` and `p = 𝟘` imply `r = 𝟘 ∧ q = 𝟘`. -/
theorem zero_imp_of_le_add (hw : 𝕄.HasWellBehavedZero) {p r q : M}
    (hle : 𝕄.le p (𝕄.add r q)) (hp : p = 𝕄.zero) : r = 𝕄.zero ∧ q = 𝕄.zero := by
  rw [hp] at hle
  exact hw.add_positive (hw.zero_le_eq_zero hle)

/-- Inversion of canonical numeral usage (`inv-usage-numeral` in M3):
    every numeral `GTerm.suck k` has usage bounded by `𝟘ᶜ`. -/
theorem inv_suck {γ : Conₘ M} {m : Mode} :
    ∀ k : Nat, Usage 𝕄 γ m (GTerm.suck k) → Conₘ.le 𝕄 γ (Conₘ.zero 𝕄)
  | 0, h => inv_zero h
  | k + 1, h => inv_suck k (inv_succ h)

end Usage

namespace Conₘ

variable {M : Type} (𝕄 : Modality M)

theorem wk_comp (τ ρ : Wk) (γ : Conₘ M) :
    wk 𝕄 τ (wk 𝕄 ρ γ) = wk 𝕄 (compWk τ ρ) γ := by
  induction τ generalizing ρ γ with
  | id => rfl
  | step τ ih =>
    simp only [wk, compWk]
    exact congrArg (fun δ ↦ cons δ 𝕄.zero) (ih ρ γ)
  | lift τ ih =>
    cases ρ with
    | id => rfl
    | step ρ =>
      have ht : tail (cons (wk 𝕄 ρ γ) 𝕄.zero) = wk 𝕄 ρ γ := rfl
      have hh : head (cons (wk 𝕄 ρ γ) 𝕄.zero) = 𝕄.zero := rfl
      simp only [wk, compWk, ht, hh]
      exact congrArg (fun δ ↦ cons δ 𝕄.zero) (ih ρ γ)
    | lift ρ =>
      have ht : tail (cons (wk 𝕄 ρ (tail γ)) (head γ)) = wk 𝕄 ρ (tail γ) := rfl
      have hh : head (cons (wk 𝕄 ρ (tail γ)) (head γ)) = head γ := rfl
      simp only [wk, compWk, ht, hh]
      exact congrArg (fun δ ↦ cons δ (head γ)) (ih ρ (tail γ))

/-- Pointwise update `γ , x ≔ p` (`_⟨_≔_⟩` / `_,_≔_` in `Graded/Context.agda`). -/
def update (γ : Conₘ M) (x : Nat) (p : M) : Conₘ M :=
  fun y ↦ if y = x then p else γ y

@[simp] theorem update_eq_self (γ : Conₘ M) (x : Nat) (p : M) :
    update γ x p x = p := by
  simp [update]

theorem update_eq_of_ne (γ : Conₘ M) {x y : Nat} (p : M) (h : y ≠ x) :
    update γ x p y = γ y := by
  simp [update, h]

@[simp] theorem update_self (γ : Conₘ M) (x : Nat) :
    update γ x (γ x) = γ := by
  funext y
  by_cases h : y = x
  · subst h; simp [update]
  · simp [update, h]

@[simp] theorem update_twice (γ : Conₘ M) (x : Nat) (p q : M) :
    update (update γ x p) x q = update γ x q := by
  funext y
  by_cases h : y = x <;> simp [update, h]

@[simp] theorem update_zero_eq_single (x : Nat) (p : M) :
    update (zero 𝕄) x p = single 𝕄 x p := rfl

@[simp] theorem update_zero_zero (x : Nat) :
    update (zero 𝕄) x 𝕄.zero = zero 𝕄 := by
  funext y
  by_cases h : y = x <;> simp [update, zero, h]

@[simp] theorem update_cons_zero (γ : Conₘ M) (q p : M) :
    update (cons γ q) 0 p = cons γ p := by
  funext y; cases y <;> rfl

@[simp] theorem update_cons_succ (γ : Conₘ M) (q : M) (x : Nat) (p : M) :
    update (cons γ q) (x + 1) p = cons (update γ x p) q := by
  funext y
  cases y with
  | zero => rfl
  | succ y =>
    simp only [update, cons]
    by_cases h : y = x <;> simp [h]

theorem update_mono {γ δ : Conₘ M} {p q : M} (x : Nat)
    (hγ : le 𝕄 γ δ) (hp : 𝕄.le p q) :
    le 𝕄 (update γ x p) (update δ x q) := by
  intro y
  by_cases h : y = x
  · subst h; simp [update, hp]
  · simp [update, h, hγ y]

theorem update_mono_left {γ δ : Conₘ M} (x : Nat) (p : M) (hγ : le 𝕄 γ δ) :
    le 𝕄 (update γ x p) (update δ x p) :=
  update_mono 𝕄 x hγ (𝕄.le_refl p)

theorem update_distrib_add (γ δ : Conₘ M) (x : Nat) (p q : M) :
    update (add 𝕄 γ δ) x (𝕄.add p q) = add 𝕄 (update γ x p) (update δ x q) := by
  funext y
  by_cases h : y = x <;> simp [update, add, h]

theorem update_distrib_scale (p : M) (γ : Conₘ M) (x : Nat) (q : M) :
    update (scale 𝕄 p γ) x (𝕄.mul p q) = scale 𝕄 p (update γ x q) := by
  funext y
  by_cases h : y = x <;> simp [update, scale, h]

end Conₘ

/-! ## 2. Untyped Heap Machine Syntax (`Graded.Heap.Untyped`, M3 Section 4.1) -/

/-- A heap closure (`Entry` in `Graded.Heap.Untyped`): a graded term paired with an
    environment weakening mapping free variables of `term` to heap pointers. -/
structure Entry (M : Type) where
  term : GTerm M
  env : Wk
  deriving DecidableEq, Repr

namespace Entry

variable {M : Type}

/-- Weakening of a closure (`wkᵉ` in `Graded.Heap.Untyped`). -/
def wk (ρ : Wk) (e : Entry M) : Entry M :=
  ⟨e.term, compWk ρ e.env⟩

/-- Single-step weakening of a closure (`wk1ᵉ` in `Graded.Heap.Untyped`). -/
def wk1 (e : Entry M) : Entry M :=
  ⟨e.term, .step e.env⟩

@[simp] theorem wk_step_id (e : Entry M) : wk (.step .id) e = wk1 e := by
  cases e; rfl

end Entry

/-- Evaluation continuation frames (`Cont` in `Graded.Heap.Untyped`, M3 Section 4.1). -/
inductive Cont (M : Type) where
  | appₑ : M → GTerm M → Wk → Cont M
  | fstₑ : M → Cont M
  | sndₑ : M → Cont M
  | prodrecₑ : M → M → M → GTerm M → GTerm M → Wk → Cont M
  | unitrecₑ : M → M → GTerm M → GTerm M → Wk → Cont M
  | natrecₑ : M → M → M → GTerm M → GTerm M → GTerm M → Wk → Cont M
  | sucₑ : Cont M
  deriving DecidableEq, Repr

namespace Cont

variable {M : Type}

/-- Weakening of a continuation frame (`wkᶜ` in `Graded.Heap.Untyped`). -/
def wk (ρ : Wk) : Cont M → Cont M
  | .appₑ p u ρ' => .appₑ p u (compWk ρ ρ')
  | .fstₑ p => .fstₑ p
  | .sndₑ p => .sndₑ p
  | .prodrecₑ r p q A u ρ' => .prodrecₑ r p q A u (compWk ρ ρ')
  | .unitrecₑ p q A u ρ' => .unitrecₑ p q A u (compWk ρ ρ')
  | .natrecₑ p q r A z s ρ' => .natrecₑ p q r A z s (compWk ρ ρ')
  | .sucₑ => .sucₑ

def wk1 : Cont M → Cont M := wk (.step .id)

def wk2 : Cont M → Cont M := wk (.step (.step .id))

/-- Multiplicity of a continuation frame (`∣_∣ᶜ[_]≡_` in `Graded.Heap.Untyped`),
    parameterized by the `natrec` multiplicity function `nr₂ : M → M → M`. -/
def mult (𝕄 : Modality M) (nr₂ : M → M → M) : Cont M → M
  | .appₑ _ _ _ => 𝕄.one
  | .fstₑ _ => 𝕄.one
  | .sndₑ _ => 𝕄.one
  | .prodrecₑ r _ _ _ _ _ => r
  | .unitrecₑ p _ _ _ _ => p
  | .natrecₑ p _ r _ _ _ _ => nr₂ p r
  | .sucₑ => 𝕄.one

@[simp] theorem mult_wk (𝕄 : Modality M) (nr₂ : M → M → M) (ρ : Wk) (c : Cont M) :
    mult 𝕄 nr₂ (wk ρ c) = mult 𝕄 nr₂ c := by
  cases c <;> rfl

end Cont

/-- Evaluation stacks (`Stack` in `Graded.Heap.Untyped`). -/
abbrev Stack (M : Type) := List (Cont M)

namespace Stack

variable {M : Type}

/-- Weakening of a stack (`wkˢ` in `Graded.Heap.Untyped`). -/
def wk (ρ : Wk) : Stack M → Stack M
  | [] => []
  | c :: S => Cont.wk ρ c :: wk ρ S

def wk1 : Stack M → Stack M := wk (.step .id)

def wk2 : Stack M → Stack M := wk (.step (.step .id))

/-- A stack of `k` successor frames (`sucₛ` in `Graded.Heap.Untyped`). -/
def sucs : Nat → Stack M
  | 0 => []
  | k + 1 => .sucₑ :: sucs k

@[simp] theorem wk_sucs (ρ : Wk) : ∀ k : Nat, wk ρ (sucs (M := M) k) = sucs k
  | 0 => rfl
  | k + 1 => congrArg (List.cons (.sucₑ : Cont M)) (wk_sucs ρ k)

/-- Multiplicity of a stack (`∣_∣≡_` in `Graded.Heap.Untyped`), representing how many
    copies of the head term are currently demanded by the evaluation context. -/
def mult (𝕄 : Modality M) (nr₂ : M → M → M) : Stack M → M
  | [] => 𝕄.one
  | c :: S => 𝕄.mul (mult 𝕄 nr₂ S) (Cont.mult 𝕄 nr₂ c)

@[simp] theorem mult_nil (𝕄 : Modality M) (nr₂ : M → M → M) :
    mult 𝕄 nr₂ [] = 𝕄.one := rfl

@[simp] theorem mult_cons (𝕄 : Modality M) (nr₂ : M → M → M) (c : Cont M) (S : Stack M) :
    mult 𝕄 nr₂ (c :: S) = 𝕄.mul (mult 𝕄 nr₂ S) (Cont.mult 𝕄 nr₂ c) := rfl

@[simp] theorem mult_wk (𝕄 : Modality M) (nr₂ : M → M → M) (ρ : Wk) :
    ∀ S : Stack M, mult 𝕄 nr₂ (wk ρ S) = mult 𝕄 nr₂ S
  | [] => rfl
  | c :: S => by simp [wk, mult, Cont.mult_wk, mult_wk 𝕄 nr₂ ρ S]

@[simp] theorem mult_wk1 (𝕄 : Modality M) (nr₂ : M → M → M) (S : Stack M) :
    mult 𝕄 nr₂ (wk1 S) = mult 𝕄 nr₂ S :=
  mult_wk 𝕄 nr₂ (.step .id) S

@[simp] theorem mult_wk2 (𝕄 : Modality M) (nr₂ : M → M → M) (S : Stack M) :
    mult 𝕄 nr₂ (wk2 S) = mult 𝕄 nr₂ S :=
  mult_wk 𝕄 nr₂ (.step (.step .id)) S

@[simp] theorem mult_sucs (𝕄 : Modality M) (nr₂ : M → M → M) :
    ∀ k : Nat, mult 𝕄 nr₂ (sucs k) = 𝕄.one
  | 0 => rfl
  | k + 1 => by simp [sucs, Cont.mult, mult_sucs 𝕄 nr₂ k, 𝕄.mul_one]

/-- Relational presentation of continuation multiplicity (`∣_∣ᶜ≡_` in M3). -/
def ContMult (𝕄 : Modality M) (nr₂ : M → M → M) (c : Cont M) (q : M) : Prop :=
  q = Cont.mult 𝕄 nr₂ c

/-- Relational presentation of stack multiplicity (`∣_∣≡_` in M3). -/
def StackMult (𝕄 : Modality M) (nr₂ : M → M → M) (S : Stack M) (p : M) : Prop :=
  p = mult 𝕄 nr₂ S

theorem contMult_det {𝕄 : Modality M} {nr₂ : M → M → M} {c : Cont M} {q₁ q₂ : M}
    (h₁ : ContMult 𝕄 nr₂ c q₁) (h₂ : ContMult 𝕄 nr₂ c q₂) : q₁ = q₂ :=
  h₁.trans h₂.symm

theorem stackMult_det {𝕄 : Modality M} {nr₂ : M → M → M} {S : Stack M} {p₁ p₂ : M}
    (h₁ : StackMult 𝕄 nr₂ S p₁) (h₂ : StackMult 𝕄 nr₂ S p₂) : p₁ = p₂ :=
  h₁.trans h₂.symm

end Stack

/-- Specification of a valid `natrec` multiplicity function `nr₂ : M → M → M`
    (unifying M3's `Nr-available` factoring `nr₂` and `Nr-not-available-GLB`
    greatest lower bound of `nrᵢ r 𝟙 p`). -/
structure NatrecMultFn {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M) : Prop where
  le_one : ∀ p r, 𝕄.le (nr₂ p r) 𝕄.one
  le_step : ∀ p r, 𝕄.le (nr₂ p r) (𝕄.add p (𝕄.mul r (nr₂ p r)))
  maximal : ∀ {p r x}, 𝕄.le x 𝕄.one → 𝕄.le x (𝕄.add p (𝕄.mul r x)) → 𝕄.le x (nr₂ p r)

namespace NatrecMultFn

variable {M : Type} {𝕄 : Modality M}

/-- M3 Section 5.2: any function `nr₂ p r` computing the greatest lower bound of
    `nrᵢ r 𝟙 p` under `HasWellBehavedGLBs` is a valid `NatrecMultFn`. -/
theorem of_GLB (hwb : 𝕄.HasWellBehavedGLBs) {nr₂ : M → M → M}
    (hglb : ∀ p r, 𝕄.GreatestLowerBound (nr₂ p r) (𝕄.nrᵢ r 𝕄.one p)) :
    NatrecMultFn 𝕄 nr₂ where
  le_one p r := 𝕄.nrᵢ_GLB_le₀ (hglb p r)
  le_step p r := 𝕄.nrᵢ_GLB_le_step hwb (hglb p r)
  maximal h1 h2 := 𝕄.le_nrᵢ_GLB h1 h2 (hglb _ _)

/-- When `𝟙` is the bottom element of the modality (`∀ q, 𝟙 ≤ q`, as in bounded distributive
    security lattices), the constant function `fun _ _ ↦ 𝟙` is a valid `NatrecMultFn`. -/
theorem of_one_bottom (hbot : ∀ q : M, 𝕄.le 𝕄.one q) :
    NatrecMultFn 𝕄 (fun _ _ ↦ 𝕄.one) where
  le_one _ _ := 𝕄.le_refl 𝕄.one
  le_step p r := hbot (𝕄.add p (𝕄.mul r 𝕄.one))
  maximal h1 _ := h1

end NatrecMultFn

/-! ### Heaps and Heap Lookups (`Graded.Heap.Untyped`, M3 Section 4.1) -/

/-- Heaps (`Heap` in `Graded.Heap.Untyped`): snoc-lists of graded closures `(p, e)`
    or dummy entries `●` representing erased free variables. -/
inductive Heap (M : Type) where
  | nil : Heap M
  | cons : Heap M → M → Entry M → Heap M
  | dummy : Heap M → Heap M
  deriving DecidableEq, Repr

/-- A heap of `k` dummy entries (`erasedHeap` in `Graded.Heap.Untyped`). -/
def erasedHeap {M : Type} : Nat → Heap M
  | 0 => .nil
  | k + 1 => .dummy (erasedHeap k)

namespace Heap

variable {M : Type}

/-- Total number of cells in the heap (`m` index of `Heap k m`). -/
def size : Heap M → Nat
  | .nil => 0
  | .cons H _ _ => H.size + 1
  | .dummy H => H.size + 1

/-- Number of dummy cells in the heap (`k` index of `Heap k m`). -/
def numDummies : Heap M → Nat
  | .nil => 0
  | .cons H _ _ => H.numDummies
  | .dummy H => H.numDummies + 1

@[simp] theorem size_erasedHeap (k : Nat) : (erasedHeap (M := M) k).size = k := by
  induction k <;> simp [erasedHeap, size, *]

@[simp] theorem numDummies_erasedHeap (k : Nat) : (erasedHeap (M := M) k).numDummies = k := by
  induction k <;> simp [erasedHeap, numDummies, *]

/-- Grade lookup `H ⟨ y ⟩ʰ` at heap pointer `y` (`_⟨_⟩ʰ` in `Graded.Heap.Untyped`). -/
def lookupGrade (𝕄 : Modality M) : Heap M → Nat → M
  | .nil, _ => 𝕄.zero
  | .cons _ p _, 0 => p
  | .cons H _ _, y + 1 => lookupGrade 𝕄 H y
  | .dummy _, 0 => 𝕄.zero
  | .dummy H, y + 1 => lookupGrade 𝕄 H y

end Heap

/-- Tracked heap lookup with grade subtraction (`_⊢_↦[_]_⨾_` in `Graded.Heap.Untyped`):
    looking up `q` copies of pointer `y` in `H` requires `p - q ≡ r` (`𝕄.SubEq p q r`),
    returns weakened closure `e`, and updates the cell's grade from `p` to `r` in `H'`. -/
inductive HeapLookup {M : Type} (𝕄 : Modality M) :
    Heap M → Nat → M → Entry M → Heap M → Prop where
  | here {H : Heap M} {p q r : M} {e : Entry M} :
      𝕄.SubEq p q r →
      HeapLookup 𝕄 (.cons H p e) 0 q (Entry.wk1 e) (.cons H r e)
  | there {H H' : Heap M} {y : Nat} {p q : M} {e e' : Entry M} :
      HeapLookup 𝕄 H y q e H' →
      HeapLookup 𝕄 (.cons H p e') (y + 1) q (Entry.wk1 e) (.cons H' p e')
  | thereDummy {H H' : Heap M} {y : Nat} {q : M} {e : Entry M} :
      HeapLookup 𝕄 H y q e H' →
      HeapLookup 𝕄 (.dummy H) (y + 1) q (Entry.wk1 e) (.dummy H')

/-- Untracked heap lookup without grade update (`_⊢_↦_` in `Graded.Heap.Untyped`). -/
inductive HeapLookupUntracked {M : Type} : Heap M → Nat → Entry M → Prop where
  | here {H : Heap M} {p : M} {e : Entry M} :
      HeapLookupUntracked (.cons H p e) 0 (Entry.wk1 e)
  | there {H : Heap M} {y : Nat} {p : M} {e e' : Entry M} :
      HeapLookupUntracked H y e →
      HeapLookupUntracked (.cons H p e') (y + 1) (Entry.wk1 e)
  | thereDummy {H : Heap M} {y : Nat} {e : Entry M} :
      HeapLookupUntracked H y e →
      HeapLookupUntracked (.dummy H) (y + 1) (Entry.wk1 e)

/-- Heap lookup hitting a dummy entry (`_⊢_↦●` in `Graded.Heap.Untyped`). -/
inductive HeapLookupDummy {M : Type} : Heap M → Nat → Prop where
  | here {H : Heap M} :
      HeapLookupDummy (.dummy H) 0
  | there {H : Heap M} {y : Nat} {p : M} {e' : Entry M} :
      HeapLookupDummy H y →
      HeapLookupDummy (.cons H p e') (y + 1)
  | thereDummy {H : Heap M} {y : Nat} :
      HeapLookupDummy H y →
      HeapLookupDummy (.dummy H) (y + 1)

/-- Equality of heaps up to grades (`_~ʰ_` in `Graded.Heap.Untyped`). -/
inductive HeapSameShape {M : Type} : Heap M → Heap M → Prop where
  | nil : HeapSameShape .nil .nil
  | cons {H H' : Heap M} {p q : M} (e : Entry M) :
      HeapSameShape H H' →
      HeapSameShape (.cons H p e) (.cons H' q e)
  | dummy {H H' : Heap M} :
      HeapSameShape H H' →
      HeapSameShape (.dummy H) (.dummy H')

/-- `p`-equivalent heaps (`_~⟨_⟩_` in `Graded.Heap.Untyped` & M3 Section 6):
    heaps coinciding on all entries whose grade is bounded by `p` (`q ≤ p`). -/
inductive HeapEquivAt {M : Type} (𝕄 : Modality M) (p : M) : Heap M → Heap M → Prop where
  | nil : HeapEquivAt 𝕄 p .nil .nil
  | cons {H H' : Heap M} {q : M} {t u : GTerm M} {ρ : Wk} :
      HeapEquivAt 𝕄 p H H' →
      (𝕄.le q p → t = u) →
      HeapEquivAt 𝕄 p (.cons H q ⟨t, ρ⟩) (.cons H' q ⟨u, ρ⟩)
  | dummy {H H' : Heap M} :
      HeapEquivAt 𝕄 p H H' →
      HeapEquivAt 𝕄 p (.dummy H) (.dummy H')

/-- Heap grade bound `H ≤ʰ p` (`_≤ʰ_` in `Graded.Heap.Usage`):
    all grades stored in `H` are bounded by `p`. -/
inductive HeapLe {M : Type} (𝕄 : Modality M) : Heap M → M → Prop where
  | nil {p : M} : HeapLe 𝕄 .nil p
  | cons {H : Heap M} {p q : M} {e : Entry M} :
      HeapLe 𝕄 H p →
      𝕄.le q p →
      HeapLe 𝕄 (.cons H q e) p
  | dummy {H : Heap M} {p : M} :
      HeapLe 𝕄 H p →
      HeapLe 𝕄 (.dummy H) p

namespace HeapSameShape

variable {M : Type}

@[refl] theorem refl : ∀ H : Heap M, HeapSameShape H H
  | .nil => .nil
  | .cons H _ e => .cons e (refl H)
  | .dummy H => .dummy (refl H)

theorem symm {H H' : Heap M} (h : HeapSameShape H H') : HeapSameShape H' H := by
  induction h with
  | nil => exact .nil
  | cons e _ ih => exact .cons e ih
  | dummy _ ih => exact .dummy ih

theorem trans {H₁ H₂ H₃ : Heap M}
    (h₁ : HeapSameShape H₁ H₂) (h₂ : HeapSameShape H₂ H₃) :
    HeapSameShape H₁ H₃ := by
  induction h₁ generalizing H₃ with
  | nil => cases h₂; exact .nil
  | cons e _ ih =>
    cases h₂ with
    | cons _ h₂ => exact .cons e (ih h₂)
  | dummy _ ih =>
    cases h₂ with
    | dummy h₂ => exact .dummy (ih h₂)

theorem lookupUntracked {H H' : Heap M} {y : Nat} {e : Entry M}
    (hshape : HeapSameShape H H') (hlookup : HeapLookupUntracked H y e) :
    HeapLookupUntracked H' y e := by
  induction hlookup generalizing H' with
  | here =>
    cases hshape with
    | cons _ _ => exact .here
  | there _ ih =>
    cases hshape with
    | cons _ hs => exact .there (ih hs)
  | thereDummy _ ih =>
    cases hshape with
    | dummy hs => exact .thereDummy (ih hs)

end HeapSameShape

namespace HeapEquivAt

variable {M : Type} {𝕄 : Modality M} {p : M}

@[refl] theorem refl : ∀ H : Heap M, HeapEquivAt 𝕄 p H H
  | .nil => .nil
  | .cons H _ ⟨_, _⟩ => .cons (refl H) (fun _ ↦ rfl)
  | .dummy H => .dummy (refl H)

theorem symm {H H' : Heap M} (h : HeapEquivAt 𝕄 p H H') : HeapEquivAt 𝕄 p H' H := by
  induction h with
  | nil => exact .nil
  | cons _ heq ih => exact .cons ih (fun hle ↦ (heq hle).symm)
  | dummy _ ih => exact .dummy ih

theorem trans {H₁ H₂ H₃ : Heap M}
    (h₁ : HeapEquivAt 𝕄 p H₁ H₂) (h₂ : HeapEquivAt 𝕄 p H₂ H₃) :
    HeapEquivAt 𝕄 p H₁ H₃ := by
  induction h₁ generalizing H₃ with
  | nil => cases h₂; exact .nil
  | cons _ heq₁ ih =>
    cases h₂ with
    | cons h₂ heq₂ =>
      exact .cons (ih h₂) (fun hle ↦ (heq₁ hle).trans (heq₂ hle))
  | dummy _ ih =>
    cases h₂ with
    | dummy h₂ => exact .dummy (ih h₂)

end HeapEquivAt

namespace HeapLookup

variable {M : Type} {𝕄 : Modality M}

/-- Forgetting the grade update yields an untracked lookup (`↦[]→↦` in M3). -/
theorem toUntracked {H H' : Heap M} {y : Nat} {q : M} {e : Entry M}
    (h : HeapLookup 𝕄 H y q e H') : HeapLookupUntracked H y e := by
  induction h with
  | here _ => exact .here
  | there _ ih => exact .there ih
  | thereDummy _ ih => exact .thereDummy ih

/-- Tracked lookup preserves heap shape (`update-~ʰ` in M3). -/
theorem sameShape {H H' : Heap M} {y : Nat} {q : M} {e : Entry M}
    (h : HeapLookup 𝕄 H y q e H') : HeapSameShape H H' := by
  induction h with
  | here _ => exact .cons _ (.refl _)
  | there _ ih => exact .cons _ ih
  | thereDummy _ ih => exact .dummy ih

/-- Determinism of tracked heap lookup (`↦[]-det` in `Graded.Heap.Untyped.Properties`). -/
theorem det {H H₁ H₂ : Heap M} {y : Nat} {q : M} {e₁ e₂ : Entry M}
    (h₁ : HeapLookup 𝕄 H y q e₁ H₁) (h₂ : HeapLookup 𝕄 H y q e₂ H₂) :
    e₁ = e₂ ∧ H₁ = H₂ := by
  induction h₁ generalizing e₂ H₂ with
  | here hsub₁ =>
    cases h₂ with
    | here hsub₂ =>
      have hr := 𝕄.subEq_unique hsub₁ hsub₂
      subst hr
      exact ⟨rfl, rfl⟩
  | there _ ih =>
    cases h₂ with
    | there h₂ =>
      rcases ih h₂ with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | thereDummy _ ih =>
    cases h₂ with
    | thereDummy h₂ =>
      rcases ih h₂ with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩

end HeapLookup

/-- Every in-bounds pointer `y < H.size` either points to a closure or to a dummy cell
    (`↦⊎↦●` in `Graded.Heap.Untyped.Properties`). -/
theorem lookup_or_dummy {M : Type} (H : Heap M) (y : Nat) (hy : y < H.size) :
    (∃ e : Entry M, HeapLookupUntracked H y e) ∨ HeapLookupDummy H y := by
  induction H generalizing y with
  | nil => simp [Heap.size] at hy
  | cons H p e' ih =>
    cases y with
    | zero => exact Or.inl ⟨Entry.wk1 e', .here⟩
    | succ y =>
      simp only [Heap.size, Nat.add_lt_add_iff_right] at hy
      rcases ih y hy with ⟨e, hl⟩ | hd
      · exact Or.inl ⟨Entry.wk1 e, .there hl⟩
      · exact Or.inr (.there hd)
  | dummy H ih =>
    cases y with
    | zero => exact Or.inr .here
    | succ y =>
      simp only [Heap.size, Nat.add_lt_add_iff_right] at hy
      rcases ih y hy with ⟨e, hl⟩ | hd
      · exact Or.inl ⟨Entry.wk1 e, .thereDummy hl⟩
      · exact Or.inr (.thereDummy hd)

/-- A closed heap (`H.numDummies = 0`) contains no dummy entries
    (`¬erased-heap→¬↦●` in `Graded.Heap.Untyped.Properties`). -/
theorem no_dummy_of_closed {M : Type} {H : Heap M} {y : Nat}
    (hd : HeapLookupDummy H y) (hclosed : H.numDummies = 0) : False := by
  induction hd with
  | here => simp [Heap.numDummies] at hclosed
  | there _ ih => exact ih hclosed
  | thereDummy _ _ => simp [Heap.numDummies] at hclosed

/-- Every in-bounds pointer in a closed heap points to a live closure
    (`¬erased-heap→↦` in `Graded.Heap.Untyped.Properties`). -/
theorem closed_heap_lookup {M : Type} {H : Heap M} (hclosed : H.numDummies = 0)
    (y : Nat) (hy : y < H.size) :
    ∃ e : Entry M, HeapLookupUntracked H y e := by
  rcases lookup_or_dummy H y hy with h | hd
  · exact h
  · exact False.elim (no_dummy_of_closed hd hclosed)

/-! ### Heaps as Substitutions and State Unfolding (`toSubstₕ`, `⦅_⦆`) -/

/-- Interpretation of a heap as a simultaneous substitution (`toSubstₕ` in `Graded.Heap.Untyped`). -/
def toSubstₕ {M : Type} : Heap M → GTerm.GSubst M
  | .nil => GTerm.idSubst
  | .cons H _ ⟨t, ρ⟩ =>
      let σ := toSubstₕ H
      GTerm.consSubst σ (GTerm.subst σ (GTerm.wk ρ t))
  | .dummy H => GTerm.liftSubst (toSubstₕ H)

@[simp] theorem toSubstₕ_erasedHeap {M : Type} :
    ∀ k : Nat, toSubstₕ (erasedHeap (M := M) k) = GTerm.idSubst
  | 0 => rfl
  | k + 1 => by
    simp only [erasedHeap, toSubstₕ, toSubstₕ_erasedHeap k]
    funext x
    exact GTerm.subst_lift_id x

theorem heapSameShape_toSubstₕ {M : Type} {H H' : Heap M}
    (h : HeapSameShape H H') : toSubstₕ H = toSubstₕ H' := by
  induction h with
  | nil => rfl
  | cons e _ ih =>
    cases e
    simp [toSubstₕ, ih]
  | dummy _ ih =>
    simp [toSubstₕ, ih]

/-- Evaluation states of the M3 abstract machine (`State` in `Graded.Heap.Untyped`). -/
structure State (M : Type) where
  heap : Heap M
  head : GTerm M
  env : Wk
  stack : Stack M
  deriving DecidableEq, Repr

/-- Converting a continuation frame back to a graded term (`⦅_⦆ᶜ_` in `Graded.Heap.Untyped`). -/
def unfoldCont {M : Type} : Cont M → GTerm M → GTerm M
  | .appₑ p u ρ, t => .app p t (GTerm.wk ρ u)
  | .fstₑ p, t => .fst p t
  | .sndₑ p, t => .snd p t
  | .prodrecₑ r p q A u ρ, t => .prodrec r p q (GTerm.wk (.lift ρ) A) t (GTerm.wk ρ u)
  | .unitrecₑ p q A u ρ, t => .unitrec p q (GTerm.wk (.lift ρ) A) t (GTerm.wk ρ u)
  | .natrecₑ p q r A z s ρ, t =>
      .natrec p q r (GTerm.wk (.lift ρ) A) (GTerm.wk ρ z) (GTerm.wk ρ s) t
  | .sucₑ, t => .succ t

/-- Converting an evaluation stack back to a graded term (`⦅_⦆ˢ_` in `Graded.Heap.Untyped`). -/
def unfoldStack {M : Type} : Stack M → GTerm M → GTerm M
  | [], t => t
  | c :: S, t => unfoldStack S (unfoldCont c t)

/-- Unfolding a machine state back to a graded term (`⦅_⦆` in `Graded.Heap.Untyped`). -/
def unfoldState {M : Type} (s : State M) : GTerm M :=
  GTerm.subst (toSubstₕ s.heap) (unfoldStack s.stack (GTerm.wk s.env s.head))

/-- Initial machine state (`initial` in `Graded.Heap.Untyped`). -/
def initialState {M : Type} (k : Nat) (t : GTerm M) : State M :=
  ⟨erasedHeap k, t, .id, []⟩

@[simp] theorem unfoldState_initial {M : Type} (k : Nat) (t : GTerm M) :
    unfoldState (initialState k t) = t := by
  simp [unfoldState, initialState, unfoldStack, GTerm.wk_id, toSubstₕ_erasedHeap, GTerm.subst_id]

/-- Weak-head values (`Value` in `Graded.Heap.Untyped`). -/
inductive GValue {M : Type} : GTerm M → Prop where
  | univ : GValue .univ
  | pi {p q A B} : GValue (.pi p q A B)
  | sigma {s p q A B} : GValue (.sigma s p q A B)
  | nat : GValue .nat
  | unit : GValue .unit
  | lam {p t} : GValue (.lam p t)
  | prod {s p t u} : GValue (.prod s p t u)
  | zero : GValue .zero
  | succ {t} : GValue (.succ t)
  | star : GValue .star

/-- Canonical numerals (`Numeral` in `Definition.Untyped`). -/
inductive GNumeral {M : Type} : GTerm M → Prop where
  | zero : GNumeral .zero
  | succ {t} : GNumeral t → GNumeral (.succ t)

namespace GNumeral

variable {M : Type}

theorem of_suck : ∀ k : Nat, GNumeral (GTerm.suck (M := M) k)
  | 0 => .zero
  | k + 1 => .succ (of_suck k)

theorem to_suck {t : GTerm M} (h : GNumeral t) : ∃ k : Nat, t = GTerm.suck k := by
  induction h with
  | zero => exact ⟨0, rfl⟩
  | succ _ ih =>
    rcases ih with ⟨k, rfl⟩
    exact ⟨k + 1, rfl⟩

theorem toValue {t : GTerm M} (h : GNumeral t) : GValue t := by
  cases h with
  | zero => exact .zero
  | succ _ => exact .succ

end GNumeral

/-- Matching head values and continuation frames (`Matching` in `Graded.Heap.Untyped`). -/
inductive Matching {M : Type} : GTerm M → Stack M → Prop where
  | appₑ {p t u ρ S} : Matching (.lam p t) (.appₑ p u ρ :: S)
  | fstₑ {p t u S} : Matching (.prod .strong p t u) (.fstₑ p :: S)
  | sndₑ {p t u S} : Matching (.prod .strong p t u) (.sndₑ p :: S)
  | prodrecₑ {r p q A t u v ρ S} : Matching (.prod .weak p t u) (.prodrecₑ r p q A v ρ :: S)
  | unitrecₑ {p q A u ρ S} : Matching .star (.unitrecₑ p q A u ρ :: S)
  | natrecₑ_zero {p q r A z s ρ S} : Matching .zero (.natrecₑ p q r A z s ρ :: S)
  | natrecₑ_succ {p q r A z s v ρ S} : Matching (.succ v) (.natrecₑ p q r A z s ρ :: S)

/-! ## 3. Heap, Continuation, Stack, and State Usage (`Graded.Heap.Usage`, M3 Section 4.3 & 5) -/

/-- Usage relation for heaps (`_▸ʰ_` in `Graded.Heap.Usage`):
    note that subsumption `sub` is covariant (`γ ▸ʰ H → γ ≤ᶜ δ → δ ▸ʰ H`). -/
inductive HeapUsage {M : Type} (𝕄 : Modality M) : Conₘ M → Heap M → Prop where
  | nil :
      HeapUsage 𝕄 (Conₘ.zero 𝕄) .nil
  | cons {γ δ : Conₘ M} {H : Heap M} {p : M} {t : GTerm M} {ρ : Wk} :
      HeapUsage 𝕄 (Conₘ.add 𝕄 γ (Conₘ.scale 𝕄 p (Conₘ.wk 𝕄 ρ δ))) H →
      Usage 𝕄 δ (Mode.ofGrade 𝕄 p) t →
      HeapUsage 𝕄 (Conₘ.cons γ p) (.cons H p ⟨t, ρ⟩)
  | dummy {γ : Conₘ M} {H : Heap M} :
      HeapUsage 𝕄 γ H →
      HeapUsage 𝕄 (Conₘ.cons γ 𝕄.zero) (.dummy H)
  | sub {γ δ : Conₘ M} {H : Heap M} :
      HeapUsage 𝕄 γ H →
      Conₘ.le 𝕄 γ δ →
      HeapUsage 𝕄 δ H

/-- Usage relation for continuation frames (`_▸ᶜ[_]_` in `Graded.Heap.Usage`).
    Note that `.sucₑ` is intentionally omitted here (as in `Graded/Heap/Usage.agda`)
    so `numStep_not_pres_usage` (`¬▸-⇒ₙ`) holds verbatim; `.sucₑ` is included in
    `ContUsageExt` below for full numeral reduction `↠*`. -/
inductive ContUsage {M : Type} (𝕄 : Modality M) : Conₘ M → Mode → Cont M → Prop where
  | appₑ {γ : Conₘ M} {m : Mode} {p : M} {u : GTerm M} {ρ : Wk} :
      Usage 𝕄 γ (Mode.scale 𝕄 m p) u →
      ContUsage 𝕄 (Conₘ.scale 𝕄 p (Conₘ.wk 𝕄 ρ γ)) m (.appₑ p u ρ)
  | fstₑ {m : Mode} {p : M} :
      𝕄.le (𝕄.mul (Mode.toGrade 𝕄 m) p) (Mode.toGrade 𝕄 m) →
      ContUsage 𝕄 (Conₘ.zero 𝕄) m (.fstₑ p)
  | sndₑ {m : Mode} {p : M} :
      ContUsage 𝕄 (Conₘ.zero 𝕄) m (.sndₑ p)
  | prodrecₑ {γ η : Conₘ M} {m : Mode} {r p q : M} {A u : GTerm M} {ρ : Wk} :
      Usage 𝕄 γ m u →
      Usage 𝕄 (Conₘ.cons η 𝕄.zero) .zeroMode A →
      ContUsage 𝕄 (Conₘ.wk 𝕄 ρ γ) m (.prodrecₑ r p q A u ρ)
  | unitrecₑ {γ η : Conₘ M} {m : Mode} {p q : M} {A u : GTerm M} {ρ : Wk} :
      Usage 𝕄 γ m u →
      Usage 𝕄 (Conₘ.cons η 𝕄.zero) .zeroMode A →
      ContUsage 𝕄 (Conₘ.wk 𝕄 ρ γ) m (.unitrecₑ p q A u ρ)
  | natrecₑ {γ δ θ χ : Conₘ M} {m : Mode} {p q r : M} {A z s : GTerm M} {ρ : Wk} :
      Usage 𝕄 γ m z →
      Usage 𝕄 δ m s →
      Usage 𝕄 (Conₘ.cons θ 𝕄.zero) .zeroMode A →
      Conₘ.le 𝕄 χ γ →
      Conₘ.le 𝕄 χ (Conₘ.add 𝕄 δ (Conₘ.scale 𝕄 r χ)) →
      ContUsage 𝕄 (Conₘ.wk 𝕄 ρ χ) m (.natrecₑ p q r A z s ρ)

/-- Extended continuation usage including `.sucₑ` (`𝟘ᶜ ▸ᶜ⁺[m] sucₑ`) for full numeral evaluation `↠*`. -/
inductive ContUsageExt {M : Type} (𝕄 : Modality M) : Conₘ M → Mode → Cont M → Prop where
  | of_contUsage {γ : Conₘ M} {m : Mode} {c : Cont M} :
      ContUsage 𝕄 γ m c →
      ContUsageExt 𝕄 γ m c
  | sucₑ {m : Mode} :
      ContUsageExt 𝕄 (Conₘ.zero 𝕄) m .sucₑ

/-- Usage relation for evaluation stacks (`_▸ˢ_` in `Graded.Heap.Usage`). -/
inductive StackUsage {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M) :
    Conₘ M → Stack M → Prop where
  | nil :
      StackUsage 𝕄 nr₂ (Conₘ.zero 𝕄) []
  | cons {γ δ : Conₘ M} {c : Cont M} {S : Stack M} :
      ContUsage 𝕄 δ (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ S)) c →
      StackUsage 𝕄 nr₂ γ S →
      StackUsage 𝕄 nr₂ (Conₘ.add 𝕄 γ (Conₘ.scale 𝕄 (Stack.mult 𝕄 nr₂ S) δ)) (c :: S)

/-- Extended stack usage relation allowing `.sucₑ` frames during `↠*`. -/
inductive StackUsageExt {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M) :
    Conₘ M → Stack M → Prop where
  | nil :
      StackUsageExt 𝕄 nr₂ (Conₘ.zero 𝕄) []
  | cons {γ δ : Conₘ M} {c : Cont M} {S : Stack M} :
      ContUsageExt 𝕄 δ (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ S)) c →
      StackUsageExt 𝕄 nr₂ γ S →
      StackUsageExt 𝕄 nr₂ (Conₘ.add 𝕄 γ (Conₘ.scale 𝕄 (Stack.mult 𝕄 nr₂ S) δ)) (c :: S)

/-- Usage relation for evaluation states (`▸_` in `Graded.Heap.Usage`, M3 Section 4.3):
    `StateUsage 𝕄 nr₂ ⟨ H , t , ρ , S ⟩` holds when `γ ▸ʰ H`, `δ ▸[ ⌞ ∣S∣ ⌟ ] t`,
    `η ▸ˢ S`, and `γ ≤ᶜ ∣S∣ ·ᶜ wkConₘ ρ δ +ᶜ η`. -/
inductive StateUsage {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M) (s : State M) : Prop where
  | mk (γ δ η : Conₘ M)
      (heapUsage : HeapUsage 𝕄 γ s.heap)
      (headUsage : Usage 𝕄 δ (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ s.stack)) s.head)
      (stackUsage : StackUsage 𝕄 nr₂ η s.stack)
      (bound : Conₘ.le 𝕄 γ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 (Stack.mult 𝕄 nr₂ s.stack) (Conₘ.wk 𝕄 s.env δ)) η)) :
      StateUsage 𝕄 nr₂ s

/-- Extended state usage relation allowing `.sucₑ` frames on the stack during `↠*`. -/
inductive StateUsageExt {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M) (s : State M) : Prop where
  | mk (γ δ η : Conₘ M)
      (heapUsage : HeapUsage 𝕄 γ s.heap)
      (headUsage : Usage 𝕄 δ (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ s.stack)) s.head)
      (stackUsage : StackUsageExt 𝕄 nr₂ η s.stack)
      (bound : Conₘ.le 𝕄 γ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 (Stack.mult 𝕄 nr₂ s.stack) (Conₘ.wk 𝕄 s.env δ)) η)) :
      StateUsageExt 𝕄 nr₂ s

/-! ### Inversion, Weakening, and Properties of Heap/Stack/State Usage -/

namespace HeapUsage

variable {M : Type} {𝕄 : Modality M}

/-- Inversion of `HeapUsage` on `.cons` (`▸ʰ∙-inv` in `Graded.Heap.Usage.Inversion`). -/
theorem inv_cons {θ : Conₘ M} {H : Heap M} {p : M} {t : GTerm M} {ρ : Wk}
    (h : HeapUsage 𝕄 θ (.cons H p ⟨t, ρ⟩)) :
    ∃ δ η : Conₘ M,
      Usage 𝕄 δ (Mode.ofGrade 𝕄 p) t ∧
      HeapUsage 𝕄 η H ∧
      𝕄.le p (Conₘ.head θ) ∧
      Conₘ.le 𝕄 η (Conₘ.add 𝕄 (Conₘ.tail θ) (Conₘ.scale 𝕄 p (Conₘ.wk 𝕄 ρ δ))) := by
  generalize hH : Heap.cons H p ⟨t, ρ⟩ = H₀ at h
  induction h with
  | nil => nomatch hH
  | @cons γ₀ δ₀ H' p₀ t₀ ρ₀ hH' ht₀ _ =>
    injection hH with hH_eq hp_eq he_eq
    subst hH_eq; subst hp_eq
    injection he_eq with ht_eq hρ_eq
    subst ht_eq; subst hρ_eq
    exact ⟨δ₀, _, ht₀, hH', 𝕄.le_refl p, Conₘ.le_refl 𝕄 _⟩
  | dummy _ _ => nomatch hH
  | sub _ hle ih =>
    rcases ih hH with ⟨δ₀, η₀, ht₀, hH', hp_le, hη_le⟩
    refine ⟨δ₀, η₀, ht₀, hH', 𝕄.le_trans hp_le (Conₘ.head_le_head 𝕄 hle), ?_⟩
    exact Conₘ.le_trans 𝕄 hη_le
      (Conₘ.add_mono 𝕄 (Conₘ.tail_le_tail 𝕄 hle) (Conₘ.le_refl 𝕄 _))

/-- Inversion of `HeapUsage` on `.dummy` (`▸ʰ●-inv` in `Graded.Heap.Usage.Inversion`). -/
theorem inv_dummy {θ : Conₘ M} {H : Heap M}
    (h : HeapUsage 𝕄 θ (.dummy H)) :
    ∃ δ : Conₘ M,
      𝕄.le 𝕄.zero (Conₘ.head θ) ∧
      HeapUsage 𝕄 δ H ∧
      Conₘ.le 𝕄 δ (Conₘ.tail θ) := by
  generalize hH : Heap.dummy H = H₀ at h
  induction h with
  | nil => nomatch hH
  | cons _ _ _ => nomatch hH
  | @dummy γ₀ H' hH' _ =>
    injection hH with hH_eq
    subst hH_eq
    exact ⟨γ₀, 𝕄.le_refl 𝕄.zero, hH', Conₘ.le_refl 𝕄 _⟩
  | sub _ hle ih =>
    rcases ih hH with ⟨δ₀, h0, hH', hδ⟩
    exact ⟨δ₀, 𝕄.le_trans h0 (Conₘ.head_le_head 𝕄 hle), hH',
      Conₘ.le_trans 𝕄 hδ (Conₘ.tail_le_tail 𝕄 hle)⟩

end HeapUsage

namespace ContUsage

variable {M : Type} {𝕄 : Modality M}

/-- Weakening of continuation usage (`wk-▸ᶜ` in `Graded.Heap.Usage.Weakening`). -/
theorem wk (τ : Wk) {γ : Conₘ M} {m : Mode} {c : Cont M}
    (h : ContUsage 𝕄 γ m c) : ContUsage 𝕄 (Conₘ.wk 𝕄 τ γ) m (Cont.wk τ c) := by
  cases h with
  | @appₑ γ₀ m p u ρ hu =>
    rw [Conₘ.wk_scale, Conₘ.wk_comp 𝕄 τ ρ γ₀]
    exact .appₑ hu
  | fstₑ hcond =>
    rw [Conₘ.wk_zero]
    exact .fstₑ hcond
  | sndₑ =>
    rw [Conₘ.wk_zero]
    exact .sndₑ
  | @prodrecₑ γ₀ η₀ m r p q A u ρ hu hA =>
    rw [Conₘ.wk_comp 𝕄 τ ρ γ₀]
    exact .prodrecₑ hu hA
  | @unitrecₑ γ₀ η₀ m p q A u ρ hu hA =>
    rw [Conₘ.wk_comp 𝕄 τ ρ γ₀]
    exact .unitrecₑ hu hA
  | @natrecₑ γ₀ δ₀ θ₀ χ₀ m p q r A z s ρ hz hs hA hχ1 hχ2 =>
    rw [Conₘ.wk_comp 𝕄 τ ρ χ₀]
    exact .natrecₑ hz hs hA hχ1 hχ2

theorem inv_sucₑ {γ : Conₘ M} {m : Mode} (h : ContUsage 𝕄 γ m .sucₑ) : False := by
  nomatch h

end ContUsage

namespace ContUsageExt

variable {M : Type} {𝕄 : Modality M}

theorem wk (τ : Wk) {γ : Conₘ M} {m : Mode} {c : Cont M}
    (h : ContUsageExt 𝕄 γ m c) : ContUsageExt 𝕄 (Conₘ.wk 𝕄 τ γ) m (Cont.wk τ c) := by
  cases h with
  | of_contUsage hc => exact .of_contUsage (hc.wk τ)
  | sucₑ =>
    rw [Conₘ.wk_zero]
    exact .sucₑ

end ContUsageExt

namespace StackUsage

variable {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}

/-- Weakening of stack usage (`wk-▸ˢ` in `Graded.Heap.Usage.Weakening`). -/
theorem wk (τ : Wk) {γ : Conₘ M} {S : Stack M}
    (h : StackUsage 𝕄 nr₂ γ S) : StackUsage 𝕄 nr₂ (Conₘ.wk 𝕄 τ γ) (Stack.wk τ S) := by
  induction h with
  | nil =>
    rw [Conₘ.wk_zero]
    exact .nil
  | @cons γ₀ δ₀ c S hc hS ih =>
    rw [Conₘ.wk_add, Conₘ.wk_scale]
    have hc' := hc.wk τ
    rw [← Stack.mult_wk 𝕄 nr₂ τ S] at hc' ⊢
    exact .cons hc' ih

theorem toExt {γ : Conₘ M} {S : Stack M}
    (h : StackUsage 𝕄 nr₂ γ S) : StackUsageExt 𝕄 nr₂ γ S := by
  induction h with
  | nil => exact .nil
  | cons hc _ ih => exact .cons (.of_contUsage hc) ih

theorem inv_nil {γ : Conₘ M} (h : StackUsage 𝕄 nr₂ γ []) : γ = Conₘ.zero 𝕄 := by
  cases h
  rfl

end StackUsage

namespace StackUsageExt

variable {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}

theorem wk (τ : Wk) {γ : Conₘ M} {S : Stack M}
    (h : StackUsageExt 𝕄 nr₂ γ S) : StackUsageExt 𝕄 nr₂ (Conₘ.wk 𝕄 τ γ) (Stack.wk τ S) := by
  induction h with
  | nil =>
    rw [Conₘ.wk_zero]
    exact .nil
  | @cons γ₀ δ₀ c S hc hS ih =>
    rw [Conₘ.wk_add, Conₘ.wk_scale]
    have hc' := hc.wk τ
    rw [← Stack.mult_wk 𝕄 nr₂ τ S] at hc' ⊢
    exact .cons hc' ih

theorem inv_nil {γ : Conₘ M} (h : StackUsageExt 𝕄 nr₂ γ []) : γ = Conₘ.zero 𝕄 := by
  cases h
  rfl

theorem toStackUsage_nil {γ : Conₘ M} (h : StackUsageExt 𝕄 nr₂ γ []) :
    StackUsage 𝕄 nr₂ γ [] := by
  rw [inv_nil h]
  exact .nil

end StackUsageExt

namespace StateUsage

variable {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}

theorem toExt {s : State M} (h : StateUsage 𝕄 nr₂ s) : StateUsageExt 𝕄 nr₂ s := by
  rcases h with ⟨γ, δ, η, hH, ht, hS, hbound⟩
  exact ⟨γ, δ, η, hH, ht, hS.toExt, hbound⟩

theorem ofExt_empty {H : Heap M} {t : GTerm M} {ρ : Wk}
    (h : StateUsageExt 𝕄 nr₂ ⟨H, t, ρ, []⟩) : StateUsage 𝕄 nr₂ ⟨H, t, ρ, []⟩ := by
  rcases h with ⟨γ, δ, η, hH, ht, hS, hbound⟩
  exact ⟨γ, δ, η, hH, ht, StackUsageExt.toStackUsage_nil hS, hbound⟩

end StateUsage

/-! ### Initial State Usage, Zero Heap Bound, and M3 Lemmas 4.1 & 4.2 -/

/-- `Graded.Heap.Usage.Properties.▸erasedHeap`:
    the dummy-only heap `erasedHeap k` is resourced by `𝟘ᶜ`. -/
theorem erasedHeap_usage {M : Type} (𝕄 : Modality M) :
    ∀ k : Nat, HeapUsage 𝕄 (Conₘ.zero 𝕄) (erasedHeap k)
  | 0 => .nil
  | k + 1 => by
    rw [← Conₘ.cons_zero_zero 𝕄]
    exact .dummy (erasedHeap_usage 𝕄 k)

/-- `Graded.Heap.Usage.Properties.▸initial`:
    if `𝟘ᶜ ▸[ ⌞ 𝟙 ⌟ ] t`, then `initialState k t` is well-resourced. -/
theorem initial_usage {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M) (k : Nat) {t : GTerm M}
    (ht : Usage 𝕄 (Conₘ.zero 𝕄) (Mode.ofGrade 𝕄 𝕄.one) t) :
    StateUsage 𝕄 nr₂ (initialState k t) := by
  refine ⟨Conₘ.zero 𝕄, Conₘ.zero 𝕄, Conₘ.zero 𝕄, erasedHeap_usage 𝕄 k, ht, .nil, ?_⟩
  simp only [initialState, Stack.mult_nil, Conₘ.wk_id, Conₘ.scale_zero, Conₘ.add_zero]
  exact Conₘ.le_refl 𝕄 _

/-- `Graded.Heap.Usage.Properties.𝟘▸H→H≤𝟘`:
    a well-resourced heap under `𝟘ᶜ` has all stored grades bounded by `𝟘`. -/
theorem zero_usage_heap_le_zero {M : Type} (𝕄 : Modality M) {H : Heap M}
    (hH : HeapUsage 𝕄 (Conₘ.zero 𝕄) H) : HeapLe 𝕄 H 𝕄.zero := by
  induction H with
  | nil => exact .nil
  | cons H p e ih =>
    cases e with
    | mk t ρ =>
      rcases HeapUsage.inv_cons hH with ⟨δ, η, _, hH', hp0, hη⟩
      have htail : Conₘ.tail (Conₘ.zero 𝕄) = Conₘ.zero 𝕄 := rfl
      have hhead : Conₘ.head (Conₘ.zero 𝕄) = 𝕄.zero := rfl
      rw [hhead] at hp0
      rw [htail, Conₘ.zero_add] at hη
      have hp_scale : Conₘ.le 𝕄 (Conₘ.scale 𝕄 p (Conₘ.wk 𝕄 ρ δ)) (Conₘ.zero 𝕄) := by
        have h1 := Conₘ.scale_mono 𝕄 hp0 (Conₘ.le_refl 𝕄 (Conₘ.wk 𝕄 ρ δ))
        rw [Conₘ.zero_scale] at h1
        exact h1
      have hη0 : Conₘ.le 𝕄 η (Conₘ.zero 𝕄) := Conₘ.le_trans 𝕄 hη hp_scale
      exact .cons (ih (.sub hH' hη0)) hp0
  | dummy H ih =>
    rcases HeapUsage.inv_dummy hH with ⟨δ, _, hH', hδ⟩
    exact .dummy (ih (.sub hH' hδ))

/-- `Graded.Heap.Usage.Properties.▸-heapLookup`:
    looking up `q` copies of pointer `y` in a well-resourced heap `γ ▸ʰ H` when
    `γ y ≤ r + q` yields a well-resourced term `δ ▸[ ⌞ q ⌟ ] t` and an updated
    well-resourced heap `(γ , y ≔ r) +ᶜ q ·ᶜ wkConₘ ρ δ ▸ʰ H'`. -/
theorem heapLookup_usage {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    {H H' : Heap M} {y : Nat} {q r : M} {t : GTerm M} {ρ : Wk} {γ : Conₘ M}
    (hlookup : HeapLookup 𝕄 H y q ⟨t, ρ⟩ H')
    (hH : HeapUsage 𝕄 γ H)
    (hy : 𝕄.le (γ y) (𝕄.add r q)) :
    ∃ δ : Conₘ M,
      Usage 𝕄 δ (Mode.ofGrade 𝕄 q) t ∧
      HeapUsage 𝕄 (Conₘ.add 𝕄 (Conₘ.update γ y r) (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δ))) H' := by
  generalize he : (⟨t, ρ⟩ : Entry M) = e₀ at hlookup
  induction hlookup generalizing γ r t ρ with
  | @here H₀ p' q₀ r' e₁ hsub =>
    cases e₁ with
    | mk t₀ ρ₀ =>
      injection he with ht_eq hρ_eq
      subst ht_eq; subst hρ_eq
      rcases HeapUsage.inv_cons hH with ⟨δ, η, ht₀, hH₀, hp'_le, hη_le⟩
      have hp'_rq : 𝕄.le p' (𝕄.add r q₀) := 𝕄.le_trans hp'_le hy
      have hp'_q : p' = 𝕄.zero → q₀ = 𝕄.zero :=
        fun hp0 ↦ (Usage.zero_imp_of_le_add hw hp'_rq hp0).2
      have hp'_r' : p' = 𝕄.zero → r' = 𝕄.zero :=
        fun hp0 ↦ (Usage.zero_imp_of_le_add hw hsub.1 hp0).1
      let δq := Conₘ.scale 𝕄 (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 q₀)) δ
      let δr' := Conₘ.scale 𝕄 (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 r')) δ
      have ht_q : Usage 𝕄 δq (Mode.ofGrade 𝕄 q₀) t := Usage.ofGrade_scale_self ht₀ hp'_q
      have ht_r' : Usage 𝕄 δr' (Mode.ofGrade 𝕄 r') t := Usage.ofGrade_scale_self ht₀ hp'_r'
      have hscale_q : Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ δq) = Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ δ) := by
        rw [Conₘ.wk_scale, ← Conₘ.scale_assoc, Mode.mul_toGrade_ofGrade]
      have hscale_r' : Conₘ.scale 𝕄 r' (Conₘ.wk 𝕄 ρ₀ δr') = Conₘ.scale 𝕄 r' (Conₘ.wk 𝕄 ρ₀ δ) := by
        rw [Conₘ.wk_scale, ← Conₘ.scale_assoc, Mode.mul_toGrade_ofGrade]
      have hη_bound : Conₘ.le 𝕄 η
          (Conₘ.add 𝕄 (Conₘ.add 𝕄 (Conₘ.tail γ) (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ δ)))
            (Conₘ.scale 𝕄 r' (Conₘ.wk 𝕄 ρ₀ δr'))) := by
        rw [hscale_r']
        have h1 : Conₘ.le 𝕄 (Conₘ.scale 𝕄 p' (Conₘ.wk 𝕄 ρ₀ δ))
            (Conₘ.scale 𝕄 (𝕄.add r' q₀) (Conₘ.wk 𝕄 ρ₀ δ)) :=
          Conₘ.scale_mono 𝕄 hsub.1 (Conₘ.le_refl 𝕄 _)
        have h2 : Conₘ.add 𝕄 (Conₘ.tail γ) (Conₘ.scale 𝕄 (𝕄.add r' q₀) (Conₘ.wk 𝕄 ρ₀ δ)) =
            Conₘ.add 𝕄 (Conₘ.add 𝕄 (Conₘ.tail γ) (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ δ)))
              (Conₘ.scale 𝕄 r' (Conₘ.wk 𝕄 ρ₀ δ)) := by
          rw [𝕄.add_comm r' q₀, Conₘ.add_scale_distrib, ← Conₘ.add_assoc]
        rw [← h2]
        exact Conₘ.le_trans 𝕄 hη_le (Conₘ.add_mono 𝕄 (Conₘ.le_refl 𝕄 _) h1)
      have hH₀' : HeapUsage 𝕄
          (Conₘ.cons (Conₘ.add 𝕄 (Conₘ.tail γ) (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ δ))) r')
          (.cons H₀ r' ⟨t, ρ₀⟩) :=
        .cons (.sub hH₀ hη_bound) ht_r'
      have hr'_le_r : 𝕄.le r' r := hsub.2 r hp'_rq
      have hfinal_eq : Conₘ.add 𝕄 (Conₘ.update γ 0 r) (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 (.step ρ₀) δq)) =
          Conₘ.cons (Conₘ.add 𝕄 (Conₘ.tail γ) (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ δ))) r := by
        funext z
        cases z with
        | zero => simp [Conₘ.add, Conₘ.update, Conₘ.scale, Conₘ.wk, Conₘ.cons, 𝕄.mul_zero, 𝕄.add_zero]
        | succ z =>
          change 𝕄.add (Conₘ.tail γ z) (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ δq) z) = _
          rw [hscale_q]
          rfl
      refine ⟨δq, ht_q, ?_⟩
      rw [hfinal_eq]
      exact .sub hH₀' (Conₘ.cons_le_cons 𝕄 (Conₘ.le_refl 𝕄 _) hr'_le_r)
  | @there H₀ H₀' y₀ p' q₀ e₁ e' d ih =>
    cases e₁ with
    | mk t₀ ρ₀ =>
      cases e' with
      | mk u₀ ρ_u =>
        injection he with ht_eq hρ_eq
        subst ht_eq; subst hρ_eq
        rcases HeapUsage.inv_cons hH with ⟨δu, η, hu₀, hH₀, hp'_le, hη_le⟩
        let s_y := (Conₘ.scale 𝕄 p' (Conₘ.wk 𝕄 ρ_u δu)) y₀
        have hη_y : 𝕄.le (η y₀) (𝕄.add (𝕄.add s_y r) q₀) := by
          have h1 : 𝕄.le (η y₀) (𝕄.add (γ (y₀ + 1)) s_y) := hη_le y₀
          have h2 : 𝕄.le (𝕄.add (γ (y₀ + 1)) s_y) (𝕄.add (𝕄.add r q₀) s_y) :=
            𝕄.add_mono hy (𝕄.le_refl s_y)
          have h3 : 𝕄.add (𝕄.add r q₀) s_y = 𝕄.add (𝕄.add s_y r) q₀ := by
            rw [𝕄.add_assoc, 𝕄.add_comm q₀ s_y, ← 𝕄.add_assoc, 𝕄.add_comm r s_y]
          rw [h3] at h2
          exact 𝕄.le_trans h1 h2
        rcases ih hH₀ hη_y rfl with ⟨δ', ht₀, hH₀'⟩
        refine ⟨δ', ht₀, ?_⟩
        have hupd_le : Conₘ.le 𝕄
            (Conₘ.add 𝕄 (Conₘ.update η y₀ (𝕄.add s_y r)) (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ δ')))
            (Conₘ.add 𝕄 (Conₘ.add 𝕄 (Conₘ.update (Conₘ.tail γ) y₀ r)
              (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ δ')))
              (Conₘ.scale 𝕄 p' (Conₘ.wk 𝕄 ρ_u δu))) := by
          intro z
          by_cases hz : z = y₀
          · rw [hz]
            simp only [Conₘ.add, Conₘ.update, ↓reduceIte]
            have heq : 𝕄.add (𝕄.add s_y r) (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ δ') y₀) =
                𝕄.add (𝕄.add r (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ δ') y₀)) s_y := by
              rw [𝕄.add_comm s_y r, 𝕄.add_assoc, 𝕄.add_comm s_y _, ← 𝕄.add_assoc]
            rw [heq]
            exact 𝕄.le_refl _
          · simp only [Conₘ.add, Conₘ.update, hz, ↓reduceIte]
            have h_z : 𝕄.le (η z) (𝕄.add (Conₘ.tail γ z) (Conₘ.scale 𝕄 p' (Conₘ.wk 𝕄 ρ_u δu) z)) := hη_le z
            have hmono := 𝕄.add_mono h_z (𝕄.le_refl (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ δ') z))
            have heq : 𝕄.add (𝕄.add (Conₘ.tail γ z) (Conₘ.scale 𝕄 p' (Conₘ.wk 𝕄 ρ_u δu) z))
                (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ δ') z) =
                𝕄.add (𝕄.add (Conₘ.tail γ z) (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ δ') z))
                  (Conₘ.scale 𝕄 p' (Conₘ.wk 𝕄 ρ_u δu) z) := by
              rw [𝕄.add_assoc, 𝕄.add_comm (Conₘ.scale 𝕄 p' _ z) _, ← 𝕄.add_assoc]
            rw [heq] at hmono
            exact hmono
        have hcons : HeapUsage 𝕄
            (Conₘ.cons (Conₘ.add 𝕄 (Conₘ.update (Conₘ.tail γ) y₀ r)
              (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ δ'))) p')
            (.cons H₀' p' ⟨u₀, ρ_u⟩) :=
          .cons (.sub hH₀' hupd_le) hu₀
        have hfinal : Conₘ.le 𝕄
            (Conₘ.cons (Conₘ.add 𝕄 (Conₘ.update (Conₘ.tail γ) y₀ r)
              (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ δ'))) p')
            (Conₘ.add 𝕄 (Conₘ.update γ (y₀ + 1) r)
              (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 (.step ρ₀) δ'))) := by
          intro z
          cases z with
          | zero =>
            simp only [Conₘ.cons, Conₘ.add, Conₘ.update, Conₘ.scale, Conₘ.wk, 𝕄.mul_zero, 𝕄.add_zero]
            exact hp'_le
          | succ z =>
            by_cases hz : z = y₀ <;>
              simp [Conₘ.cons, Conₘ.add, Conₘ.update, Conₘ.tail, Conₘ.scale, Conₘ.wk, hz, 𝕄.le_refl]
        exact .sub hcons hfinal
  | @thereDummy H₀ H₀' y₀ q₀ e₁ d ih =>
    cases e₁ with
    | mk t₀ ρ₀ =>
      injection he with ht_eq hρ_eq
      subst ht_eq; subst hρ_eq
      rcases HeapUsage.inv_dummy hH with ⟨δ₀, h0_le, hH₀, hδ_le⟩
      have hδ_y : 𝕄.le (δ₀ y₀) (𝕄.add r q₀) := 𝕄.le_trans (hδ_le y₀) hy
      rcases ih hH₀ hδ_y rfl with ⟨η', ht₀, hH₀'⟩
      refine ⟨η', ht₀, ?_⟩
      have hdum : HeapUsage 𝕄
          (Conₘ.cons (Conₘ.add 𝕄 (Conₘ.update δ₀ y₀ r) (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ η'))) 𝕄.zero)
          (.dummy H₀') := .dummy hH₀'
      have hfinal : Conₘ.le 𝕄
          (Conₘ.cons (Conₘ.add 𝕄 (Conₘ.update δ₀ y₀ r) (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 ρ₀ η'))) 𝕄.zero)
          (Conₘ.add 𝕄 (Conₘ.update γ (y₀ + 1) r) (Conₘ.scale 𝕄 q₀ (Conₘ.wk 𝕄 (.step ρ₀) η'))) := by
        intro z
        cases z with
        | zero =>
          simp only [Conₘ.cons, Conₘ.add, Conₘ.update, Conₘ.scale, Conₘ.wk, 𝕄.mul_zero, 𝕄.add_zero]
          exact h0_le
        | succ z =>
          have hupd_z : 𝕄.le (Conₘ.update δ₀ y₀ r z) (Conₘ.update γ (y₀ + 1) r (z + 1)) := by
            by_cases hz : z = y₀
            · simp [Conₘ.update, hz, 𝕄.le_refl]
            · simp [Conₘ.update, hz]
              exact hδ_le z
          exact 𝕄.add_mono hupd_z (𝕄.le_refl _)
      exact .sub hdum hfinal

/-- **M3 Lemma 4.1a (`↦→↦[]` in `Graded.Heap.Usage.Properties`)**:
    under `SupportsSubtraction`, any untracked lookup `H ⊢ y ↦ e` in a well-resourced
    heap `γ ▸ʰ H` with `γ y ≤ p + q` succeeds as a tracked lookup `H ⊢ y ↦[q] e ⨾ H'`. -/
theorem lookup_succeeds_of_untracked {M : Type} {𝕄 : Modality M}
    (hsub : 𝕄.SupportsSubtraction) {H : Heap M} {y : Nat} {p q : M} {e : Entry M} {γ : Conₘ M}
    (hl : HeapLookupUntracked H y e) (hH : HeapUsage 𝕄 γ H)
    (hy : 𝕄.le (γ y) (𝕄.add p q)) :
    ∃ H' : Heap M, HeapLookup 𝕄 H y q e H' := by
  induction hl generalizing γ p with
  | @here H₀ p' e₀ =>
    cases e₀ with
    | mk t₀ ρ₀ =>
      rcases HeapUsage.inv_cons hH with ⟨_, _, _, _, hp'_le, _⟩
      rcases hsub (𝕄.le_trans hp'_le hy) with ⟨r', hr'⟩
      exact ⟨.cons H₀ r' ⟨t₀, ρ₀⟩, .here hr'⟩
  | @there H₀ y₀ r' e₀ e' d ih =>
    cases e' with
    | mk u₀ ρ_u =>
      rcases HeapUsage.inv_cons hH with ⟨δu, η, _, hH₀, _, hη_le⟩
      let s_y := (Conₘ.scale 𝕄 r' (Conₘ.wk 𝕄 ρ_u δu)) y₀
      have hη_y : 𝕄.le (η y₀) (𝕄.add (𝕄.add p s_y) q) := by
        have h1 : 𝕄.le (η y₀) (𝕄.add (γ (y₀ + 1)) s_y) := hη_le y₀
        have h2 : 𝕄.le (𝕄.add (γ (y₀ + 1)) s_y) (𝕄.add (𝕄.add p q) s_y) :=
          𝕄.add_mono hy (𝕄.le_refl s_y)
        have h3 : 𝕄.add (𝕄.add p q) s_y = 𝕄.add (𝕄.add p s_y) q := by
          rw [𝕄.add_assoc, 𝕄.add_comm q s_y, ← 𝕄.add_assoc]
        rw [h3] at h2
        exact 𝕄.le_trans h1 h2
      rcases ih hH₀ hη_y with ⟨H₀', d'⟩
      exact ⟨.cons H₀' r' ⟨u₀, ρ_u⟩, .there d'⟩
  | @thereDummy H₀ y₀ e₀ d ih =>
    rcases HeapUsage.inv_dummy hH with ⟨δ₀, _, hH₀, hδ_le⟩
    rcases ih hH₀ (𝕄.le_trans (hδ_le y₀) hy) with ⟨H₀', d'⟩
    exact ⟨.dummy H₀', .thereDummy d'⟩

/-- Variable state inversion (`▸ₛ-var-inv′` in `Graded.Heap.Usage.Inversion`):
    if `δ ▸[ ⌞ q ⌟ ] .var x` and `γ ≤ᶜ q ·ᶜ wkConₘ ρ δ +ᶜ η`, then `γ (wkVar ρ x) ≤ q + η (wkVar ρ x)`. -/
theorem var_state_bound {M : Type} {𝕄 : Modality M} {γ δ η : Conₘ M}
    {q : M} {x : Nat} {ρ : Wk}
    (ht : Usage 𝕄 δ (Mode.ofGrade 𝕄 q) (.var x))
    (hbound : Conₘ.le 𝕄 γ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δ)) η)) :
    𝕄.le (γ (wkVar ρ x)) (𝕄.add q (η (wkVar ρ x))) := by
  have hvar := Usage.inv_var ht
  have hwk := Conₘ.wk_mono 𝕄 ρ hvar
  rw [Conₘ.wk_single] at hwk
  have hscale := Conₘ.scale_mono_right 𝕄 q hwk
  rw [Conₘ.scale_single, Mode.mul_toGrade_ofGrade] at hscale
  have hbound_x := (Conₘ.le_trans 𝕄 hbound (Conₘ.add_mono 𝕄 hscale (Conₘ.le_refl 𝕄 η))) (wkVar ρ x)
  simpa only [Conₘ.add, Conₘ.single, ↓reduceIte] using hbound_x

/-- **M3 Lemma 4.1 (`▸↦→↦[]` in `Graded.Heap.Usage.Properties`)**:
    under `SupportsSubtraction`, if a well-resourced state `⟨ H , .var x , ρ , S ⟩` has
    an untracked lookup `H ⊢ wkVar ρ x ↦ e`, then the tracked lookup
    `H ⊢ wkVar ρ x ↦[ ∣S∣ ] e ⨾ H'` succeeds. -/
theorem state_lookup_succeeds {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hsub : 𝕄.SupportsSubtraction) {H : Heap M} {x : Nat} {ρ : Wk} {S : Stack M} {e : Entry M}
    (hl : HeapLookupUntracked H (wkVar ρ x) e)
    (hs : StateUsage 𝕄 nr₂ ⟨H, .var x, ρ, S⟩) :
    ∃ H' : Heap M, HeapLookup 𝕄 H (wkVar ρ x) (Stack.mult 𝕄 nr₂ S) e H' := by
  rcases hs with ⟨γ, δ, η, hH, ht, _, hbound⟩
  have hvar := var_state_bound ht hbound
  rw [𝕄.add_comm] at hvar
  exact lookup_succeeds_of_untracked hsub hl hH hvar

/-- **M3 Lemma 4.1 for `StateUsageExt`**. -/
theorem stateExt_lookup_succeeds {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hsub : 𝕄.SupportsSubtraction) {H : Heap M} {x : Nat} {ρ : Wk} {S : Stack M} {e : Entry M}
    (hl : HeapLookupUntracked H (wkVar ρ x) e)
    (hs : StateUsageExt 𝕄 nr₂ ⟨H, .var x, ρ, S⟩) :
    ∃ H' : Heap M, HeapLookup 𝕄 H (wkVar ρ x) (Stack.mult 𝕄 nr₂ S) e H' := by
  rcases hs with ⟨γ, δ, η, hH, ht, _, hbound⟩
  have hvar := var_state_bound ht hbound
  rw [𝕄.add_comm] at hvar
  exact lookup_succeeds_of_untracked hsub hl hH hvar

/-- **M3 Lemma 4.1 for Closed States (`▸↦[]-closed` in `Graded.Heap.Usage.Properties`)**:
    in a closed well-resourced state (`H.numDummies = 0` and `wkVar ρ x < H.size`),
    tracked variable lookup always succeeds. -/
theorem lookup_succeeds_closed {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hsub : 𝕄.SupportsSubtraction) {H : Heap M} {x : Nat} {ρ : Wk} {S : Stack M}
    (hclosed : H.numDummies = 0) (hin : wkVar ρ x < H.size)
    (hs : StateUsage 𝕄 nr₂ ⟨H, .var x, ρ, S⟩) :
    ∃ (e : Entry M) (H' : Heap M),
      HeapLookup 𝕄 H (wkVar ρ x) (Stack.mult 𝕄 nr₂ S) e H' := by
  rcases closed_heap_lookup hclosed (wkVar ρ x) hin with ⟨e, hl⟩
  rcases state_lookup_succeeds hsub hl hs with ⟨H', hl'⟩
  exact ⟨e, H', hl'⟩

/-- **M3 Lemma 4.2a (`▸H●` in `Graded.Heap.Usage.Properties`)**:
    under `HasWellBehavedZero`, if pointer `y` points to a dummy entry `H ⊢ y ↦●` in
    a well-resourced heap `γ ▸ʰ H`, then `γ y = 𝟘`. -/
theorem lookup_dummy_usage_zero {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    {H : Heap M} {y : Nat} {γ : Conₘ M}
    (hd : HeapLookupDummy H y) (hH : HeapUsage 𝕄 γ H) : γ y = 𝕄.zero := by
  induction hd generalizing γ with
  | here =>
    rcases HeapUsage.inv_dummy hH with ⟨_, h0_le, _, _⟩
    exact hw.zero_le_eq_zero h0_le
  | @there H₀ y₀ p e' d ih =>
    cases e' with
    | mk u₀ ρ_u =>
      rcases HeapUsage.inv_cons hH with ⟨δu, η, _, hH₀, _, hη_le⟩
      have hη0 := ih hH₀
      have hle_y := hη_le y₀
      rw [hη0] at hle_y
      exact hw.add_positive_left (hw.zero_le_eq_zero hle_y)
  | @thereDummy H₀ y₀ d ih =>
    rcases HeapUsage.inv_dummy hH with ⟨δ₀, _, hH₀, hδ_le⟩
    have hδ0 := ih hH₀
    have hle_y := hδ_le y₀
    rw [hδ0] at hle_y
    exact hw.zero_le_eq_zero hle_y

/-- **M3 Lemma 4.2 (`▸s●` in `Graded.Heap.Usage.Properties`)**:
    under `HasWellBehavedZero`, if a well-resourced state `⟨ H , .var x , ρ , S ⟩`
    has a variable pointing to a dummy heap entry `H ⊢ wkVar ρ x ↦●`, then the stack
    multiplicity is `𝟘` (`Stack.mult 𝕄 nr₂ S = 𝕄.zero`). -/
theorem lookup_dummy_stack_zero {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) {H : Heap M} {x : Nat} {ρ : Wk} {S : Stack M}
    (hd : HeapLookupDummy H (wkVar ρ x))
    (hs : StateUsage 𝕄 nr₂ ⟨H, .var x, ρ, S⟩) :
    Stack.mult 𝕄 nr₂ S = 𝕄.zero := by
  rcases hs with ⟨γ, δ, η, hH, ht, _, hbound⟩
  have hγ0 := lookup_dummy_usage_zero hw hd hH
  have hvar := var_state_bound ht hbound
  rw [hγ0] at hvar
  exact hw.add_positive_left (hw.zero_le_eq_zero hvar)

/-! ## 4. Heap Machine Reduction and Usage Preservation (`Graded.Heap.Reduction`, M3 Theorem 4.3) -/

/-- Head-eliminator reduction steps pushing a continuation frame onto the stack
    (`_⇒ₑ_` in `Graded.Heap.Reduction`, M3 Section 4.2). -/
inductive ElimStep {M : Type} : State M → State M → Prop where
  | appₕ {H : Heap M} {p : M} {t u : GTerm M} {ρ : Wk} {S : Stack M} :
      ElimStep ⟨H, .app p t u, ρ, S⟩ ⟨H, t, ρ, .appₑ p u ρ :: S⟩
  | fstₕ {H : Heap M} {p : M} {t : GTerm M} {ρ : Wk} {S : Stack M} :
      ElimStep ⟨H, .fst p t, ρ, S⟩ ⟨H, t, ρ, .fstₑ p :: S⟩
  | sndₕ {H : Heap M} {p : M} {t : GTerm M} {ρ : Wk} {S : Stack M} :
      ElimStep ⟨H, .snd p t, ρ, S⟩ ⟨H, t, ρ, .sndₑ p :: S⟩
  | prodrecₕ {H : Heap M} {r p q : M} {A t u : GTerm M} {ρ : Wk} {S : Stack M} :
      ElimStep ⟨H, .prodrec r p q A t u, ρ, S⟩ ⟨H, t, ρ, .prodrecₑ r p q A u ρ :: S⟩
  | unitrecₕ {H : Heap M} {p q : M} {A t u : GTerm M} {ρ : Wk} {S : Stack M} :
      ElimStep ⟨H, .unitrec p q A t u, ρ, S⟩ ⟨H, t, ρ, .unitrecₑ p q A u ρ :: S⟩
  | natrecₕ {H : Heap M} {p q r : M} {A z s t : GTerm M} {ρ : Wk} {S : Stack M} :
      ElimStep ⟨H, .natrec p q r A z s t, ρ, S⟩ ⟨H, t, ρ, .natrecₑ p q r A z s ρ :: S⟩

/-- Eliminator or tracked variable lookup step (`_⇾ₑ_` in `Graded.Heap.Reduction`). -/
inductive TrackElimStep {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M) :
    State M → State M → Prop where
  | var {H H' : Heap M} {x : Nat} {t : GTerm M} {ρ ρ' : Wk} {S : Stack M} :
      HeapLookup 𝕄 H (wkVar ρ x) (Stack.mult 𝕄 nr₂ S) ⟨t, ρ'⟩ H' →
      TrackElimStep 𝕄 nr₂ ⟨H, .var x, ρ, S⟩ ⟨H', t, ρ', S⟩
  | elim {s₁ s₂ : State M} :
      ElimStep s₁ s₂ →
      TrackElimStep 𝕄 nr₂ s₁ s₂

/-- Eliminator or untracked variable lookup step (`_⇢ₑ_` in `Graded.Heap.Reduction`). -/
inductive UntrackElimStep {M : Type} : State M → State M → Prop where
  | var {H : Heap M} {x : Nat} {t : GTerm M} {ρ ρ' : Wk} {S : Stack M} :
      HeapLookupUntracked H (wkVar ρ x) ⟨t, ρ'⟩ →
      UntrackElimStep ⟨H, .var x, ρ, S⟩ ⟨H, t, ρ', S⟩
  | elim {s₁ s₂ : State M} :
      ElimStep s₁ s₂ →
      UntrackElimStep s₁ s₂

/-- Value-continuation β-reduction steps (`_⇒ᵥ_` in `Graded.Heap.Reduction`, M3 Section 4.2).
    In `prodWeakₕ` and `sucₕ`, the two new bindings are allocated on the heap `H` with their
    exact M3 multiplicities (`q' · r · p` and `q' · r` for `prodWeakₕ`, and `q' · p'` and
    `q' · r` for `sucₕ`), and the curried branch `u` or `s` is applied to `.var 1` and `.var 0`. -/
inductive ValStep {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M) :
    State M → State M → Prop where
  | lamₕ {H : Heap M} {p : M} {t u : GTerm M} {ρ ρ' : Wk} {S : Stack M} :
      ValStep 𝕄 nr₂
        ⟨H, .lam p t, ρ, .appₑ p u ρ' :: S⟩
        ⟨.cons H (𝕄.mul (Stack.mult 𝕄 nr₂ S) p) ⟨u, ρ'⟩, t, .lift ρ, Stack.wk1 S⟩
  | prodStrongₕ₁ {H : Heap M} {p : M} {t₁ t₂ : GTerm M} {ρ : Wk} {S : Stack M} :
      ValStep 𝕄 nr₂
        ⟨H, .prod .strong p t₁ t₂, ρ, .fstₑ p :: S⟩
        ⟨H, t₁, ρ, S⟩
  | prodStrongₕ₂ {H : Heap M} {p : M} {t₁ t₂ : GTerm M} {ρ : Wk} {S : Stack M} :
      ValStep 𝕄 nr₂
        ⟨H, .prod .strong p t₁ t₂, ρ, .sndₑ p :: S⟩
        ⟨H, t₂, ρ, S⟩
  | prodWeakₕ {H : Heap M} {r p q : M} {t₁ t₂ A u : GTerm M} {ρ ρ' : Wk} {S : Stack M} :
      ValStep 𝕄 nr₂
        ⟨H, .prod .weak p t₁ t₂, ρ, .prodrecₑ r p q A u ρ' :: S⟩
        ⟨.cons (.cons H (𝕄.mul (𝕄.mul (Stack.mult 𝕄 nr₂ S) r) p) ⟨t₁, ρ⟩)
            (𝕄.mul (Stack.mult 𝕄 nr₂ S) r) ⟨t₂, .step ρ⟩,
          .app r (.app (𝕄.mul r p) (GTerm.wk (.step (.step .id)) u) (.var 1)) (.var 0),
          .lift (.lift ρ'), Stack.wk2 S⟩
  | zeroₕ {H : Heap M} {p q r : M} {A z s : GTerm M} {ρ ρ' : Wk} {S : Stack M} :
      ValStep 𝕄 nr₂
        ⟨H, .zero, ρ, .natrecₑ p q r A z s ρ' :: S⟩
        ⟨H, z, ρ', S⟩
  | sucₕ {H : Heap M} {p q r : M} {t A z s : GTerm M} {ρ ρ' : Wk} {S : Stack M} :
      ValStep 𝕄 nr₂
        ⟨H, .succ t, ρ, .natrecₑ p q r A z s ρ' :: S⟩
        ⟨.cons (.cons H (𝕄.mul (Stack.mult 𝕄 nr₂ S) (nr₂ p r)) ⟨t, ρ⟩)
            (𝕄.mul (Stack.mult 𝕄 nr₂ S) r)
            ⟨.natrec p q r (GTerm.wk (.lift (.step .id)) A) (GTerm.wk1 z) (GTerm.wk1 s) (.var 0),
              .lift ρ'⟩,
          .app r (.app p (GTerm.wk (.step (.step .id)) s) (.var 1)) (.var 0),
          .lift (.lift ρ'), Stack.wk2 S⟩
  | starWeakₕ {H : Heap M} {p q : M} {A u : GTerm M} {ρ ρ' : Wk} {S : Stack M} :
      ValStep 𝕄 nr₂
        ⟨H, .star, ρ, .unitrecₑ p q A u ρ' :: S⟩
        ⟨H, u, ρ', S⟩

/-- Under-successor reduction steps for full numeral evaluation (`_⇒ₙ_` in `Graded.Heap.Reduction`). -/
inductive NumStep {M : Type} : State M → State M → Prop where
  | sucₕ {H : Heap M} {t : GTerm M} {ρ : Wk} {ℓ : Nat} :
      ¬ GNumeral t →
      NumStep ⟨H, .succ t, ρ, Stack.sucs ℓ⟩ ⟨H, t, ρ, .sucₑ :: Stack.sucs ℓ⟩
  | numₕ {H : Heap M} {t : GTerm M} {ρ : Wk} {S : Stack M} :
      GNumeral t →
      NumStep ⟨H, t, ρ, .sucₑ :: S⟩ ⟨H, .succ t, ρ, S⟩

/-- Call-by-name WHNF heap evaluation with resource tracking (`_⇾_` in `Graded.Heap.Reduction`). -/
inductive HeapStep {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M) :
    State M → State M → Prop where
  | elimStep {s₁ s₂ : State M} :
      TrackElimStep 𝕄 nr₂ s₁ s₂ →
      HeapStep 𝕄 nr₂ s₁ s₂
  | valStep {s₁ s₂ : State M} :
      ValStep 𝕄 nr₂ s₁ s₂ →
      HeapStep 𝕄 nr₂ s₁ s₂

/-- Call-by-name WHNF heap evaluation without resource tracking (`_⇢_` in `Graded.Heap.Reduction`). -/
inductive HeapStepUntracked {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M) :
    State M → State M → Prop where
  | elimStep {s₁ s₂ : State M} :
      UntrackElimStep s₁ s₂ →
      HeapStepUntracked 𝕄 nr₂ s₁ s₂
  | valStep {s₁ s₂ : State M} :
      ValStep 𝕄 nr₂ s₁ s₂ →
      HeapStepUntracked 𝕄 nr₂ s₁ s₂

/-- Call-by-name full numeral heap evaluation with resource tracking (`_↠_` in `Graded.Heap.Reduction`). -/
inductive HeapNumStep {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M) :
    State M → State M → Prop where
  | elimStep {s₁ s₂ : State M} :
      TrackElimStep 𝕄 nr₂ s₁ s₂ →
      HeapNumStep 𝕄 nr₂ s₁ s₂
  | valStep {s₁ s₂ : State M} :
      ValStep 𝕄 nr₂ s₁ s₂ →
      HeapNumStep 𝕄 nr₂ s₁ s₂
  | numStep {s₁ s₂ : State M} :
      NumStep s₁ s₂ →
      HeapNumStep 𝕄 nr₂ s₁ s₂

/-- Reflexive-transitive closure of `HeapStep` (`_⇾*_`). -/
inductive HeapStar {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M) :
    State M → State M → Prop where
  | refl (s : State M) : HeapStar 𝕄 nr₂ s s
  | step {s₁ s₂ s₃ : State M} :
      HeapStep 𝕄 nr₂ s₁ s₂ → HeapStar 𝕄 nr₂ s₂ s₃ → HeapStar 𝕄 nr₂ s₁ s₃

/-- Reflexive-transitive closure of `HeapStepUntracked` (`_⇢*_`). -/
inductive HeapStarUntracked {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M) :
    State M → State M → Prop where
  | refl (s : State M) : HeapStarUntracked 𝕄 nr₂ s s
  | step {s₁ s₂ s₃ : State M} :
      HeapStepUntracked 𝕄 nr₂ s₁ s₂ →
      HeapStarUntracked 𝕄 nr₂ s₂ s₃ →
      HeapStarUntracked 𝕄 nr₂ s₁ s₃

/-- Reflexive-transitive closure of `HeapNumStep` (`_↠*_`). -/
inductive HeapNumStar {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M) :
    State M → State M → Prop where
  | refl (s : State M) : HeapNumStar 𝕄 nr₂ s s
  | step {s₁ s₂ s₃ : State M} :
      HeapNumStep 𝕄 nr₂ s₁ s₂ → HeapNumStar 𝕄 nr₂ s₂ s₃ → HeapNumStar 𝕄 nr₂ s₁ s₃

/-- Irreducible WHNF states (`Final` in `Graded.Heap.Reduction`). -/
def FinalState {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M) (s : State M) : Prop :=
  ∀ s' : State M, ¬ HeapStep 𝕄 nr₂ s s'

/-- Evaluation to a final WHNF state (`_⇘_` in `Graded.Heap.Reduction`). -/
def EvalToFinal {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M) (s s' : State M) : Prop :=
  HeapStar 𝕄 nr₂ s s' ∧ FinalState 𝕄 nr₂ s'

namespace HeapStar

variable {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}

theorem trans {s₁ s₂ s₃ : State M}
    (h₁ : HeapStar 𝕄 nr₂ s₁ s₂) (h₂ : HeapStar 𝕄 nr₂ s₂ s₃) :
    HeapStar 𝕄 nr₂ s₁ s₃ := by
  induction h₁ with
  | refl _ => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem toNumStar {s₁ s₂ : State M}
    (h : HeapStar 𝕄 nr₂ s₁ s₂) : HeapNumStar 𝕄 nr₂ s₁ s₂ := by
  induction h with
  | refl s => exact .refl s
  | step hs _ ih =>
    cases hs with
    | elimStep he => exact .step (.elimStep he) ih
    | valStep hv => exact .step (.valStep hv) ih

end HeapStar

namespace HeapStarUntracked

variable {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}

theorem trans {s₁ s₂ s₃ : State M}
    (h₁ : HeapStarUntracked 𝕄 nr₂ s₁ s₂) (h₂ : HeapStarUntracked 𝕄 nr₂ s₂ s₃) :
    HeapStarUntracked 𝕄 nr₂ s₁ s₃ := by
  induction h₁ with
  | refl _ => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

end HeapStarUntracked

namespace HeapNumStar

variable {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}

theorem trans {s₁ s₂ s₃ : State M}
    (h₁ : HeapNumStar 𝕄 nr₂ s₁ s₂) (h₂ : HeapNumStar 𝕄 nr₂ s₂ s₃) :
    HeapNumStar 𝕄 nr₂ s₁ s₃ := by
  induction h₁ with
  | refl _ => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

end HeapNumStar

/-! ### Helper Lemmas for Usage Preservation (`Graded.Heap.Usage.Reduction`) -/

namespace Usage

variable {M : Type} {𝕄 : Modality M}

@[simp] theorem toGrade_mul_comm (m : Mode) (r : M) :
    𝕄.mul (Mode.toGrade 𝕄 m) r = 𝕄.mul r (Mode.toGrade 𝕄 m) := by
  cases m <;> simp [Mode.toGrade, 𝕄.zero_mul, 𝕄.mul_zero, 𝕄.one_mul, 𝕄.mul_one]

/-- Usage of the curried two-argument application
    `.app r₂ (.app r₁ (wk (step (step id)) u) (var 1)) (var 0)`
    used in `ValStep.prodWeakₕ` and `ValStep.sucₕ`. -/
theorem curried_app2 {δ : Conₘ M} {m : Mode} {r₁ r₂ : M} {u : GTerm M}
    (hu : Usage 𝕄 δ m u) :
    Usage 𝕄 (Conₘ.cons (Conₘ.cons δ (𝕄.mul (Mode.toGrade 𝕄 m) r₁))
      (𝕄.mul (Mode.toGrade 𝕄 m) r₂)) m
      (.app r₂ (.app r₁ (GTerm.wk (.step (.step .id)) u) (.var 1)) (.var 0)) := by
  have hu_wk : Usage 𝕄 (Conₘ.cons (Conₘ.cons δ 𝕄.zero) 𝕄.zero) m
      (GTerm.wk (.step (.step .id)) u) :=
    wkUsage (.step (.step .id)) hu
  have hvar1 : Usage 𝕄 (Conₘ.single 𝕄 1 (Mode.toGrade 𝕄 m)) m (.var 1) := .var
  have hvar0 : Usage 𝕄 (Conₘ.single 𝕄 0 (Mode.toGrade 𝕄 m)) m (.var 0) := .var
  have happ1 := app_same_mode (r := r₁) hu_wk hvar1
  have happ2 := app_same_mode (r := r₂) happ1 hvar0
  refine Usage.sub happ2 ?_
  intro z
  cases z with
  | zero =>
    dsimp only [Conₘ.add, Conₘ.cons, Conₘ.scale, Conₘ.single]
    rw [if_neg (by decide), if_pos rfl, 𝕄.mul_zero, 𝕄.add_zero, 𝕄.zero_add, toGrade_mul_comm]
    exact 𝕄.le_refl _
  | succ z =>
    cases z with
    | zero =>
      dsimp only [Conₘ.add, Conₘ.cons, Conₘ.scale, Conₘ.single]
      rw [if_pos rfl, if_neg (by decide), 𝕄.mul_zero, 𝕄.add_zero, 𝕄.zero_add, toGrade_mul_comm]
      exact 𝕄.le_refl _
    | succ z =>
      have h1 : z + 1 + 1 ≠ 1 := fun h ↦ Nat.noConfusion (Nat.succ.inj h)
      have h0 : z + 1 + 1 ≠ 0 := Nat.succ_ne_zero _
      dsimp only [Conₘ.add, Conₘ.cons, Conₘ.scale, Conₘ.single]
      rw [if_neg h1, if_neg h0, 𝕄.mul_zero, 𝕄.add_zero, 𝕄.mul_zero, 𝕄.add_zero]
      exact 𝕄.le_refl _

end Usage

/-- **M3 Theorem 4.3a (`▸-⇒ₑ` in `Graded.Heap.Usage.Reduction`)**:
    head-eliminator transitions preserve `StateUsage`. -/
theorem usage_pres_elimStep {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s s' : State M} (hs : StateUsage 𝕄 nr₂ s) (hstep : ElimStep s s') :
    StateUsage 𝕄 nr₂ s' := by
  rcases hs with ⟨γ, δ, η, hH, ht, hS, hbound⟩
  cases hstep with
  | @appₕ H p t u ρ S =>
    let q := Stack.mult 𝕄 nr₂ S
    rcases Usage.inv_app ht with ⟨γf, δu, hf, hu, hle⟩
    have hf' : Usage 𝕄 γf (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (.appₑ p u ρ :: S))) t := by
      simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one]
      exact hf
    have hS' : StackUsage 𝕄 nr₂
        (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q (Conₘ.scale 𝕄 p (Conₘ.wk 𝕄 ρ δu))))
        (.appₑ p u ρ :: S) :=
      .cons (.appₑ hu) hS
    refine ⟨γ, γf, _, hH, hf', hS', ?_⟩
    simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one]
    have h1 : Conₘ.le 𝕄 γ
        (Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ (Conₘ.add 𝕄 γf (Conₘ.scale 𝕄 p δu)))) η) :=
      Conₘ.le_trans 𝕄 hbound
        (Conₘ.add_mono 𝕄 (Conₘ.scale_mono_right 𝕄 q (Conₘ.wk_mono 𝕄 ρ hle)) (Conₘ.le_refl 𝕄 η))
    have heq : Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ (Conₘ.add 𝕄 γf (Conₘ.scale 𝕄 p δu)))) η =
        Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ γf))
          (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q (Conₘ.scale 𝕄 p (Conₘ.wk 𝕄 ρ δu)))) := by
      rw [Conₘ.wk_add, Conₘ.wk_scale, Conₘ.scale_add_distrib, Conₘ.add_assoc,
        Conₘ.add_comm 𝕄 (Conₘ.scale 𝕄 q _) η]
    rw [← heq]
    exact h1
  | @fstₕ H p t ρ S =>
    let q := Stack.mult 𝕄 nr₂ S
    rcases Usage.inv_fst ht with ⟨hu, hcond⟩
    have hu' : Usage 𝕄 δ (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (.fstₑ p :: S))) t := by
      simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one]
      exact hu
    have hS' : StackUsage 𝕄 nr₂ (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q (Conₘ.zero 𝕄))) (.fstₑ p :: S) :=
      .cons (.fstₑ hcond) hS
    refine ⟨γ, δ, _, hH, hu', hS', ?_⟩
    simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one, Conₘ.scale_zero, Conₘ.add_zero]
    exact hbound
  | @sndₕ H p t ρ S =>
    let q := Stack.mult 𝕄 nr₂ S
    have hu := Usage.inv_snd ht
    have hu' : Usage 𝕄 δ (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (.sndₑ p :: S))) t := by
      simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one]
      exact hu
    have hS' : StackUsage 𝕄 nr₂ (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q (Conₘ.zero 𝕄))) (.sndₑ p :: S) :=
      .cons .sndₑ hS
    refine ⟨γ, δ, _, hH, hu', hS', ?_⟩
    simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one, Conₘ.scale_zero, Conₘ.add_zero]
    exact hbound
  | @prodrecₕ H r p q₀ A t u ρ S =>
    let q := Stack.mult 𝕄 nr₂ S
    rcases Usage.inv_prodrec ht with ⟨γt, δu, ηA, ht1, hu1, hA, hle⟩
    have ht1' : Usage 𝕄 γt (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (.prodrecₑ r p q₀ A u ρ :: S))) t := by
      simp only [Stack.mult_cons, Cont.mult]
      rw [← Mode.scale_ofGrade hw q r]
      exact ht1
    have hS' : StackUsage 𝕄 nr₂
        (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δu)))
        (.prodrecₑ r p q₀ A u ρ :: S) :=
      .cons (.prodrecₑ hu1 hA) hS
    refine ⟨γ, γt, _, hH, ht1', hS', ?_⟩
    simp only [Stack.mult_cons, Cont.mult]
    have h1 : Conₘ.le 𝕄 γ
        (Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 r γt) δu))) η) :=
      Conₘ.le_trans 𝕄 hbound
        (Conₘ.add_mono 𝕄 (Conₘ.scale_mono_right 𝕄 q (Conₘ.wk_mono 𝕄 ρ hle)) (Conₘ.le_refl 𝕄 η))
    have heq : Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 r γt) δu))) η =
        Conₘ.add 𝕄 (Conₘ.scale 𝕄 (𝕄.mul q r) (Conₘ.wk 𝕄 ρ γt))
          (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δu))) := by
      rw [Conₘ.wk_add, Conₘ.wk_scale, Conₘ.scale_add_distrib, ← Conₘ.scale_assoc,
        Conₘ.add_assoc, Conₘ.add_comm 𝕄 (Conₘ.scale 𝕄 q _) η]
    rw [← heq]
    exact h1
  | @unitrecₕ H p q₀ A t u ρ S =>
    let q := Stack.mult 𝕄 nr₂ S
    rcases Usage.inv_unitrec ht with ⟨γt, δu, ηA, ht1, hu1, hA, hle⟩
    have ht1' : Usage 𝕄 γt (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (.unitrecₑ p q₀ A u ρ :: S))) t := by
      simp only [Stack.mult_cons, Cont.mult]
      rw [← Mode.scale_ofGrade hw q p]
      exact ht1
    have hS' : StackUsage 𝕄 nr₂
        (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δu)))
        (.unitrecₑ p q₀ A u ρ :: S) :=
      .cons (.unitrecₑ hu1 hA) hS
    refine ⟨γ, γt, _, hH, ht1', hS', ?_⟩
    simp only [Stack.mult_cons, Cont.mult]
    have h1 : Conₘ.le 𝕄 γ
        (Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 p γt) δu))) η) :=
      Conₘ.le_trans 𝕄 hbound
        (Conₘ.add_mono 𝕄 (Conₘ.scale_mono_right 𝕄 q (Conₘ.wk_mono 𝕄 ρ hle)) (Conₘ.le_refl 𝕄 η))
    have heq : Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 p γt) δu))) η =
        Conₘ.add 𝕄 (Conₘ.scale 𝕄 (𝕄.mul q p) (Conₘ.wk 𝕄 ρ γt))
          (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δu))) := by
      rw [Conₘ.wk_add, Conₘ.wk_scale, Conₘ.scale_add_distrib, ← Conₘ.scale_assoc,
        Conₘ.add_assoc, Conₘ.add_comm 𝕄 (Conₘ.scale 𝕄 q _) η]
    rw [← heq]
    exact h1
  | @natrecₕ H p q₀ r A z s t ρ S =>
    let q := Stack.mult 𝕄 nr₂ S
    let r' := nr₂ p r
    rcases Usage.inv_natrec ht with ⟨γz, δs, ηn, θA, χ, x, hz, hs, hn, hA, hx1, hx2, hχ1, hχ2, hle⟩
    have hq_imp : q = 𝕄.zero → 𝕄.mul q r' = 𝕄.zero := by
      intro hq0; rw [hq0, 𝕄.zero_mul]
    let ηn' := Conₘ.scale 𝕄 (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 (𝕄.mul q r'))) ηn
    have hn' : Usage 𝕄 ηn' (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (.natrecₑ p q₀ r A z s ρ :: S))) t := by
      simp only [Stack.mult_cons, Cont.mult]
      exact Usage.ofGrade_scale_self hn hq_imp
    have hS' : StackUsage 𝕄 nr₂
        (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ χ)))
        (.natrecₑ p q₀ r A z s ρ :: S) :=
      .cons (.natrecₑ hz hs hA hχ1 hχ2) hS
    refine ⟨γ, ηn', _, hH, hn', hS', ?_⟩
    simp only [Stack.mult_cons, Cont.mult]
    have hscale_ηn' : Conₘ.scale 𝕄 (𝕄.mul q r') (Conₘ.wk 𝕄 ρ ηn') =
        Conₘ.scale 𝕄 (𝕄.mul q r') (Conₘ.wk 𝕄 ρ ηn) := by
      rw [Conₘ.wk_scale, ← Conₘ.scale_assoc, Mode.mul_toGrade_ofGrade]
    rw [hscale_ηn']
    have hqx_le : 𝕄.le (𝕄.mul q x) (𝕄.mul q r') := by
      by_cases hq0 : q = 𝕄.zero
      · rw [hq0]
        simp only [𝕄.zero_mul]
        exact 𝕄.le_refl 𝕄.zero
      · have hx2' : 𝕄.le x (𝕄.add p (𝕄.mul r x)) := by
          rw [Mode.ofGrade_ne_zero 𝕄 hq0] at hx2
          simpa only [Mode.toGrade, 𝕄.one_mul] using hx2
        exact 𝕄.mul_mono_right q (hnr.maximal hx1 hx2')
    have h1 : Conₘ.le 𝕄 γ
        (Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 x ηn) χ))) η) :=
      Conₘ.le_trans 𝕄 hbound
        (Conₘ.add_mono 𝕄 (Conₘ.scale_mono_right 𝕄 q (Conₘ.wk_mono 𝕄 ρ hle)) (Conₘ.le_refl 𝕄 η))
    have h2 : Conₘ.le 𝕄
        (Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 x ηn) χ))) η)
        (Conₘ.add 𝕄 (Conₘ.scale 𝕄 (𝕄.mul q r') (Conₘ.wk 𝕄 ρ ηn))
          (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ χ)))) := by
      rw [Conₘ.wk_add, Conₘ.wk_scale, Conₘ.scale_add_distrib, ← Conₘ.scale_assoc,
        Conₘ.add_assoc, Conₘ.add_comm 𝕄 (Conₘ.scale 𝕄 q _) η]
      exact Conₘ.add_mono 𝕄 (Conₘ.scale_mono 𝕄 hqx_le (Conₘ.le_refl 𝕄 _)) (Conₘ.le_refl 𝕄 _)
    exact Conₘ.le_trans 𝕄 h1 h2

/-- **M3 Theorem 4.3b (`▸-⇾ₑ` in `Graded.Heap.Usage.Reduction`)**:
    tracked eliminator and variable lookup steps preserve `StateUsage`. -/
theorem usage_pres_trackElimStep {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s s' : State M} (hs : StateUsage 𝕄 nr₂ s) (hstep : TrackElimStep 𝕄 nr₂ s s') :
    StateUsage 𝕄 nr₂ s' := by
  cases hstep with
  | elim he => exact usage_pres_elimStep hw hnr hs he
  | @var H H' x t ρ ρ' S hlookup =>
    let p := Stack.mult 𝕄 nr₂ S
    rcases hs with ⟨γ, δ, η, hH, ht, hS, hbound⟩
    have hvar_raw := var_state_bound ht hbound
    have hvar_bound : 𝕄.le (γ (wkVar ρ x)) (𝕄.add (η (wkVar ρ x)) p) := by
      rw [𝕄.add_comm]
      exact hvar_raw
    rcases heapLookup_usage hw hlookup hH hvar_bound with ⟨δ', ht', hH'⟩
    refine ⟨_, δ', η, hH', ht', hS, ?_⟩
    have hγ_le : Conₘ.le 𝕄 γ (Conₘ.add 𝕄 (Conₘ.single 𝕄 (wkVar ρ x) p) η) := by
      have hvar := Usage.inv_var ht
      have hwk := Conₘ.wk_mono 𝕄 ρ hvar
      rw [Conₘ.wk_single] at hwk
      have hscale := Conₘ.scale_mono_right 𝕄 p hwk
      rw [Conₘ.scale_single, Mode.mul_toGrade_ofGrade] at hscale
      exact Conₘ.le_trans 𝕄 hbound (Conₘ.add_mono 𝕄 hscale (Conₘ.le_refl 𝕄 η))
    have hupd_le : Conₘ.le 𝕄 (Conₘ.update γ (wkVar ρ x) (η (wkVar ρ x))) η := by
      intro z
      by_cases hz : z = wkVar ρ x
      · subst hz
        simp only [Conₘ.update, ↓reduceIte]
        exact 𝕄.le_refl _
      · simp only [Conₘ.update, hz, ↓reduceIte]
        have hz_le := hγ_le z
        simpa only [Conₘ.add, Conₘ.single, hz, ↓reduceIte, 𝕄.zero_add] using hz_le
    rw [Conₘ.add_comm 𝕄 (Conₘ.scale 𝕄 p _) η]
    exact Conₘ.add_mono 𝕄 hupd_le (Conₘ.le_refl 𝕄 _)

/-- **M3 Theorem 4.3c (`▸-⇒ᵥ` in `Graded.Heap.Usage.Reduction`)**:
    value-continuation β-reduction steps preserve `StateUsage`. -/
theorem usage_pres_valStep {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s s' : State M} (hs : StateUsage 𝕄 nr₂ s) (hstep : ValStep 𝕄 nr₂ s s') :
    StateUsage 𝕄 nr₂ s' := by
  rcases hs with ⟨γ, δ, η_all, hH, ht, hS_all, hbound⟩
  cases hstep with
  | @lamₕ H p t u ρ ρ' S =>
    let q := Stack.mult 𝕄 nr₂ S
    cases hS_all with
    | @cons η θ _ _ hc hS =>
      cases hc with
      | @appₑ θ' _ _ _ _ hu =>
        have hbody : Usage 𝕄 (Conₘ.cons δ (𝕄.mul (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 q)) p))
            (Mode.ofGrade 𝕄 q) t := by
          simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one] at ht
          exact Usage.inv_lam ht
        have hu' : Usage 𝕄 θ' (Mode.ofGrade 𝕄 (𝕄.mul q p)) u := by
          rw [← Mode.scale_ofGrade hw q p]
          exact hu
        have hγ_le : Conₘ.le 𝕄 γ
            (Conₘ.add 𝕄 (Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δ)) η)
              (Conₘ.scale 𝕄 (𝕄.mul q p) (Conₘ.wk 𝕄 ρ' θ'))) := by
          simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one] at hbound
          rw [Conₘ.scale_assoc, Conₘ.add_assoc]
          exact hbound
        have hH' : HeapUsage 𝕄
            (Conₘ.cons (Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δ)) η) (𝕄.mul q p))
            (.cons H (𝕄.mul q p) ⟨u, ρ'⟩) :=
          .cons (.sub hH hγ_le) hu'
        have hbody' : Usage 𝕄 (Conₘ.cons δ (𝕄.mul (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 q)) p))
            (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (Stack.wk1 S))) t := by
          rw [Stack.mult_wk1]
          exact hbody
        refine ⟨_, _, _, hH', hbody', hS.wk (.step .id), ?_⟩
        rw [Stack.mult_wk1]
        intro z
        cases z with
        | zero =>
          dsimp only [q]
          simp only [Conₘ.cons, Conₘ.add, Conₘ.scale, Conₘ.wk, Conₘ.head, 𝕄.add_zero,
            ← 𝕄.mul_assoc, Mode.mul_toGrade_ofGrade]
          exact 𝕄.le_refl _
        | succ z =>
          exact 𝕄.le_refl _
  | @prodStrongₕ₁ H p t₁ t₂ ρ S =>
    let q := Stack.mult 𝕄 nr₂ S
    cases hS_all with
    | @cons η _ _ _ hc hS =>
      cases hc with
      | fstₑ hcond =>
        simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one] at ht hbound
        rcases Usage.inv_prodStrong ht with ⟨δ₁, δ₂, ht₁, _, hδ_le⟩
        rw [Mode.scale_ofGrade hw q p] at ht₁
        have hqp_imp : 𝕄.mul q p = 𝕄.zero → q = 𝕄.zero := by
          intro hqp0
          have h1 : 𝕄.le (𝕄.mul q (𝕄.mul (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 q)) p))
              (𝕄.mul q (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 q))) :=
            𝕄.mul_mono_right q hcond
          rw [← 𝕄.mul_assoc, Mode.mul_toGrade_ofGrade, hqp0] at h1
          exact hw.zero_le_eq_zero h1
        let δ₁' := Conₘ.scale 𝕄 (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 q)) δ₁
        have ht₁' : Usage 𝕄 δ₁' (Mode.ofGrade 𝕄 q) t₁ := Usage.ofGrade_scale_self ht₁ hqp_imp
        refine ⟨γ, δ₁', η, hH, ht₁', hS, ?_⟩
        simp only [Conₘ.scale_zero, Conₘ.add_zero] at hbound
        have hscale_δ₁' : Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δ₁') = Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δ₁) := by
          rw [Conₘ.wk_scale, ← Conₘ.scale_assoc, Mode.mul_toGrade_ofGrade]
        rw [hscale_δ₁']
        have hmeet_le : Conₘ.le 𝕄 δ (Conₘ.scale 𝕄 p δ₁) :=
          Conₘ.le_trans 𝕄 hδ_le (fun x ↦ 𝕄.meet_le_left _ _)
        have hqp_le_q : 𝕄.le (𝕄.mul q p) q := by
          have h1 := 𝕄.mul_mono_right q hcond
          rwa [← 𝕄.mul_assoc, Mode.mul_toGrade_ofGrade] at h1
        have hwk_le : Conₘ.le 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δ))
            (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δ₁)) := by
          have h1 := Conₘ.scale_mono_right 𝕄 q (Conₘ.wk_mono 𝕄 ρ hmeet_le)
          rw [Conₘ.wk_scale, ← Conₘ.scale_assoc] at h1
          exact Conₘ.le_trans 𝕄 h1 (Conₘ.scale_mono 𝕄 hqp_le_q (Conₘ.le_refl 𝕄 _))
        exact Conₘ.le_trans 𝕄 hbound (Conₘ.add_mono 𝕄 hwk_le (Conₘ.le_refl 𝕄 η))
  | @prodStrongₕ₂ H p t₁ t₂ ρ S =>
    let q := Stack.mult 𝕄 nr₂ S
    cases hS_all with
    | @cons η _ _ _ hc hS =>
      cases hc with
      | sndₑ =>
        simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one] at ht hbound
        rcases Usage.inv_prodStrong ht with ⟨δ₁, δ₂, _, ht₂, hδ_le⟩
        refine ⟨γ, δ₂, η, hH, ht₂, hS, ?_⟩
        simp only [Conₘ.scale_zero, Conₘ.add_zero] at hbound
        have hmeet_le : Conₘ.le 𝕄 δ δ₂ :=
          Conₘ.le_trans 𝕄 hδ_le (fun x ↦ 𝕄.meet_le_right _ _)
        exact Conₘ.le_trans 𝕄 hbound
          (Conₘ.add_mono 𝕄 (Conₘ.scale_mono_right 𝕄 q (Conₘ.wk_mono 𝕄 ρ hmeet_le))
            (Conₘ.le_refl 𝕄 η))
  | @prodWeakₕ H r p q₀ t₁ t₂ A u ρ ρ' S =>
    let q' := Stack.mult 𝕄 nr₂ S
    cases hS_all with
    | @cons η _ _ _ hc hS =>
      cases hc with
      | @prodrecₑ θ' _ _ _ _ _ _ _ _ hu hA =>
        simp only [Stack.mult_cons, Cont.mult] at ht hbound
        rcases Usage.inv_prodWeak ht with ⟨δ₁, δ₂, ht₁, ht₂, hδ_le⟩
        rw [Mode.scale_ofGrade hw (𝕄.mul q' r) p] at ht₁
        have hγ_le : Conₘ.le 𝕄 γ
            (Conₘ.add 𝕄
              (Conₘ.add 𝕄 (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ')))
                (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 ρ δ₂)))
              (Conₘ.scale 𝕄 (𝕄.mul (𝕄.mul q' r) p) (Conₘ.wk 𝕄 ρ δ₁))) := by
          have h1 : Conₘ.le 𝕄 γ
              (Conₘ.add 𝕄 (Conₘ.scale 𝕄 (𝕄.mul q' r)
                (Conₘ.wk 𝕄 ρ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 p δ₁) δ₂)))
                (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ')))) :=
            Conₘ.le_trans 𝕄 hbound
              (Conₘ.add_mono 𝕄
                (Conₘ.scale_mono_right 𝕄 (𝕄.mul q' r) (Conₘ.wk_mono 𝕄 ρ hδ_le))
                (Conₘ.le_refl 𝕄 _))
          have heq : Conₘ.add 𝕄 (Conₘ.scale 𝕄 (𝕄.mul q' r)
              (Conₘ.wk 𝕄 ρ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 p δ₁) δ₂)))
              (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ'))) =
              Conₘ.add 𝕄
                (Conₘ.add 𝕄 (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ')))
                  (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 ρ δ₂)))
                (Conₘ.scale 𝕄 (𝕄.mul (𝕄.mul q' r) p) (Conₘ.wk 𝕄 ρ δ₁)) := by
            rw [Conₘ.wk_add, Conₘ.wk_scale, Conₘ.scale_add_distrib, ← Conₘ.scale_assoc,
              Conₘ.add_comm 𝕄 _ (Conₘ.add 𝕄 η _),
              Conₘ.add_comm 𝕄 (Conₘ.scale 𝕄 (𝕄.mul (𝕄.mul q' r) p) _) _,
              Conₘ.add_assoc, ← Conₘ.add_assoc, ← Conₘ.add_assoc]
          rw [← heq]
          exact h1
        have hH₁ : HeapUsage 𝕄
            (Conₘ.cons
              (Conₘ.add 𝕄 (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ')))
                (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 ρ δ₂)))
              (𝕄.mul (𝕄.mul q' r) p))
            (.cons H (𝕄.mul (𝕄.mul q' r) p) ⟨t₁, ρ⟩) :=
          .cons (.sub hH hγ_le) ht₁
        have hH₁_sub : HeapUsage 𝕄
            (Conₘ.add 𝕄
              (Conₘ.cons (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ')))
                (𝕄.mul (𝕄.mul q' r) p))
              (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 (.step ρ) δ₂)))
            (.cons H (𝕄.mul (𝕄.mul q' r) p) ⟨t₁, ρ⟩) := by
          have heq : Conₘ.add 𝕄
              (Conₘ.cons (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ')))
                (𝕄.mul (𝕄.mul q' r) p))
              (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 (.step ρ) δ₂)) =
              Conₘ.cons
                (Conₘ.add 𝕄 (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ')))
                  (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 ρ δ₂)))
                (𝕄.mul (𝕄.mul q' r) p) := by
            funext z; cases z <;> simp [Conₘ.add, Conₘ.cons, Conₘ.scale, Conₘ.wk, 𝕄.mul_zero, 𝕄.add_zero]
          rw [heq]
          exact hH₁
        have hH₂ : HeapUsage 𝕄
            (Conₘ.cons
              (Conₘ.cons (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ')))
                (𝕄.mul (𝕄.mul q' r) p))
              (𝕄.mul q' r))
            (.cons (.cons H (𝕄.mul (𝕄.mul q' r) p) ⟨t₁, ρ⟩) (𝕄.mul q' r) ⟨t₂, .step ρ⟩) :=
          .cons hH₁_sub ht₂
        have happ : Usage 𝕄
            (Conₘ.cons (Conₘ.cons θ' (𝕄.mul (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 q')) (𝕄.mul r p)))
              (𝕄.mul (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 q')) r))
            (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (Stack.wk2 S)))
            (.app r (.app (𝕄.mul r p) (GTerm.wk (.step (.step .id)) u) (.var 1)) (.var 0)) := by
          rw [Stack.mult_wk2]
          exact Usage.curried_app2 hu
        refine ⟨_, _, _, hH₂, happ, hS.wk (.step (.step .id)), ?_⟩
        rw [Stack.mult_wk2]
        intro z
        cases z with
        | zero =>
          dsimp only [q']
          simp only [Conₘ.cons, Conₘ.add, Conₘ.scale, Conₘ.wk, Conₘ.head, 𝕄.add_zero,
            ← 𝕄.mul_assoc, Mode.mul_toGrade_ofGrade]
          exact 𝕄.le_refl _
        | succ z =>
          cases z with
          | zero =>
            dsimp only [q']
            simp only [Conₘ.cons, Conₘ.add, Conₘ.scale, Conₘ.wk, Conₘ.tail, Conₘ.head,
              𝕄.add_zero, ← 𝕄.mul_assoc, Mode.mul_toGrade_ofGrade]
            exact 𝕄.le_refl _
          | succ z =>
            simp only [Conₘ.cons, Conₘ.add, Conₘ.scale, Conₘ.wk]
            rw [𝕄.add_comm]
            exact 𝕄.le_refl _
  | @zeroₕ H p q₀ r A z s ρ ρ' S =>
    let q' := Stack.mult 𝕄 nr₂ S
    cases hS_all with
    | @cons η _ _ _ hc hS =>
      cases hc with
      | @natrecₑ γz δs θA χ _ _ _ _ _ _ _ _ hz _ _ hχ1 _ =>
        simp only [Stack.mult_cons, Cont.mult] at ht hbound
        have hδ0 := Usage.inv_zero ht
        refine ⟨γ, γz, η, hH, hz, hS, ?_⟩
        have h1 : Conₘ.le 𝕄 (Conₘ.scale 𝕄 (𝕄.mul q' (nr₂ p r)) (Conₘ.wk 𝕄 ρ δ)) (Conₘ.zero 𝕄) := by
          have hs0 := Conₘ.scale_mono_right 𝕄 (𝕄.mul q' (nr₂ p r)) (Conₘ.wk_mono 𝕄 ρ hδ0)
          rwa [Conₘ.wk_zero, Conₘ.scale_zero] at hs0
        have h2 : Conₘ.le 𝕄 γ (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' χ))) := by
          have hsum := Conₘ.add_mono 𝕄 h1
            (Conₘ.le_refl 𝕄 (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' χ))))
          rw [Conₘ.zero_add] at hsum
          exact Conₘ.le_trans 𝕄 hbound hsum
        have h3 : Conₘ.le 𝕄 (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' χ)))
            (Conₘ.add 𝕄 (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' γz)) η) := by
          rw [Conₘ.add_comm 𝕄 η]
          exact Conₘ.add_mono 𝕄 (Conₘ.scale_mono_right 𝕄 q' (Conₘ.wk_mono 𝕄 ρ' hχ1))
            (Conₘ.le_refl 𝕄 η)
        exact Conₘ.le_trans 𝕄 h2 h3
  | @sucₕ H p q₀ r t A z s ρ ρ' S =>
    let q' := Stack.mult 𝕄 nr₂ S
    let p' := nr₂ p r
    cases hS_all with
    | @cons η _ _ _ hc hS =>
      cases hc with
      | @natrecₑ γz δs θA χ _ _ _ _ _ _ _ _ hz hs hA hχ1 hχ2 =>
        simp only [Stack.mult_cons, Cont.mult] at ht hbound
        have ht_pred : Usage 𝕄 δ (Mode.ofGrade 𝕄 (𝕄.mul q' p')) t := Usage.inv_succ ht
        let m := Mode.ofGrade 𝕄 q'
        have hnr_body : Usage 𝕄 (Conₘ.cons χ (𝕄.mul p' (Mode.toGrade 𝕄 m))) m
            (.natrec p q₀ r (GTerm.wk (.lift (.step .id)) A) (GTerm.wk1 z) (GTerm.wk1 s) (.var 0)) := by
          have hz1 : Usage 𝕄 (Conₘ.cons γz 𝕄.zero) m (GTerm.wk1 z) := Usage.wkUsage (.step .id) hz
          have hs1 : Usage 𝕄 (Conₘ.cons δs 𝕄.zero) m (GTerm.wk1 s) := Usage.wkUsage (.step .id) hs
          have hn0 : Usage 𝕄 (Conₘ.single 𝕄 0 (Mode.toGrade 𝕄 m)) m (.var 0) := .var
          have hA1 : Usage 𝕄 (Conₘ.cons (Conₘ.cons θA 𝕄.zero) 𝕄.zero) .zeroMode
              (GTerm.wk (.lift (.step .id)) A) := Usage.wkUsage (.lift (.step .id)) hA
          have hχ1' : Conₘ.le 𝕄 (Conₘ.cons χ 𝕄.zero) (Conₘ.cons γz 𝕄.zero) :=
            Conₘ.cons_le_cons 𝕄 hχ1 (𝕄.le_refl 𝕄.zero)
          have hχ2' : Conₘ.le 𝕄 (Conₘ.cons χ 𝕄.zero)
              (Conₘ.add 𝕄 (Conₘ.cons δs 𝕄.zero) (Conₘ.scale 𝕄 r (Conₘ.cons χ 𝕄.zero))) := by
            rw [Conₘ.cons_scale, 𝕄.mul_zero, Conₘ.cons_add, 𝕄.add_zero]
            exact Conₘ.cons_le_cons 𝕄 hχ2 (𝕄.le_refl 𝕄.zero)
          have hfix := Usage.natrec_fix (q := q₀) hz1 hs1 hn0 hA1 (hnr.le_one p r)
            (𝕄.mul_mono_right (Mode.toGrade 𝕄 m) (hnr.le_step p r)) hχ1' hχ2'
          have heq : Conₘ.add 𝕄 (Conₘ.scale 𝕄 p' (Conₘ.single 𝕄 0 (Mode.toGrade 𝕄 m)))
              (Conₘ.cons χ 𝕄.zero) = Conₘ.cons χ (𝕄.mul p' (Mode.toGrade 𝕄 m)) := by
            rw [Conₘ.single_zero, Conₘ.cons_scale, Conₘ.scale_zero, Conₘ.cons_add,
              Conₘ.zero_add, 𝕄.add_zero]
          rwa [heq] at hfix
        let δ_nr := Conₘ.scale 𝕄 (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 (𝕄.mul q' r)))
          (Conₘ.cons χ (𝕄.mul p' (Mode.toGrade 𝕄 m)))
        have hnr_body' : Usage 𝕄 δ_nr (Mode.ofGrade 𝕄 (𝕄.mul q' r))
            (.natrec p q₀ r (GTerm.wk (.lift (.step .id)) A) (GTerm.wk1 z) (GTerm.wk1 s) (.var 0)) := by
          apply Usage.ofGrade_scale_self hnr_body
          intro hq0
          rw [hq0, 𝕄.zero_mul]
        have hscale_nr : Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 (.lift ρ') δ_nr) =
            Conₘ.cons (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 ρ' χ))
              (𝕄.mul (𝕄.mul q' r) p') := by
          rw [Conₘ.wk_scale, ← Conₘ.scale_assoc, Mode.mul_toGrade_ofGrade]
          have hwk_lift : Conₘ.wk 𝕄 (.lift ρ') (Conₘ.cons χ (𝕄.mul p' (Mode.toGrade 𝕄 m))) =
              Conₘ.cons (Conₘ.wk 𝕄 ρ' χ) (𝕄.mul p' (Mode.toGrade 𝕄 m)) := rfl
          rw [hwk_lift, Conₘ.cons_scale]
          congr 1
          have hm_comm : 𝕄.mul p' (Mode.toGrade 𝕄 m) = 𝕄.mul (Mode.toGrade 𝕄 m) p' :=
            (Usage.toGrade_mul_comm m p').symm
          rw [hm_comm, ← 𝕄.mul_assoc, 𝕄.mul_assoc q' r (Mode.toGrade 𝕄 m),
            ← Usage.toGrade_mul_comm m r, ← 𝕄.mul_assoc q' (Mode.toGrade 𝕄 m) r,
            Mode.mul_toGrade_ofGrade]
        have hγ_le : Conₘ.le 𝕄 γ
            (Conₘ.add 𝕄 (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' χ)))
              (Conₘ.scale 𝕄 (𝕄.mul q' p') (Conₘ.wk 𝕄 ρ δ))) := by
          rw [Conₘ.add_comm 𝕄 _ (Conₘ.scale 𝕄 (𝕄.mul q' p') _)]
          exact hbound
        have hH₁ : HeapUsage 𝕄
            (Conₘ.cons (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' χ))) (𝕄.mul q' p'))
            (.cons H (𝕄.mul q' p') ⟨t, ρ⟩) :=
          .cons (.sub hH hγ_le) ht_pred
        have hH₁_sub : HeapUsage 𝕄
            (Conₘ.add 𝕄 (Conₘ.cons (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' δs))) (𝕄.mul q' p))
              (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 (.lift ρ') δ_nr)))
            (.cons H (𝕄.mul q' p') ⟨t, ρ⟩) := by
          rw [hscale_nr, Conₘ.cons_add]
          apply HeapUsage.sub hH₁
          refine Conₘ.cons_le_cons 𝕄 ?_ ?_
          · have hχ_step : Conₘ.le 𝕄 (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' χ))
                (Conₘ.add 𝕄 (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' δs))
                  (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 ρ' χ))) := by
              have h1 := Conₘ.scale_mono_right 𝕄 q' (Conₘ.wk_mono 𝕄 ρ' hχ2)
              rwa [Conₘ.wk_add, Conₘ.wk_scale, Conₘ.scale_add_distrib, ← Conₘ.scale_assoc] at h1
            rw [Conₘ.add_assoc]
            exact Conₘ.add_mono 𝕄 (Conₘ.le_refl 𝕄 η) hχ_step
          · have h1 := 𝕄.mul_mono_right q' (hnr.le_step p r)
            rwa [𝕄.left_distrib, ← 𝕄.mul_assoc] at h1
        have hH₂ : HeapUsage 𝕄
            (Conₘ.cons (Conₘ.cons (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' δs))) (𝕄.mul q' p))
              (𝕄.mul q' r))
            (.cons (.cons H (𝕄.mul q' p') ⟨t, ρ⟩) (𝕄.mul q' r)
              ⟨.natrec p q₀ r (GTerm.wk (.lift (.step .id)) A) (GTerm.wk1 z) (GTerm.wk1 s) (.var 0),
                .lift ρ'⟩) :=
          .cons hH₁_sub hnr_body'
        have happ : Usage 𝕄
            (Conₘ.cons (Conₘ.cons δs (𝕄.mul (Mode.toGrade 𝕄 m) p))
              (𝕄.mul (Mode.toGrade 𝕄 m) r))
            (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (Stack.wk2 S)))
            (.app r (.app p (GTerm.wk (.step (.step .id)) s) (.var 1)) (.var 0)) := by
          rw [Stack.mult_wk2]
          exact Usage.curried_app2 hs
        refine ⟨_, _, _, hH₂, happ, hS.wk (.step (.step .id)), ?_⟩
        rw [Stack.mult_wk2]
        intro z₀
        cases z₀ with
        | zero =>
          dsimp only [q', m]
          simp only [Conₘ.cons, Conₘ.add, Conₘ.scale, Conₘ.wk, Conₘ.head, 𝕄.add_zero,
            ← 𝕄.mul_assoc, Mode.mul_toGrade_ofGrade]
          exact 𝕄.le_refl _
        | succ z₀ =>
          cases z₀ with
          | zero =>
            dsimp only [q', m]
            simp only [Conₘ.cons, Conₘ.add, Conₘ.scale, Conₘ.wk, Conₘ.tail, Conₘ.head,
              𝕄.add_zero, ← 𝕄.mul_assoc, Mode.mul_toGrade_ofGrade]
            exact 𝕄.le_refl _
          | succ z₀ =>
            simp only [Conₘ.cons, Conₘ.add, Conₘ.scale, Conₘ.wk]
            rw [𝕄.add_comm]
            exact 𝕄.le_refl _
  | @starWeakₕ H p q₀ A u ρ ρ' S =>
    let q' := Stack.mult 𝕄 nr₂ S
    cases hS_all with
    | @cons η _ _ _ hc hS =>
      cases hc with
      | @unitrecₑ θ' _ _ _ _ _ _ _ hu _ =>
        simp only [Stack.mult_cons, Cont.mult] at ht hbound
        have hδ0 := Usage.inv_star ht
        refine ⟨γ, θ', η, hH, hu, hS, ?_⟩
        have h1 : Conₘ.le 𝕄 (Conₘ.scale 𝕄 (𝕄.mul q' p) (Conₘ.wk 𝕄 ρ δ)) (Conₘ.zero 𝕄) := by
          have hs0 := Conₘ.scale_mono_right 𝕄 (𝕄.mul q' p) (Conₘ.wk_mono 𝕄 ρ hδ0)
          rwa [Conₘ.wk_zero, Conₘ.scale_zero] at hs0
        have h2 : Conₘ.le 𝕄 γ (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ'))) := by
          have hsum := Conₘ.add_mono 𝕄 h1
            (Conₘ.le_refl 𝕄 (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ'))))
          rw [Conₘ.zero_add] at hsum
          exact Conₘ.le_trans 𝕄 hbound hsum
        rw [Conₘ.add_comm 𝕄 _ η]
        exact h2

/-- **M3 Theorem 4.3 (`▸-⇾` in `Graded.Heap.Usage.Reduction`)**:
    single-step WHNF heap machine reduction preserves `StateUsage`. -/
theorem usage_pres_step {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s s' : State M} (hs : StateUsage 𝕄 nr₂ s) (hstep : HeapStep 𝕄 nr₂ s s') :
    StateUsage 𝕄 nr₂ s' := by
  cases hstep with
  | elimStep he => exact usage_pres_trackElimStep hw hnr hs he
  | valStep hv => exact usage_pres_valStep hw hnr hs hv

/-- **M3 Theorem 4.3 (`▸-⇾*` in `Graded.Heap.Usage.Reduction`)**:
    multi-step WHNF heap machine reduction preserves `StateUsage`. -/
theorem usage_pres_star {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s s' : State M} (hs : StateUsage 𝕄 nr₂ s) (hstar : HeapStar 𝕄 nr₂ s s') :
    StateUsage 𝕄 nr₂ s' := by
  induction hstar with
  | refl _ => exact hs
  | step hstep _ ih => exact ih (usage_pres_step hw hnr hs hstep)

/-- `Graded.Heap.Usage.Reduction.¬▸-⇒ₙ`:
    `NumStep` (`⇒ₙ`) does not preserve `StateUsage` because `.sucₑ` is not in `ContUsage`. -/
theorem numStep_not_pres_usage {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {s s' : State M} (hs : StateUsage 𝕄 nr₂ s) (hstep : NumStep s s')
    (hs' : StateUsage 𝕄 nr₂ s') : False := by
  cases hstep with
  | sucₕ _ =>
    rcases hs' with ⟨_, _, _, _, _, hS', _⟩
    cases hS' with
    | cons hc _ => exact ContUsage.inv_sucₑ hc
  | numₕ _ =>
    rcases hs with ⟨_, _, _, _, _, hS, _⟩
    cases hS with
    | cons hc _ => exact ContUsage.inv_sucₑ hc

/-! ### Preservation of `StateUsageExt` across Full Numeral Reduction `↠*` -/

theorem usageExt_pres_elimStep {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s s' : State M} (hs : StateUsageExt 𝕄 nr₂ s) (hstep : ElimStep s s') :
    StateUsageExt 𝕄 nr₂ s' := by
  rcases hs with ⟨γ, δ, η, hH, ht, hS, hbound⟩
  cases hstep with
  | @appₕ H p t u ρ S =>
    let q := Stack.mult 𝕄 nr₂ S
    rcases Usage.inv_app ht with ⟨γf, δu, hf, hu, hle⟩
    have hf' : Usage 𝕄 γf (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (.appₑ p u ρ :: S))) t := by
      simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one]; exact hf
    refine ⟨γ, γf, _, hH, hf', .cons (.of_contUsage (.appₑ hu)) hS, ?_⟩
    simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one]
    have h1 := Conₘ.le_trans 𝕄 hbound
      (Conₘ.add_mono 𝕄 (Conₘ.scale_mono_right 𝕄 q (Conₘ.wk_mono 𝕄 ρ hle)) (Conₘ.le_refl 𝕄 η))
    have heq : Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ (Conₘ.add 𝕄 γf (Conₘ.scale 𝕄 p δu)))) η =
        Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ γf))
          (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q (Conₘ.scale 𝕄 p (Conₘ.wk 𝕄 ρ δu)))) := by
      rw [Conₘ.wk_add, Conₘ.wk_scale, Conₘ.scale_add_distrib, Conₘ.add_assoc,
        Conₘ.add_comm 𝕄 (Conₘ.scale 𝕄 q _) η]
    rwa [← heq]
  | @fstₕ H p t ρ S =>
    rcases Usage.inv_fst ht with ⟨hu, hcond⟩
    have hu' : Usage 𝕄 δ (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (.fstₑ p :: S))) t := by
      simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one]; exact hu
    refine ⟨γ, δ, _, hH, hu', .cons (.of_contUsage (.fstₑ hcond)) hS, ?_⟩
    simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one, Conₘ.scale_zero, Conₘ.add_zero]
    exact hbound
  | @sndₕ H p t ρ S =>
    have hu := Usage.inv_snd ht
    have hu' : Usage 𝕄 δ (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (.sndₑ p :: S))) t := by
      simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one]; exact hu
    refine ⟨γ, δ, _, hH, hu', .cons (.of_contUsage .sndₑ) hS, ?_⟩
    simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one, Conₘ.scale_zero, Conₘ.add_zero]
    exact hbound
  | @prodrecₕ H r p q₀ A t u ρ S =>
    let q := Stack.mult 𝕄 nr₂ S
    rcases Usage.inv_prodrec ht with ⟨γt, δu, ηA, ht1, hu1, hA, hle⟩
    have ht1' : Usage 𝕄 γt (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (.prodrecₑ r p q₀ A u ρ :: S))) t := by
      simp only [Stack.mult_cons, Cont.mult]
      rw [← Mode.scale_ofGrade hw q r]; exact ht1
    refine ⟨γ, γt, _, hH, ht1', .cons (.of_contUsage (.prodrecₑ hu1 hA)) hS, ?_⟩
    simp only [Stack.mult_cons, Cont.mult]
    have h1 := Conₘ.le_trans 𝕄 hbound
      (Conₘ.add_mono 𝕄 (Conₘ.scale_mono_right 𝕄 q (Conₘ.wk_mono 𝕄 ρ hle)) (Conₘ.le_refl 𝕄 η))
    have heq : Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 r γt) δu))) η =
        Conₘ.add 𝕄 (Conₘ.scale 𝕄 (𝕄.mul q r) (Conₘ.wk 𝕄 ρ γt))
          (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δu))) := by
      rw [Conₘ.wk_add, Conₘ.wk_scale, Conₘ.scale_add_distrib, ← Conₘ.scale_assoc,
        Conₘ.add_assoc, Conₘ.add_comm 𝕄 (Conₘ.scale 𝕄 q _) η]
    rwa [← heq]
  | @unitrecₕ H p q₀ A t u ρ S =>
    let q := Stack.mult 𝕄 nr₂ S
    rcases Usage.inv_unitrec ht with ⟨γt, δu, ηA, ht1, hu1, hA, hle⟩
    have ht1' : Usage 𝕄 γt (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (.unitrecₑ p q₀ A u ρ :: S))) t := by
      simp only [Stack.mult_cons, Cont.mult]
      rw [← Mode.scale_ofGrade hw q p]; exact ht1
    refine ⟨γ, γt, _, hH, ht1', .cons (.of_contUsage (.unitrecₑ hu1 hA)) hS, ?_⟩
    simp only [Stack.mult_cons, Cont.mult]
    have h1 := Conₘ.le_trans 𝕄 hbound
      (Conₘ.add_mono 𝕄 (Conₘ.scale_mono_right 𝕄 q (Conₘ.wk_mono 𝕄 ρ hle)) (Conₘ.le_refl 𝕄 η))
    have heq : Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 p γt) δu))) η =
        Conₘ.add 𝕄 (Conₘ.scale 𝕄 (𝕄.mul q p) (Conₘ.wk 𝕄 ρ γt))
          (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δu))) := by
      rw [Conₘ.wk_add, Conₘ.wk_scale, Conₘ.scale_add_distrib, ← Conₘ.scale_assoc,
        Conₘ.add_assoc, Conₘ.add_comm 𝕄 (Conₘ.scale 𝕄 q _) η]
    rwa [← heq]
  | @natrecₕ H p q₀ r A z s t ρ S =>
    let q := Stack.mult 𝕄 nr₂ S
    let r' := nr₂ p r
    rcases Usage.inv_natrec ht with ⟨γz, δs, ηn, θA, χ, x, hz, hs, hn, hA, hx1, hx2, hχ1, hχ2, hle⟩
    have hq_imp : q = 𝕄.zero → 𝕄.mul q r' = 𝕄.zero := by intro hq0; rw [hq0, 𝕄.zero_mul]
    let ηn' := Conₘ.scale 𝕄 (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 (𝕄.mul q r'))) ηn
    have hn' : Usage 𝕄 ηn' (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (.natrecₑ p q₀ r A z s ρ :: S))) t := by
      simp only [Stack.mult_cons, Cont.mult]; exact Usage.ofGrade_scale_self hn hq_imp
    refine ⟨γ, ηn', _, hH, hn', .cons (.of_contUsage (.natrecₑ hz hs hA hχ1 hχ2)) hS, ?_⟩
    simp only [Stack.mult_cons, Cont.mult]
    have hscale_ηn' : Conₘ.scale 𝕄 (𝕄.mul q r') (Conₘ.wk 𝕄 ρ ηn') =
        Conₘ.scale 𝕄 (𝕄.mul q r') (Conₘ.wk 𝕄 ρ ηn) := by
      rw [Conₘ.wk_scale, ← Conₘ.scale_assoc, Mode.mul_toGrade_ofGrade]
    rw [hscale_ηn']
    have hqx_le : 𝕄.le (𝕄.mul q x) (𝕄.mul q r') := by
      by_cases hq0 : q = 𝕄.zero
      · rw [hq0]; simp only [𝕄.zero_mul]; exact 𝕄.le_refl 𝕄.zero
      · have hx2' : 𝕄.le x (𝕄.add p (𝕄.mul r x)) := by
          rw [Mode.ofGrade_ne_zero 𝕄 hq0] at hx2
          simpa only [Mode.toGrade, 𝕄.one_mul] using hx2
        exact 𝕄.mul_mono_right q (hnr.maximal hx1 hx2')
    have h1 := Conₘ.le_trans 𝕄 hbound
      (Conₘ.add_mono 𝕄 (Conₘ.scale_mono_right 𝕄 q (Conₘ.wk_mono 𝕄 ρ hle)) (Conₘ.le_refl 𝕄 η))
    have h2 : Conₘ.le 𝕄
        (Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 x ηn) χ))) η)
        (Conₘ.add 𝕄 (Conₘ.scale 𝕄 (𝕄.mul q r') (Conₘ.wk 𝕄 ρ ηn))
          (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ χ)))) := by
      rw [Conₘ.wk_add, Conₘ.wk_scale, Conₘ.scale_add_distrib, ← Conₘ.scale_assoc,
        Conₘ.add_assoc, Conₘ.add_comm 𝕄 (Conₘ.scale 𝕄 q _) η]
      exact Conₘ.add_mono 𝕄 (Conₘ.scale_mono 𝕄 hqx_le (Conₘ.le_refl 𝕄 _)) (Conₘ.le_refl 𝕄 _)
    exact Conₘ.le_trans 𝕄 h1 h2

theorem usageExt_pres_trackElimStep {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s s' : State M} (hs : StateUsageExt 𝕄 nr₂ s) (hstep : TrackElimStep 𝕄 nr₂ s s') :
    StateUsageExt 𝕄 nr₂ s' := by
  cases hstep with
  | elim he => exact usageExt_pres_elimStep hw hnr hs he
  | @var H H' x t ρ ρ' S hlookup =>
    let p := Stack.mult 𝕄 nr₂ S
    rcases hs with ⟨γ, δ, η, hH, ht, hS, hbound⟩
    have hvar_raw := var_state_bound ht hbound
    have hvar_bound : 𝕄.le (γ (wkVar ρ x)) (𝕄.add (η (wkVar ρ x)) p) := by
      rw [𝕄.add_comm]; exact hvar_raw
    rcases heapLookup_usage hw hlookup hH hvar_bound with ⟨δ', ht', hH'⟩
    refine ⟨_, δ', η, hH', ht', hS, ?_⟩
    have hγ_le : Conₘ.le 𝕄 γ (Conₘ.add 𝕄 (Conₘ.single 𝕄 (wkVar ρ x) p) η) := by
      have hvar := Usage.inv_var ht
      have hwk := Conₘ.wk_mono 𝕄 ρ hvar
      rw [Conₘ.wk_single] at hwk
      have hscale := Conₘ.scale_mono_right 𝕄 p hwk
      rw [Conₘ.scale_single, Mode.mul_toGrade_ofGrade] at hscale
      exact Conₘ.le_trans 𝕄 hbound (Conₘ.add_mono 𝕄 hscale (Conₘ.le_refl 𝕄 η))
    have hupd_le : Conₘ.le 𝕄 (Conₘ.update γ (wkVar ρ x) (η (wkVar ρ x))) η := by
      intro z
      by_cases hz : z = wkVar ρ x
      · subst hz; simp only [Conₘ.update, ↓reduceIte]; exact 𝕄.le_refl _
      · simp only [Conₘ.update, hz, ↓reduceIte]
        have hz_le := hγ_le z
        simpa only [Conₘ.add, Conₘ.single, hz, ↓reduceIte, 𝕄.zero_add] using hz_le
    rw [Conₘ.add_comm 𝕄 (Conₘ.scale 𝕄 p _) η]
    exact Conₘ.add_mono 𝕄 hupd_le (Conₘ.le_refl 𝕄 _)

theorem usageExt_pres_valStep {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s s' : State M} (hs : StateUsageExt 𝕄 nr₂ s) (hstep : ValStep 𝕄 nr₂ s s') :
    StateUsageExt 𝕄 nr₂ s' := by
  rcases hs with ⟨γ, δ, η_all, hH, ht, hS_all, hbound⟩
  cases hstep with
  | @lamₕ H p t u ρ ρ' S =>
    let q := Stack.mult 𝕄 nr₂ S
    cases hS_all with
    | @cons η θ _ _ hcExt hS =>
      cases hcExt with
      | of_contUsage hc =>
        cases hc with
        | @appₑ θ' _ _ _ _ hu =>
          have hbody : Usage 𝕄 (Conₘ.cons δ (𝕄.mul (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 q)) p))
              (Mode.ofGrade 𝕄 q) t := by
            simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one] at ht
            exact Usage.inv_lam ht
          have hu' : Usage 𝕄 θ' (Mode.ofGrade 𝕄 (𝕄.mul q p)) u := by
            rw [← Mode.scale_ofGrade hw q p]
            exact hu
          have hγ_le : Conₘ.le 𝕄 γ
              (Conₘ.add 𝕄 (Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δ)) η)
                (Conₘ.scale 𝕄 (𝕄.mul q p) (Conₘ.wk 𝕄 ρ' θ'))) := by
            simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one] at hbound
            rw [Conₘ.scale_assoc, Conₘ.add_assoc]
            exact hbound
          have hH' : HeapUsage 𝕄
              (Conₘ.cons (Conₘ.add 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δ)) η) (𝕄.mul q p))
              (.cons H (𝕄.mul q p) ⟨u, ρ'⟩) :=
            .cons (.sub hH hγ_le) hu'
          have hbody' : Usage 𝕄 (Conₘ.cons δ (𝕄.mul (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 q)) p))
              (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (Stack.wk1 S))) t := by
            rw [Stack.mult_wk1]
            exact hbody
          refine ⟨_, _, _, hH', hbody', hS.wk (.step .id), ?_⟩
          rw [Stack.mult_wk1]
          intro z
          cases z with
          | zero =>
            dsimp only [q]
            simp only [Conₘ.cons, Conₘ.add, Conₘ.scale, Conₘ.wk, Conₘ.head, 𝕄.add_zero,
              ← 𝕄.mul_assoc, Mode.mul_toGrade_ofGrade]
            exact 𝕄.le_refl _
          | succ z =>
            exact 𝕄.le_refl _
  | @prodStrongₕ₁ H p t₁ t₂ ρ S =>
    let q := Stack.mult 𝕄 nr₂ S
    cases hS_all with
    | @cons η _ _ _ hcExt hS =>
      cases hcExt with
      | of_contUsage hc =>
        cases hc with
        | fstₑ hcond =>
          simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one] at ht hbound
          rcases Usage.inv_prodStrong ht with ⟨δ₁, δ₂, ht₁, _, hδ_le⟩
          rw [Mode.scale_ofGrade hw q p] at ht₁
          have hqp_imp : 𝕄.mul q p = 𝕄.zero → q = 𝕄.zero := by
            intro hqp0
            have h1 : 𝕄.le (𝕄.mul q (𝕄.mul (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 q)) p))
                (𝕄.mul q (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 q))) :=
              𝕄.mul_mono_right q hcond
            rw [← 𝕄.mul_assoc, Mode.mul_toGrade_ofGrade, hqp0] at h1
            exact hw.zero_le_eq_zero h1
          let δ₁' := Conₘ.scale 𝕄 (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 q)) δ₁
          have ht₁' : Usage 𝕄 δ₁' (Mode.ofGrade 𝕄 q) t₁ := Usage.ofGrade_scale_self ht₁ hqp_imp
          refine ⟨γ, δ₁', η, hH, ht₁', hS, ?_⟩
          simp only [Conₘ.scale_zero, Conₘ.add_zero] at hbound
          have hscale_δ₁' : Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δ₁') = Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δ₁) := by
            rw [Conₘ.wk_scale, ← Conₘ.scale_assoc, Mode.mul_toGrade_ofGrade]
          rw [hscale_δ₁']
          have hmeet_le : Conₘ.le 𝕄 δ (Conₘ.scale 𝕄 p δ₁) :=
            Conₘ.le_trans 𝕄 hδ_le (fun x ↦ 𝕄.meet_le_left _ _)
          have hqp_le_q : 𝕄.le (𝕄.mul q p) q := by
            have h1 := 𝕄.mul_mono_right q hcond
            rwa [← 𝕄.mul_assoc, Mode.mul_toGrade_ofGrade] at h1
          have hwk_le : Conₘ.le 𝕄 (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δ))
              (Conₘ.scale 𝕄 q (Conₘ.wk 𝕄 ρ δ₁)) := by
            have h1 := Conₘ.scale_mono_right 𝕄 q (Conₘ.wk_mono 𝕄 ρ hmeet_le)
            rw [Conₘ.wk_scale, ← Conₘ.scale_assoc] at h1
            exact Conₘ.le_trans 𝕄 h1 (Conₘ.scale_mono 𝕄 hqp_le_q (Conₘ.le_refl 𝕄 _))
          exact Conₘ.le_trans 𝕄 hbound (Conₘ.add_mono 𝕄 hwk_le (Conₘ.le_refl 𝕄 η))
  | @prodStrongₕ₂ H p t₁ t₂ ρ S =>
    let q := Stack.mult 𝕄 nr₂ S
    cases hS_all with
    | @cons η _ _ _ hcExt hS =>
      cases hcExt with
      | of_contUsage hc =>
        cases hc with
        | sndₑ =>
          simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one] at ht hbound
          rcases Usage.inv_prodStrong ht with ⟨δ₁, δ₂, _, ht₂, hδ_le⟩
          refine ⟨γ, δ₂, η, hH, ht₂, hS, ?_⟩
          simp only [Conₘ.scale_zero, Conₘ.add_zero] at hbound
          have hmeet_le : Conₘ.le 𝕄 δ δ₂ :=
            Conₘ.le_trans 𝕄 hδ_le (fun x ↦ 𝕄.meet_le_right _ _)
          exact Conₘ.le_trans 𝕄 hbound
            (Conₘ.add_mono 𝕄 (Conₘ.scale_mono_right 𝕄 q (Conₘ.wk_mono 𝕄 ρ hmeet_le))
              (Conₘ.le_refl 𝕄 η))
  | @prodWeakₕ H r p q₀ t₁ t₂ A u ρ ρ' S =>
    let q' := Stack.mult 𝕄 nr₂ S
    cases hS_all with
    | @cons η _ _ _ hcExt hS =>
      cases hcExt with
      | of_contUsage hc =>
        cases hc with
        | @prodrecₑ θ' _ _ _ _ _ _ _ _ hu hA =>
          simp only [Stack.mult_cons, Cont.mult] at ht hbound
          rcases Usage.inv_prodWeak ht with ⟨δ₁, δ₂, ht₁, ht₂, hδ_le⟩
          rw [Mode.scale_ofGrade hw (𝕄.mul q' r) p] at ht₁
          have hγ_le : Conₘ.le 𝕄 γ
              (Conₘ.add 𝕄
                (Conₘ.add 𝕄 (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ')))
                  (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 ρ δ₂)))
                (Conₘ.scale 𝕄 (𝕄.mul (𝕄.mul q' r) p) (Conₘ.wk 𝕄 ρ δ₁))) := by
            have h1 : Conₘ.le 𝕄 γ
                (Conₘ.add 𝕄 (Conₘ.scale 𝕄 (𝕄.mul q' r)
                  (Conₘ.wk 𝕄 ρ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 p δ₁) δ₂)))
                  (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ')))) :=
              Conₘ.le_trans 𝕄 hbound
                (Conₘ.add_mono 𝕄
                  (Conₘ.scale_mono_right 𝕄 (𝕄.mul q' r) (Conₘ.wk_mono 𝕄 ρ hδ_le))
                  (Conₘ.le_refl 𝕄 _))
            have heq : Conₘ.add 𝕄 (Conₘ.scale 𝕄 (𝕄.mul q' r)
                (Conₘ.wk 𝕄 ρ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 p δ₁) δ₂)))
                (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ')))=
                Conₘ.add 𝕄
                  (Conₘ.add 𝕄 (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ')))
                    (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 ρ δ₂)))
                  (Conₘ.scale 𝕄 (𝕄.mul (𝕄.mul q' r) p) (Conₘ.wk 𝕄 ρ δ₁)) := by
              rw [Conₘ.wk_add, Conₘ.wk_scale, Conₘ.scale_add_distrib, ← Conₘ.scale_assoc,
                Conₘ.add_comm 𝕄 _ (Conₘ.add 𝕄 η _),
                Conₘ.add_comm 𝕄 (Conₘ.scale 𝕄 (𝕄.mul (𝕄.mul q' r) p) _) _,
                Conₘ.add_assoc, ← Conₘ.add_assoc, ← Conₘ.add_assoc]
            rw [← heq]
            exact h1
          have hH₁ : HeapUsage 𝕄
              (Conₘ.cons
                (Conₘ.add 𝕄 (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ')))
                  (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 ρ δ₂)))
                (𝕄.mul (𝕄.mul q' r) p))
              (.cons H (𝕄.mul (𝕄.mul q' r) p) ⟨t₁, ρ⟩) :=
            .cons (.sub hH hγ_le) ht₁
          have hH₁_sub : HeapUsage 𝕄
              (Conₘ.add 𝕄
                (Conₘ.cons (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ')))
                  (𝕄.mul (𝕄.mul q' r) p))
                (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 (.step ρ) δ₂)))
              (.cons H (𝕄.mul (𝕄.mul q' r) p) ⟨t₁, ρ⟩) := by
            have heq : Conₘ.add 𝕄
                (Conₘ.cons (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ')))
                  (𝕄.mul (𝕄.mul q' r) p))
                (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 (.step ρ) δ₂)) =
                Conₘ.cons
                  (Conₘ.add 𝕄 (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ')))
                    (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 ρ δ₂)))
                  (𝕄.mul (𝕄.mul q' r) p) := by
              funext z; cases z <;> simp [Conₘ.add, Conₘ.cons, Conₘ.scale, Conₘ.wk, 𝕄.mul_zero, 𝕄.add_zero]
            rw [heq]
            exact hH₁
          have hH₂ : HeapUsage 𝕄
              (Conₘ.cons
                (Conₘ.cons (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ')))
                  (𝕄.mul (𝕄.mul q' r) p))
                (𝕄.mul q' r))
              (.cons (.cons H (𝕄.mul (𝕄.mul q' r) p) ⟨t₁, ρ⟩) (𝕄.mul q' r) ⟨t₂, .step ρ⟩) :=
            .cons hH₁_sub ht₂
          have happ : Usage 𝕄
              (Conₘ.cons (Conₘ.cons θ' (𝕄.mul (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 q')) (𝕄.mul r p)))
                (𝕄.mul (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 q')) r))
              (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (Stack.wk2 S)))
              (.app r (.app (𝕄.mul r p) (GTerm.wk (.step (.step .id)) u) (.var 1)) (.var 0)) := by
            rw [Stack.mult_wk2]
            exact Usage.curried_app2 hu
          refine ⟨_, _, _, hH₂, happ, hS.wk (.step (.step .id)), ?_⟩
          rw [Stack.mult_wk2]
          intro z
          cases z with
          | zero =>
            dsimp only [q']
            simp only [Conₘ.cons, Conₘ.add, Conₘ.scale, Conₘ.wk, Conₘ.head, 𝕄.add_zero,
              ← 𝕄.mul_assoc, Mode.mul_toGrade_ofGrade]
            exact 𝕄.le_refl _
          | succ z =>
            cases z with
            | zero =>
              dsimp only [q']
              simp only [Conₘ.cons, Conₘ.add, Conₘ.scale, Conₘ.wk, Conₘ.tail, Conₘ.head,
                𝕄.add_zero, ← 𝕄.mul_assoc, Mode.mul_toGrade_ofGrade]
              exact 𝕄.le_refl _
            | succ z =>
              simp only [Conₘ.cons, Conₘ.add, Conₘ.scale, Conₘ.wk]
              rw [𝕄.add_comm]
              exact 𝕄.le_refl _
  | @zeroₕ H p q₀ r A z s ρ ρ' S =>
    let q' := Stack.mult 𝕄 nr₂ S
    cases hS_all with
    | @cons η _ _ _ hcExt hS =>
      cases hcExt with
      | of_contUsage hc =>
        cases hc with
        | @natrecₑ γz δs θA χ _ _ _ _ _ _ _ _ hz _ _ hχ1 _ =>
          simp only [Stack.mult_cons, Cont.mult] at ht hbound
          have hδ0 := Usage.inv_zero ht
          refine ⟨γ, γz, η, hH, hz, hS, ?_⟩
          have h1 : Conₘ.le 𝕄 (Conₘ.scale 𝕄 (𝕄.mul q' (nr₂ p r)) (Conₘ.wk 𝕄 ρ δ)) (Conₘ.zero 𝕄) := by
            have hs0 := Conₘ.scale_mono_right 𝕄 (𝕄.mul q' (nr₂ p r)) (Conₘ.wk_mono 𝕄 ρ hδ0)
            rwa [Conₘ.wk_zero, Conₘ.scale_zero] at hs0
          have h2 : Conₘ.le 𝕄 γ (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' χ))) := by
            have hsum := Conₘ.add_mono 𝕄 h1
              (Conₘ.le_refl 𝕄 (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' χ))))
            rw [Conₘ.zero_add] at hsum
            exact Conₘ.le_trans 𝕄 hbound hsum
          have h3 : Conₘ.le 𝕄 (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' χ)))
              (Conₘ.add 𝕄 (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' γz)) η) := by
            rw [Conₘ.add_comm 𝕄 η]
            exact Conₘ.add_mono 𝕄 (Conₘ.scale_mono_right 𝕄 q' (Conₘ.wk_mono 𝕄 ρ' hχ1))
              (Conₘ.le_refl 𝕄 η)
          exact Conₘ.le_trans 𝕄 h2 h3
  | @sucₕ H p q₀ r t A z s ρ ρ' S =>
    let q' := Stack.mult 𝕄 nr₂ S
    let p' := nr₂ p r
    cases hS_all with
    | @cons η _ _ _ hcExt hS =>
      cases hcExt with
      | of_contUsage hc =>
        cases hc with
        | @natrecₑ γz δs θA χ _ _ _ _ _ _ _ _ hz hs hA hχ1 hχ2 =>
          simp only [Stack.mult_cons, Cont.mult] at ht hbound
          have ht_pred : Usage 𝕄 δ (Mode.ofGrade 𝕄 (𝕄.mul q' p')) t := Usage.inv_succ ht
          let m := Mode.ofGrade 𝕄 q'
          have hnr_body : Usage 𝕄 (Conₘ.cons χ (𝕄.mul p' (Mode.toGrade 𝕄 m))) m
              (.natrec p q₀ r (GTerm.wk (.lift (.step .id)) A) (GTerm.wk1 z) (GTerm.wk1 s) (.var 0)) := by
            have hz1 : Usage 𝕄 (Conₘ.cons γz 𝕄.zero) m (GTerm.wk1 z) := Usage.wkUsage (.step .id) hz
            have hs1 : Usage 𝕄 (Conₘ.cons δs 𝕄.zero) m (GTerm.wk1 s) := Usage.wkUsage (.step .id) hs
            have hn0 : Usage 𝕄 (Conₘ.single 𝕄 0 (Mode.toGrade 𝕄 m)) m (.var 0) := .var
            have hA1 : Usage 𝕄 (Conₘ.cons (Conₘ.cons θA 𝕄.zero) 𝕄.zero) .zeroMode
                (GTerm.wk (.lift (.step .id)) A) := Usage.wkUsage (.lift (.step .id)) hA
            have hχ1' : Conₘ.le 𝕄 (Conₘ.cons χ 𝕄.zero) (Conₘ.cons γz 𝕄.zero) :=
              Conₘ.cons_le_cons 𝕄 hχ1 (𝕄.le_refl 𝕄.zero)
            have hχ2' : Conₘ.le 𝕄 (Conₘ.cons χ 𝕄.zero)
                (Conₘ.add 𝕄 (Conₘ.cons δs 𝕄.zero) (Conₘ.scale 𝕄 r (Conₘ.cons χ 𝕄.zero))) := by
              rw [Conₘ.cons_scale, 𝕄.mul_zero, Conₘ.cons_add, 𝕄.add_zero]
              exact Conₘ.cons_le_cons 𝕄 hχ2 (𝕄.le_refl 𝕄.zero)
            have hfix := Usage.natrec_fix (q := q₀) hz1 hs1 hn0 hA1 (hnr.le_one p r)
              (𝕄.mul_mono_right (Mode.toGrade 𝕄 m) (hnr.le_step p r)) hχ1' hχ2'
            have heq : Conₘ.add 𝕄 (Conₘ.scale 𝕄 p' (Conₘ.single 𝕄 0 (Mode.toGrade 𝕄 m)))
                (Conₘ.cons χ 𝕄.zero) = Conₘ.cons χ (𝕄.mul p' (Mode.toGrade 𝕄 m)) := by
              rw [Conₘ.single_zero, Conₘ.cons_scale, Conₘ.scale_zero, Conₘ.cons_add,
                Conₘ.zero_add, 𝕄.add_zero]
            rwa [heq] at hfix
          let δ_nr := Conₘ.scale 𝕄 (Mode.toGrade 𝕄 (Mode.ofGrade 𝕄 (𝕄.mul q' r)))
            (Conₘ.cons χ (𝕄.mul p' (Mode.toGrade 𝕄 m)))
          have hnr_body' : Usage 𝕄 δ_nr (Mode.ofGrade 𝕄 (𝕄.mul q' r))
              (.natrec p q₀ r (GTerm.wk (.lift (.step .id)) A) (GTerm.wk1 z) (GTerm.wk1 s) (.var 0)) := by
            apply Usage.ofGrade_scale_self hnr_body
            intro hq0
            rw [hq0, 𝕄.zero_mul]
          have hscale_nr : Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 (.lift ρ') δ_nr) =
              Conₘ.cons (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 ρ' χ))
                (𝕄.mul (𝕄.mul q' r) p') := by
            rw [Conₘ.wk_scale, ← Conₘ.scale_assoc, Mode.mul_toGrade_ofGrade]
            have hwk_lift : Conₘ.wk 𝕄 (.lift ρ') (Conₘ.cons χ (𝕄.mul p' (Mode.toGrade 𝕄 m))) =
                Conₘ.cons (Conₘ.wk 𝕄 ρ' χ) (𝕄.mul p' (Mode.toGrade 𝕄 m)) := rfl
            rw [hwk_lift, Conₘ.cons_scale]
            congr 1
            have hm_comm : 𝕄.mul p' (Mode.toGrade 𝕄 m) = 𝕄.mul (Mode.toGrade 𝕄 m) p' :=
              (Usage.toGrade_mul_comm m p').symm
            rw [hm_comm, ← 𝕄.mul_assoc, 𝕄.mul_assoc q' r (Mode.toGrade 𝕄 m),
              ← Usage.toGrade_mul_comm m r, ← 𝕄.mul_assoc q' (Mode.toGrade 𝕄 m) r,
              Mode.mul_toGrade_ofGrade]
          have hγ_le : Conₘ.le 𝕄 γ
              (Conₘ.add 𝕄 (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' χ)))
                (Conₘ.scale 𝕄 (𝕄.mul q' p') (Conₘ.wk 𝕄 ρ δ))) := by
            rw [Conₘ.add_comm 𝕄 _ (Conₘ.scale 𝕄 (𝕄.mul q' p') _)]
            exact hbound
          have hH₁ : HeapUsage 𝕄
              (Conₘ.cons (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' χ))) (𝕄.mul q' p'))
              (.cons H (𝕄.mul q' p') ⟨t, ρ⟩) :=
            .cons (.sub hH hγ_le) ht_pred
          have hH₁_sub : HeapUsage 𝕄
              (Conₘ.add 𝕄 (Conₘ.cons (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' δs))) (𝕄.mul q' p))
                (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 (.lift ρ') δ_nr)))
              (.cons H (𝕄.mul q' p') ⟨t, ρ⟩) := by
            rw [hscale_nr, Conₘ.cons_add]
            apply HeapUsage.sub hH₁
            refine Conₘ.cons_le_cons 𝕄 ?_ ?_
            · have hχ_step : Conₘ.le 𝕄 (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' χ))
                  (Conₘ.add 𝕄 (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' δs))
                    (Conₘ.scale 𝕄 (𝕄.mul q' r) (Conₘ.wk 𝕄 ρ' χ))) := by
                have h1 := Conₘ.scale_mono_right 𝕄 q' (Conₘ.wk_mono 𝕄 ρ' hχ2)
                rwa [Conₘ.wk_add, Conₘ.wk_scale, Conₘ.scale_add_distrib, ← Conₘ.scale_assoc] at h1
              rw [Conₘ.add_assoc]
              exact Conₘ.add_mono 𝕄 (Conₘ.le_refl 𝕄 η) hχ_step
            · have h1 := 𝕄.mul_mono_right q' (hnr.le_step p r)
              rwa [𝕄.left_distrib, ← 𝕄.mul_assoc] at h1
          have hH₂ : HeapUsage 𝕄
              (Conₘ.cons (Conₘ.cons (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' δs))) (𝕄.mul q' p))
                (𝕄.mul q' r))
              (.cons (.cons H (𝕄.mul q' p') ⟨t, ρ⟩) (𝕄.mul q' r)
                ⟨.natrec p q₀ r (GTerm.wk (.lift (.step .id)) A) (GTerm.wk1 z) (GTerm.wk1 s) (.var 0),
                  .lift ρ'⟩) :=
            .cons hH₁_sub hnr_body'
          have happ : Usage 𝕄
              (Conₘ.cons (Conₘ.cons δs (𝕄.mul (Mode.toGrade 𝕄 m) p))
                (𝕄.mul (Mode.toGrade 𝕄 m) r))
              (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (Stack.wk2 S)))
              (.app r (.app p (GTerm.wk (.step (.step .id)) s) (.var 1)) (.var 0)) := by
            rw [Stack.mult_wk2]
            exact Usage.curried_app2 hs
          refine ⟨_, _, _, hH₂, happ, hS.wk (.step (.step .id)), ?_⟩
          rw [Stack.mult_wk2]
          intro z₀
          cases z₀ with
          | zero =>
            dsimp only [q', m]
            simp only [Conₘ.cons, Conₘ.add, Conₘ.scale, Conₘ.wk, Conₘ.head, 𝕄.add_zero,
              ← 𝕄.mul_assoc, Mode.mul_toGrade_ofGrade]
            exact 𝕄.le_refl _
          | succ z₀ =>
            cases z₀ with
            | zero =>
              dsimp only [q', m]
              simp only [Conₘ.cons, Conₘ.add, Conₘ.scale, Conₘ.wk, Conₘ.tail, Conₘ.head,
                𝕄.add_zero, ← 𝕄.mul_assoc, Mode.mul_toGrade_ofGrade]
              exact 𝕄.le_refl _
            | succ z₀ =>
              simp only [Conₘ.cons, Conₘ.add, Conₘ.scale, Conₘ.wk]
              rw [𝕄.add_comm]
              exact 𝕄.le_refl _
  | @starWeakₕ H p q₀ A u ρ ρ' S =>
    let q' := Stack.mult 𝕄 nr₂ S
    cases hS_all with
    | @cons η _ _ _ hcExt hS =>
      cases hcExt with
      | of_contUsage hc =>
        cases hc with
        | @unitrecₑ θ' _ _ _ _ _ _ _ hu _ =>
          simp only [Stack.mult_cons, Cont.mult] at ht hbound
          have hδ0 := Usage.inv_star ht
          refine ⟨γ, θ', η, hH, hu, hS, ?_⟩
          have h1 : Conₘ.le 𝕄 (Conₘ.scale 𝕄 (𝕄.mul q' p) (Conₘ.wk 𝕄 ρ δ)) (Conₘ.zero 𝕄) := by
            have hs0 := Conₘ.scale_mono_right 𝕄 (𝕄.mul q' p) (Conₘ.wk_mono 𝕄 ρ hδ0)
            rwa [Conₘ.wk_zero, Conₘ.scale_zero] at hs0
          have h2 : Conₘ.le 𝕄 γ (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ'))) := by
            have hsum := Conₘ.add_mono 𝕄 h1
              (Conₘ.le_refl 𝕄 (Conₘ.add 𝕄 η (Conₘ.scale 𝕄 q' (Conₘ.wk 𝕄 ρ' θ'))))
            rw [Conₘ.zero_add] at hsum
            exact Conₘ.le_trans 𝕄 hbound hsum
          rw [Conₘ.add_comm 𝕄 _ η]
          exact h2

theorem usageExt_pres_numStep {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {s s' : State M} (hs : StateUsageExt 𝕄 nr₂ s) (hstep : NumStep s s') :
    StateUsageExt 𝕄 nr₂ s' := by
  rcases hs with ⟨γ, δ, η_all, hH, ht, hS_all, hbound⟩
  cases hstep with
  | @sucₕ H t ρ ℓ _ =>
    have ht' : Usage 𝕄 δ (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ (.sucₑ :: Stack.sucs ℓ))) t := by
      simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one]
      exact Usage.inv_succ ht
    refine ⟨γ, δ, _, hH, ht', .cons .sucₑ hS_all, ?_⟩
    simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one, Conₘ.scale_zero, Conₘ.add_zero]
    exact hbound
  | @numₕ H t ρ S _ =>
    cases hS_all with
    | @cons η θ _ _ hcExt hS =>
      cases hcExt with
      | of_contUsage hc => exact False.elim (ContUsage.inv_sucₑ hc)
      | sucₑ =>
        simp only [Stack.mult_cons, Cont.mult, 𝕄.mul_one, Conₘ.scale_zero, Conₘ.add_zero] at ht hbound
        exact ⟨γ, δ, η, hH, .succ ht, hS, hbound⟩

theorem usageExt_pres_heapNumStep {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s s' : State M} (hs : StateUsageExt 𝕄 nr₂ s) (hstep : HeapNumStep 𝕄 nr₂ s s') :
    StateUsageExt 𝕄 nr₂ s' := by
  cases hstep with
  | elimStep he => exact usageExt_pres_trackElimStep hw hnr hs he
  | valStep hv => exact usageExt_pres_valStep hw hnr hs hv
  | numStep hn => exact usageExt_pres_numStep hs hn

theorem usageExt_pres_heapNumStar {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s s' : State M} (hs : StateUsageExt 𝕄 nr₂ s) (hstar : HeapNumStar 𝕄 nr₂ s s') :
    StateUsageExt 𝕄 nr₂ s' := by
  induction hstar with
  | refl _ => exact hs
  | step hstep _ ih => exact ih (usageExt_pres_heapNumStep hw hnr hs hstep)

/-- **M3 Theorem 4.3 for Full Numeral Reduction (`▸-↠*` with empty final stack)**:
    if `s` is well-resourced (`StateUsage 𝕄 nr₂ s`) and evaluates via `↠*` to a state
    `⟨ H , t , ρ , [] ⟩` with an empty stack, then `StateUsage 𝕄 nr₂ ⟨ H , t , ρ , [] ⟩` holds. -/
theorem usage_pres_numStar_empty {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s : State M} {H : Heap M} {t : GTerm M} {ρ : Wk}
    (hs : StateUsage 𝕄 nr₂ s) (hstar : HeapNumStar 𝕄 nr₂ s ⟨H, t, ρ, []⟩) :
    StateUsage 𝕄 nr₂ ⟨H, t, ρ, []⟩ :=
  StateUsage.ofExt_empty (usageExt_pres_heapNumStar hw hnr hs.toExt hstar)

/-! ## 5. Bisimilarity and Unfolding Soundness (`Graded.Heap.Reduction.Properties`, M3 Theorems 4.6–4.10) -/

/-- Equivalence of machine states up to heap grades (`_~ₛ_` in M3 Section 4.3). -/
def StateSameShape {M : Type} (s₁ s₂ : State M) : Prop :=
  HeapSameShape s₁.heap s₂.heap ∧ s₁.head = s₂.head ∧ s₁.env = s₂.env ∧ s₁.stack = s₂.stack

namespace StateSameShape

variable {M : Type}

@[refl] theorem refl (s : State M) : StateSameShape s s :=
  ⟨HeapSameShape.refl s.heap, rfl, rfl, rfl⟩

theorem symm {s₁ s₂ : State M} (h : StateSameShape s₁ s₂) : StateSameShape s₂ s₁ :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem trans {s₁ s₂ s₃ : State M}
    (h₁ : StateSameShape s₁ s₂) (h₂ : StateSameShape s₂ s₃) : StateSameShape s₁ s₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1, h₁.2.2.2.trans h₂.2.2.2⟩

theorem unfoldState_eq {s₁ s₂ : State M} (h : StateSameShape s₁ s₂) :
    unfoldState s₁ = unfoldState s₂ := by
  rcases s₁ with ⟨H₁, t₁, ρ₁, S₁⟩
  rcases s₂ with ⟨H₂, t₂, ρ₂, S₂⟩
  rcases h with ⟨hH, rfl, rfl, rfl⟩
  simp [unfoldState, heapSameShape_toSubstₕ hH]

end StateSameShape

/-- **M3 Theorem 4.6a (`⇾→⇢` in `Graded.Heap.Reduction.Properties`)**:
    tracked WHNF transitions map to untracked transitions on states of the same shape. -/
theorem tracked_to_untracked_step {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {s₁ s₂ u₁ : State M} (hshape : StateSameShape s₁ u₁)
    (hstep : HeapStep 𝕄 nr₂ s₁ s₂) :
    ∃ u₂ : State M, HeapStepUntracked 𝕄 nr₂ u₁ u₂ ∧ StateSameShape s₂ u₂ := by
  rcases s₁ with ⟨H₁, t₁, ρ₁, S₁⟩
  rcases u₁ with ⟨H₁', t₁', ρ₁', S₁'⟩
  rcases hshape with ⟨hH, ht, hρ, hS⟩
  dsimp only at hH ht hρ hS
  subst ht; subst hρ; subst hS
  cases hstep with
  | elimStep he =>
    cases he with
    | @var _ H₂ x t _ ρ' _ hlookup =>
      have hl_untracked : HeapLookupUntracked H₁' (wkVar ρ₁ x) ⟨t, ρ'⟩ :=
        hH.lookupUntracked hlookup.toUntracked
      exact ⟨⟨H₁', t, ρ', S₁⟩, .elimStep (.var hl_untracked),
        ⟨(hlookup.sameShape.symm).trans hH, rfl, rfl, rfl⟩⟩
    | elim helim =>
      cases helim with
      | appₕ =>
        exact ⟨_, .elimStep (.elim .appₕ), ⟨hH, rfl, rfl, rfl⟩⟩
      | fstₕ =>
        exact ⟨_, .elimStep (.elim .fstₕ), ⟨hH, rfl, rfl, rfl⟩⟩
      | sndₕ =>
        exact ⟨_, .elimStep (.elim .sndₕ), ⟨hH, rfl, rfl, rfl⟩⟩
      | prodrecₕ =>
        exact ⟨_, .elimStep (.elim .prodrecₕ), ⟨hH, rfl, rfl, rfl⟩⟩
      | unitrecₕ =>
        exact ⟨_, .elimStep (.elim .unitrecₕ), ⟨hH, rfl, rfl, rfl⟩⟩
      | natrecₕ =>
        exact ⟨_, .elimStep (.elim .natrecₕ), ⟨hH, rfl, rfl, rfl⟩⟩
  | valStep hv =>
    cases hv with
    | lamₕ =>
      exact ⟨_, .valStep .lamₕ, ⟨.cons _ hH, rfl, rfl, rfl⟩⟩
    | prodStrongₕ₁ =>
      exact ⟨_, .valStep .prodStrongₕ₁, ⟨hH, rfl, rfl, rfl⟩⟩
    | prodStrongₕ₂ =>
      exact ⟨_, .valStep .prodStrongₕ₂, ⟨hH, rfl, rfl, rfl⟩⟩
    | prodWeakₕ =>
      exact ⟨_, .valStep .prodWeakₕ, ⟨.cons _ (.cons _ hH), rfl, rfl, rfl⟩⟩
    | zeroₕ =>
      exact ⟨_, .valStep .zeroₕ, ⟨hH, rfl, rfl, rfl⟩⟩
    | sucₕ =>
      exact ⟨_, .valStep .sucₕ, ⟨.cons _ (.cons _ hH), rfl, rfl, rfl⟩⟩
    | starWeakₕ =>
      exact ⟨_, .valStep .starWeakₕ, ⟨hH, rfl, rfl, rfl⟩⟩

/-- **M3 Theorem 4.6a Multi-step (`⇾*→⇢*` in `Graded.Heap.Reduction.Properties`)**:
    tracked multi-step WHNF evaluation maps to untracked multi-step evaluation. -/
theorem tracked_to_untracked_star {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {s₁ s₂ u₁ : State M} (hshape : StateSameShape s₁ u₁)
    (hstar : HeapStar 𝕄 nr₂ s₁ s₂) :
    ∃ u₂ : State M, HeapStarUntracked 𝕄 nr₂ u₁ u₂ ∧ StateSameShape s₂ u₂ := by
  induction hstar generalizing u₁ with
  | refl _ => exact ⟨u₁, .refl u₁, hshape⟩
  | step hs _ ih =>
    rcases tracked_to_untracked_step hshape hs with ⟨u_mid, hs_u, hshape_mid⟩
    rcases ih hshape_mid with ⟨u₂, hstar_u, hshape₂⟩
    exact ⟨u₂, .step hs_u hstar_u, hshape₂⟩

/-- **M3 Theorem 4.6b (`⇢→⇾` in `Graded.Heap.Reduction.Properties`)**:
    under `SupportsSubtraction`, `HasWellBehavedZero`, and `NatrecMultFn`, any untracked step
    from a state shape-equivalent to a well-resourced state `s₁` lifts to a tracked step
    preserving `StateUsage`. -/
theorem untracked_to_tracked_step {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hsub : 𝕄.SupportsSubtraction) (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s₁ u₁ u₂ : State M} (hs₁ : StateUsage 𝕄 nr₂ s₁)
    (hshape : StateSameShape s₁ u₁)
    (hstep : HeapStepUntracked 𝕄 nr₂ u₁ u₂) :
    ∃ s₂ : State M, HeapStep 𝕄 nr₂ s₁ s₂ ∧ StateUsage 𝕄 nr₂ s₂ ∧ StateSameShape s₂ u₂ := by
  rcases s₁ with ⟨H₁, t₁, ρ₁, S₁⟩
  rcases u₁ with ⟨H₁', t₁', ρ₁', S₁'⟩
  rcases hshape with ⟨hH, ht, hρ, hS⟩
  dsimp only at hH ht hρ hS
  subst ht; subst hρ; subst hS
  cases hstep with
  | elimStep he =>
    cases he with
    | @var _ x t _ ρ' _ hl_u =>
      have hl₁ : HeapLookupUntracked H₁ (wkVar ρ₁ x) ⟨t, ρ'⟩ :=
        hH.symm.lookupUntracked hl_u
      rcases state_lookup_succeeds hsub hl₁ hs₁ with ⟨H₂, hl_tr⟩
      have hstep_tr : HeapStep 𝕄 nr₂ ⟨H₁, .var x, ρ₁, S₁⟩ ⟨H₂, t, ρ', S₁⟩ :=
        .elimStep (.var hl_tr)
      exact ⟨⟨H₂, t, ρ', S₁⟩, hstep_tr, usage_pres_step hw hnr hs₁ hstep_tr,
        ⟨(hl_tr.sameShape.symm).trans hH, rfl, rfl, rfl⟩⟩
    | elim helim =>
      cases helim with
      | @appₕ _ p t u _ _ =>
        have hstep_tr : HeapStep 𝕄 nr₂ ⟨H₁, .app p t u, ρ₁, S₁⟩ _ := .elimStep (.elim .appₕ)
        exact ⟨_, hstep_tr, usage_pres_step hw hnr hs₁ hstep_tr, ⟨hH, rfl, rfl, rfl⟩⟩
      | @fstₕ _ p t _ _ =>
        have hstep_tr : HeapStep 𝕄 nr₂ ⟨H₁, .fst p t, ρ₁, S₁⟩ _ := .elimStep (.elim .fstₕ)
        exact ⟨_, hstep_tr, usage_pres_step hw hnr hs₁ hstep_tr, ⟨hH, rfl, rfl, rfl⟩⟩
      | @sndₕ _ p t _ _ =>
        have hstep_tr : HeapStep 𝕄 nr₂ ⟨H₁, .snd p t, ρ₁, S₁⟩ _ := .elimStep (.elim .sndₕ)
        exact ⟨_, hstep_tr, usage_pres_step hw hnr hs₁ hstep_tr, ⟨hH, rfl, rfl, rfl⟩⟩
      | @prodrecₕ _ r p q A t u _ _ =>
        have hstep_tr : HeapStep 𝕄 nr₂ ⟨H₁, .prodrec r p q A t u, ρ₁, S₁⟩ _ := .elimStep (.elim .prodrecₕ)
        exact ⟨_, hstep_tr, usage_pres_step hw hnr hs₁ hstep_tr, ⟨hH, rfl, rfl, rfl⟩⟩
      | @unitrecₕ _ p q A t u _ _ =>
        have hstep_tr : HeapStep 𝕄 nr₂ ⟨H₁, .unitrec p q A t u, ρ₁, S₁⟩ _ := .elimStep (.elim .unitrecₕ)
        exact ⟨_, hstep_tr, usage_pres_step hw hnr hs₁ hstep_tr, ⟨hH, rfl, rfl, rfl⟩⟩
      | @natrecₕ _ p q r A z s t _ _ =>
        have hstep_tr : HeapStep 𝕄 nr₂ ⟨H₁, .natrec p q r A z s t, ρ₁, S₁⟩ _ := .elimStep (.elim .natrecₕ)
        exact ⟨_, hstep_tr, usage_pres_step hw hnr hs₁ hstep_tr, ⟨hH, rfl, rfl, rfl⟩⟩
  | valStep hv =>
    cases hv with
    | @lamₕ _ p t u _ ρ' S =>
      have hstep_tr : HeapStep 𝕄 nr₂ ⟨H₁, .lam p t, ρ₁, .appₑ p u ρ' :: S⟩ _ := .valStep .lamₕ
      exact ⟨_, hstep_tr, usage_pres_step hw hnr hs₁ hstep_tr, ⟨.cons _ hH, rfl, rfl, rfl⟩⟩
    | @prodStrongₕ₁ _ p t₁ t₂ _ S =>
      have hstep_tr : HeapStep 𝕄 nr₂ ⟨H₁, .prod .strong p t₁ t₂, ρ₁, .fstₑ p :: S⟩ _ :=
        .valStep .prodStrongₕ₁
      exact ⟨_, hstep_tr, usage_pres_step hw hnr hs₁ hstep_tr, ⟨hH, rfl, rfl, rfl⟩⟩
    | @prodStrongₕ₂ _ p t₁ t₂ _ S =>
      have hstep_tr : HeapStep 𝕄 nr₂ ⟨H₁, .prod .strong p t₁ t₂, ρ₁, .sndₑ p :: S⟩ _ :=
        .valStep .prodStrongₕ₂
      exact ⟨_, hstep_tr, usage_pres_step hw hnr hs₁ hstep_tr, ⟨hH, rfl, rfl, rfl⟩⟩
    | @prodWeakₕ _ r p q t₁ t₂ A u _ ρ' S =>
      have hstep_tr : HeapStep 𝕄 nr₂ ⟨H₁, .prod .weak p t₁ t₂, ρ₁, .prodrecₑ r p q A u ρ' :: S⟩ _ :=
        .valStep .prodWeakₕ
      exact ⟨_, hstep_tr, usage_pres_step hw hnr hs₁ hstep_tr,
        ⟨.cons _ (.cons _ hH), rfl, rfl, rfl⟩⟩
    | @zeroₕ _ p q r A z s _ ρ' S =>
      have hstep_tr : HeapStep 𝕄 nr₂ ⟨H₁, .zero, ρ₁, .natrecₑ p q r A z s ρ' :: S⟩ _ :=
        .valStep .zeroₕ
      exact ⟨_, hstep_tr, usage_pres_step hw hnr hs₁ hstep_tr, ⟨hH, rfl, rfl, rfl⟩⟩
    | @sucₕ _ p q r t A z s _ ρ' S =>
      have hstep_tr : HeapStep 𝕄 nr₂ ⟨H₁, .succ t, ρ₁, .natrecₑ p q r A z s ρ' :: S⟩ _ :=
        .valStep .sucₕ
      exact ⟨_, hstep_tr, usage_pres_step hw hnr hs₁ hstep_tr,
        ⟨.cons _ (.cons _ hH), rfl, rfl, rfl⟩⟩
    | @starWeakₕ _ p q A u _ ρ' S =>
      have hstep_tr : HeapStep 𝕄 nr₂ ⟨H₁, .star, ρ₁, .unitrecₑ p q A u ρ' :: S⟩ _ :=
        .valStep .starWeakₕ
      exact ⟨_, hstep_tr, usage_pres_step hw hnr hs₁ hstep_tr, ⟨hH, rfl, rfl, rfl⟩⟩

/-- **M3 Theorem 4.6b Multi-step (`⇢*→⇾*` in `Graded.Heap.Reduction.Properties`)**:
    under `SupportsSubtraction`, `HasWellBehavedZero`, and `NatrecMultFn`, any untracked
    multi-step reduction from a well-resourced state lifts to a tracked multi-step reduction. -/
theorem untracked_to_tracked_star {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hsub : 𝕄.SupportsSubtraction) (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s₁ u₁ u₂ : State M} (hs₁ : StateUsage 𝕄 nr₂ s₁)
    (hshape : StateSameShape s₁ u₁)
    (hstar : HeapStarUntracked 𝕄 nr₂ u₁ u₂) :
    ∃ s₂ : State M, HeapStar 𝕄 nr₂ s₁ s₂ ∧ StateUsage 𝕄 nr₂ s₂ ∧ StateSameShape s₂ u₂ := by
  induction hstar generalizing s₁ with
  | refl _ => exact ⟨s₁, .refl s₁, hs₁, hshape⟩
  | step hs_u _ ih =>
    rcases untracked_to_tracked_step hsub hw hnr hs₁ hshape hs_u with
      ⟨s_mid, hs_tr, husage_mid, hshape_mid⟩
    rcases ih husage_mid hshape_mid with ⟨s₂, hstar_tr, husage₂, hshape₂⟩
    exact ⟨s₂, .step hs_tr hstar_tr, husage₂, hshape₂⟩

/-! ### Unfolding Soundness (`Graded.Heap.Reduction.Properties`, M3 Theorems 4.7–4.10) -/

theorem subst_consSubst_wk1 {M : Type} (σ : GTerm.GSubst M) (a u : GTerm M) :
    GTerm.subst (GTerm.consSubst σ a) (GTerm.wk1 u) = GTerm.subst σ u :=
  GTerm.subst_wk u

theorem subst_liftSubst_wk1 {M : Type} (σ : GTerm.GSubst M) (u : GTerm M) :
    GTerm.subst (GTerm.liftSubst σ) (GTerm.wk1 u) = GTerm.wk1 (GTerm.subst σ u) :=
  (GTerm.subst_wk u).trans (GTerm.wk_subst u).symm

theorem wk_step_eq_wk1_wk {M : Type} (ρ : Wk) (u : GTerm M) :
    GTerm.wk (.step ρ) u = GTerm.wk1 (GTerm.wk ρ u) := by
  unfold GTerm.wk1
  rw [GTerm.wk_comp (.step .id) ρ u]
  rfl

/-- Untracked lookup in `H` unfolds to the exact term bound in `toSubstₕ H`
    (`↦→toSubstₕ` in `Graded.Heap.Reduction.Properties`). -/
theorem HeapLookupUntracked.toSubstₕ_eq {M : Type} {H : Heap M} {y : Nat} {t : GTerm M} {ρ : Wk}
    (hl : HeapLookupUntracked H y ⟨t, ρ⟩) :
    toSubstₕ H y = GTerm.subst (toSubstₕ H) (GTerm.wk ρ t) := by
  generalize he : (⟨t, ρ⟩ : Entry M) = e₀ at hl
  induction hl generalizing t ρ with
  | @here H₀ p e₁ =>
    cases e₁ with
    | mk t₀ ρ₀ =>
      injection he with ht_eq hρ_eq
      subst ht_eq; subst hρ_eq
      simp only [toSubstₕ, GTerm.consSubst]
      rw [wk_step_eq_wk1_wk, subst_consSubst_wk1]
  | @there H₀ y₀ p e₁ e' _ ih =>
    cases e₁ with
    | mk t₀ ρ₀ =>
      cases e' with
      | mk u₀ ρ_u =>
        injection he with ht_eq hρ_eq
        subst ht_eq; subst hρ_eq
        simp only [toSubstₕ, GTerm.consSubst]
        rw [ih rfl, wk_step_eq_wk1_wk, subst_consSubst_wk1]
  | @thereDummy H₀ y₀ e₁ _ ih =>
    cases e₁ with
    | mk t₀ ρ₀ =>
      injection he with ht_eq hρ_eq
      subst ht_eq; subst hρ_eq
      simp only [toSubstₕ, GTerm.liftSubst]
      rw [ih rfl, wk_step_eq_wk1_wk, subst_liftSubst_wk1]

/-- Substituted continuation frame (`subst σ (unfoldCont c u) = substCont σ c (subst σ u)`). -/
def substCont {M : Type} (σ : GTerm.GSubst M) : Cont M → GTerm M → GTerm M
  | .appₑ p u ρ, v => .app p v (GTerm.subst σ (GTerm.wk ρ u))
  | .fstₑ p, v => .fst p v
  | .sndₑ p, v => .snd p v
  | .prodrecₑ r p q A u ρ, v =>
      .prodrec r p q (GTerm.subst (GTerm.liftSubst σ) (GTerm.wk (.lift ρ) A))
        v (GTerm.subst σ (GTerm.wk ρ u))
  | .unitrecₑ p q A u ρ, v =>
      .unitrec p q (GTerm.subst (GTerm.liftSubst σ) (GTerm.wk (.lift ρ) A))
        v (GTerm.subst σ (GTerm.wk ρ u))
  | .natrecₑ p q r A z s ρ, v =>
      .natrec p q r (GTerm.subst (GTerm.liftSubst σ) (GTerm.wk (.lift ρ) A))
        (GTerm.subst σ (GTerm.wk ρ z)) (GTerm.subst σ (GTerm.wk ρ s)) v
  | .sucₑ, v => .succ v

/-- Substituted continuation stack (`subst σ (unfoldStack S u) = substStack σ S (subst σ u)`). -/
def substStack {M : Type} (σ : GTerm.GSubst M) : Stack M → GTerm M → GTerm M
  | [], v => v
  | c :: S, v => substStack σ S (substCont σ c v)

@[simp] theorem subst_unfoldCont {M : Type} (σ : GTerm.GSubst M) (c : Cont M) (u : GTerm M) :
    GTerm.subst σ (unfoldCont c u) = substCont σ c (GTerm.subst σ u) := by
  cases c <;> rfl

@[simp] theorem subst_unfoldStack {M : Type} (σ : GTerm.GSubst M) (S : Stack M) (u : GTerm M) :
    GTerm.subst σ (unfoldStack S u) = substStack σ S (GTerm.subst σ u) := by
  induction S generalizing u with
  | nil => rfl
  | cons c S ih => rw [unfoldStack, ih, subst_unfoldCont, substStack]

theorem unfoldState_eq_substStack {M : Type} (s : State M) :
    unfoldState s = substStack (toSubstₕ s.heap) s.stack (GTerm.subst (toSubstₕ s.heap) (GTerm.wk s.env s.head)) :=
  subst_unfoldStack (toSubstₕ s.heap) s.stack (GTerm.wk s.env s.head)

@[simp] theorem substStack_append {M : Type} (σ : GTerm.GSubst M) (S₁ S₂ : Stack M) (v : GTerm M) :
    substStack σ (S₁ ++ S₂) v = substStack σ S₂ (substStack σ S₁ v) := by
  induction S₁ generalizing v with
  | nil => rfl
  | cons c S₁ ih => simp [substStack, ih]

theorem subst_wk_congr {M : Type} {σ₁ σ₂ : GTerm.GSubst M} {τ : Wk}
    (hσ : ∀ x, σ₁ (wkVar τ x) = σ₂ x) (u : GTerm M) :
    GTerm.subst σ₁ (GTerm.wk τ u) = GTerm.subst σ₂ u := by
  rw [GTerm.subst_wk]
  exact GTerm.substVar_to_subst hσ u

theorem subst_wk_wk_congr {M : Type} {σ₁ σ₂ : GTerm.GSubst M} {τ₁ τ₂ : Wk}
    (hσ : ∀ x, σ₁ (wkVar τ₁ x) = σ₂ (wkVar τ₂ x)) (u : GTerm M) :
    GTerm.subst σ₁ (GTerm.wk τ₁ u) = GTerm.subst σ₂ (GTerm.wk τ₂ u) := by
  rw [GTerm.subst_wk, GTerm.subst_wk]
  exact GTerm.substVar_to_subst hσ u

theorem subst_lift_wk_lift_congr {M : Type} {σ₁ σ₂ : GTerm.GSubst M} {τ : Wk}
    (hσ : ∀ x, σ₁ (wkVar τ x) = σ₂ x) (u : GTerm M) :
    GTerm.subst (GTerm.liftSubst σ₁) (GTerm.wk (.lift τ) u) =
      GTerm.subst (GTerm.liftSubst σ₂) u := by
  apply subst_wk_congr
  intro x
  cases x with
  | zero => rfl
  | succ x => exact congrArg GTerm.wk1 (hσ x)

theorem substCont_wk_congr {M : Type} {σ₁ σ₂ : GTerm.GSubst M} {τ : Wk}
    (hσ : ∀ x, σ₁ (wkVar τ x) = σ₂ x) (c : Cont M) (v : GTerm M) :
    substCont σ₁ (Cont.wk τ c) v = substCont σ₂ c v := by
  cases c with
  | appₑ p u ρ =>
    simp only [Cont.wk, substCont, ← GTerm.wk_comp τ ρ u, subst_wk_congr hσ]
  | fstₑ p => rfl
  | sndₑ p => rfl
  | prodrecₑ r p q A u ρ =>
    have hA : GTerm.wk (.lift (compWk τ ρ)) A = GTerm.wk (.lift τ) (GTerm.wk (.lift ρ) A) := by
      rw [GTerm.wk_comp (.lift τ) (.lift ρ) A]; rfl
    simp only [Cont.wk, substCont, hA, subst_lift_wk_lift_congr hσ,
      ← GTerm.wk_comp τ ρ u, subst_wk_congr hσ]
  | unitrecₑ p q A u ρ =>
    have hA : GTerm.wk (.lift (compWk τ ρ)) A = GTerm.wk (.lift τ) (GTerm.wk (.lift ρ) A) := by
      rw [GTerm.wk_comp (.lift τ) (.lift ρ) A]; rfl
    simp only [Cont.wk, substCont, hA, subst_lift_wk_lift_congr hσ,
      ← GTerm.wk_comp τ ρ u, subst_wk_congr hσ]
  | natrecₑ p q r A z s ρ =>
    have hA : GTerm.wk (.lift (compWk τ ρ)) A = GTerm.wk (.lift τ) (GTerm.wk (.lift ρ) A) := by
      rw [GTerm.wk_comp (.lift τ) (.lift ρ) A]; rfl
    simp only [Cont.wk, substCont, hA, subst_lift_wk_lift_congr hσ,
      ← GTerm.wk_comp τ ρ z, ← GTerm.wk_comp τ ρ s, subst_wk_congr hσ]
  | sucₑ => rfl

theorem substStack_wk_congr {M : Type} {σ₁ σ₂ : GTerm.GSubst M} {τ : Wk}
    (hσ : ∀ x, σ₁ (wkVar τ x) = σ₂ x) (S : Stack M) (v : GTerm M) :
    substStack σ₁ (Stack.wk τ S) v = substStack σ₂ S v := by
  induction S generalizing v with
  | nil => rfl
  | cons c S ih =>
    simp only [Stack.wk, substStack, substCont_wk_congr hσ, ih]

theorem substStack_wk1_cons {M : Type} (H : Heap M) (p : M) (e : Entry M)
    (S : Stack M) (v : GTerm M) :
    substStack (toSubstₕ (.cons H p e)) (Stack.wk1 S) v = substStack (toSubstₕ H) S v := by
  cases e
  exact substStack_wk_congr (fun _ ↦ rfl) S v

theorem substStack_wk2_cons2 {M : Type} (H : Heap M) (p₁ p₂ : M) (e₁ e₂ : Entry M)
    (S : Stack M) (v : GTerm M) :
    substStack (toSubstₕ (.cons (.cons H p₁ e₁) p₂ e₂)) (Stack.wk2 S) v =
      substStack (toSubstₕ H) S v := by
  cases e₁; cases e₂
  exact substStack_wk_congr (fun _ ↦ rfl) S v

/-- **M3 Lemma 4.7a (`⇒ₑ`-unfolding)**:
    `ElimStep` preserves `unfoldState` up to syntactic equality. -/
theorem unfold_elimStep {M : Type} {s₁ s₂ : State M} (h : ElimStep s₁ s₂) :
    unfoldState s₁ = unfoldState s₂ := by
  cases h <;> rfl

/-- **M3 Lemma 4.7b (`⇢ₑ`-unfolding)**:
    `UntrackElimStep` preserves `unfoldState` up to syntactic equality. -/
theorem unfold_untrackElimStep {M : Type} {s₁ s₂ : State M} (h : UntrackElimStep s₁ s₂) :
    unfoldState s₁ = unfoldState s₂ := by
  cases h with
  | elim he => exact unfold_elimStep he
  | @var H x t ρ ρ' S hl =>
    simp only [unfoldState_eq_substStack, GTerm.wk, GTerm.subst, hl.toSubstₕ_eq]

/-- **M3 Lemma 4.7c (`⇾ₑ`-unfolding)**:
    `TrackElimStep` preserves `unfoldState` up to syntactic equality. -/
theorem unfold_trackElimStep {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {s₁ s₂ : State M} (h : TrackElimStep 𝕄 nr₂ s₁ s₂) :
    unfoldState s₁ = unfoldState s₂ := by
  cases h with
  | elim he => exact unfold_elimStep he
  | @var H H' x t ρ ρ' S hl =>
    have hshape : toSubstₕ H' = toSubstₕ H := heapSameShape_toSubstₕ hl.sameShape.symm
    simp only [unfoldState_eq_substStack, hshape, GTerm.wk, GTerm.subst, hl.toUntracked.toSubstₕ_eq]

/-- **M3 Lemma 4.9a (`⇒ₙ`-unfolding)**:
    `NumStep` preserves `unfoldState` up to syntactic equality. -/
theorem unfold_numStep {M : Type} {s₁ s₂ : State M} (h : NumStep s₁ s₂) :
    unfoldState s₁ = unfoldState s₂ := by
  cases h <;> rfl

/-- Stack invariant stating that no `.sucₑ` frame occurs in `S`. -/
def NoSuc {M : Type} : Stack M → Prop
  | [] => True
  | c :: S => c ≠ .sucₑ ∧ NoSuc S

theorem NoSuc.wk {M : Type} (τ : Wk) {S : Stack M} (h : NoSuc S) :
    NoSuc (Stack.wk τ S) := by
  induction S with
  | nil => trivial
  | cons c S ih =>
    rcases h with ⟨hc, hS⟩
    refine ⟨?_, ih hS⟩
    cases c <;> simp [Cont.wk] at hc ⊢

theorem NoSuc.of_stackUsage {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {η : Conₘ M} {S : Stack M} (h : StackUsage 𝕄 nr₂ η S) : NoSuc S := by
  induction h with
  | nil => trivial
  | cons hc _ ih =>
    refine ⟨?_, ih⟩
    intro hsuc
    subst hsuc
    exact ContUsage.inv_sucₑ hc

theorem substCont_gstep {M : Type} {𝕄 : Modality M} (σ : GTerm.GSubst M)
    {c : Cont M} (hc : c ≠ .sucₑ) {v₁ v₂ : GTerm M} (hstep : GStep 𝕄 v₁ v₂) :
    GStep 𝕄 (substCont σ c v₁) (substCont σ c v₂) := by
  cases c with
  | appₑ _ _ _ => exact .app_subst hstep
  | fstₑ _ => exact .fst_subst hstep
  | sndₑ _ => exact .snd_subst hstep
  | prodrecₑ _ _ _ _ _ _ => exact .prodrec_subst hstep
  | unitrecₑ _ _ _ _ _ => exact .unitrec_subst hstep
  | natrecₑ _ _ _ _ _ _ _ => exact .natrec_subst hstep
  | sucₑ => exact False.elim (hc rfl)

theorem substStack_gstep {M : Type} {𝕄 : Modality M} (σ : GTerm.GSubst M)
    {S : Stack M} (hS : NoSuc S) {v₁ v₂ : GTerm M} (hstep : GStep 𝕄 v₁ v₂) :
    GStep 𝕄 (substStack σ S v₁) (substStack σ S v₂) := by
  induction S generalizing v₁ v₂ with
  | nil => exact hstep
  | cons c S ih =>
    rcases hS with ⟨hc, hS'⟩
    exact ih hS' (substCont_gstep σ hc hstep)

/-- Inner β-step of `ValStep`: for any `ValStep 𝕄 nr₂ s₁ s₂`, `s₁` has stack `c :: S` with `c ≠ .sucₑ`,
    `s₂` has stack `S₂` with `substStack (toSubstₕ s₂.heap) S₂ = substStack (toSubstₕ s₁.heap) S`,
    `NoSuc S → NoSuc S₂`, and the active redex steps in one `GStep`. -/
theorem valStep_inner_gstep {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M)
    {s₁ s₂ : State M} (h : ValStep 𝕄 nr₂ s₁ s₂) :
    ∃ (c : Cont M) (S : Stack M) (v₁ v₂ : GTerm M),
      s₁.stack = c :: S ∧
      c ≠ .sucₑ ∧
      (NoSuc S → NoSuc s₂.stack) ∧
      unfoldState s₁ = substStack (toSubstₕ s₁.heap) S v₁ ∧
      unfoldState s₂ = substStack (toSubstₕ s₁.heap) S v₂ ∧
      GStep 𝕄 v₁ v₂ := by
  cases h with
  | @lamₕ H p t u ρ ρ' S =>
    let q' := 𝕄.mul (Stack.mult 𝕄 nr₂ S) p
    let H₁ := Heap.cons H q' ⟨u, ρ'⟩
    let u' := GTerm.subst (toSubstₕ H) (GTerm.wk ρ' u)
    let t' := GTerm.subst (GTerm.liftSubst (toSubstₕ H)) (GTerm.wk (.lift ρ) t)
    refine ⟨.appₑ p u ρ', S, .app p (.lam p t') u', GTerm.subst0 t' u',
      rfl, nofun, NoSuc.wk (.step .id), ?_, ?_, .beta⟩
    · rw [unfoldState_eq_substStack]; rfl
    · rw [unfoldState_eq_substStack]
      dsimp only
      rw [substStack_wk1_cons]
      congr 1
      rw [GTerm.singleSubstComp]
      rfl
  | @prodStrongₕ₁ H p t₁ t₂ ρ S =>
    let t₁' := GTerm.subst (toSubstₕ H) (GTerm.wk ρ t₁)
    let t₂' := GTerm.subst (toSubstₕ H) (GTerm.wk ρ t₂)
    refine ⟨.fstₑ p, S, .fst p (.prod .strong p t₁' t₂'), t₁',
      rfl, nofun, id, ?_, unfoldState_eq_substStack _, .sigma_beta1⟩
    rw [unfoldState_eq_substStack]; rfl
  | @prodStrongₕ₂ H p t₁ t₂ ρ S =>
    let t₁' := GTerm.subst (toSubstₕ H) (GTerm.wk ρ t₁)
    let t₂' := GTerm.subst (toSubstₕ H) (GTerm.wk ρ t₂)
    refine ⟨.sndₑ p, S, .snd p (.prod .strong p t₁' t₂'), t₂',
      rfl, nofun, id, ?_, unfoldState_eq_substStack _, .sigma_beta2⟩
    rw [unfoldState_eq_substStack]; rfl
  | @prodWeakₕ H r p q t₁ t₂ A u ρ ρ' S =>
    let q₁ := 𝕄.mul (𝕄.mul (Stack.mult 𝕄 nr₂ S) r) p
    let q₂ := 𝕄.mul (Stack.mult 𝕄 nr₂ S) r
    let H₁ := Heap.cons H q₁ ⟨t₁, ρ⟩
    let H₂ := Heap.cons H₁ q₂ ⟨t₂, .step ρ⟩
    let A' := GTerm.subst (GTerm.liftSubst (toSubstₕ H)) (GTerm.wk (.lift ρ') A)
    let t₁' := GTerm.subst (toSubstₕ H) (GTerm.wk ρ t₁)
    let t₂' := GTerm.subst (toSubstₕ H) (GTerm.wk ρ t₂)
    let u' := GTerm.subst (toSubstₕ H) (GTerm.wk ρ' u)
    refine ⟨.prodrecₑ r p q A u ρ', S,
      .prodrec r p q A' (.prod .weak p t₁' t₂') u',
      .app r (.app (𝕄.mul r p) u' t₁') t₂',
      rfl, nofun, NoSuc.wk (.step (.step .id)), ?_, ?_, .prodrec_beta⟩
    · rw [unfoldState_eq_substStack]; rfl
    · rw [unfoldState_eq_substStack]
      dsimp only
      rw [substStack_wk2_cons2]
      congr 1
      simp only [GTerm.wk, GTerm.subst, wkVar]
      have hu_eq : GTerm.subst (toSubstₕ H₂)
          (GTerm.wk (.lift (.lift ρ')) (GTerm.wk (.step (.step .id)) u)) = u' := by
        rw [GTerm.wk_comp (.lift (.lift ρ')) (.step (.step .id)) u]
        apply subst_wk_wk_congr
        intro x
        rw [← wkVar_comp]
        rfl
      have ht₁_eq : toSubstₕ H₂ 1 = t₁' := rfl
      have ht₂_eq : toSubstₕ H₂ 0 = t₂' := by
        simp only [H₂, H₁, toSubstₕ, GTerm.consSubst]
        rw [wk_step_eq_wk1_wk, subst_consSubst_wk1]
      rw [hu_eq, ht₁_eq, ht₂_eq]
  | @zeroₕ H p q r A z s ρ ρ' S =>
    let A' := GTerm.subst (GTerm.liftSubst (toSubstₕ H)) (GTerm.wk (.lift ρ') A)
    let z' := GTerm.subst (toSubstₕ H) (GTerm.wk ρ' z)
    let s' := GTerm.subst (toSubstₕ H) (GTerm.wk ρ' s)
    refine ⟨.natrecₑ p q r A z s ρ', S, .natrec p q r A' z' s' .zero, z',
      rfl, nofun, id, ?_, unfoldState_eq_substStack _, .natrec_zero⟩
    rw [unfoldState_eq_substStack]; rfl
  | @sucₕ H p q r t A z s ρ ρ' S =>
    let q₁ := 𝕄.mul (Stack.mult 𝕄 nr₂ S) (nr₂ p r)
    let q₂ := 𝕄.mul (Stack.mult 𝕄 nr₂ S) r
    let H₁ := Heap.cons H q₁ ⟨t, ρ⟩
    let nr_term := GTerm.natrec p q r (GTerm.wk (.lift (.step .id)) A) (GTerm.wk1 z) (GTerm.wk1 s) (.var 0)
    let H₂ := Heap.cons H₁ q₂ ⟨nr_term, .lift ρ'⟩
    let A' := GTerm.subst (GTerm.liftSubst (toSubstₕ H)) (GTerm.wk (.lift ρ') A)
    let z' := GTerm.subst (toSubstₕ H) (GTerm.wk ρ' z)
    let s' := GTerm.subst (toSubstₕ H) (GTerm.wk ρ' s)
    let t' := GTerm.subst (toSubstₕ H) (GTerm.wk ρ t)
    refine ⟨.natrecₑ p q r A z s ρ', S,
      .natrec p q r A' z' s' (.succ t'),
      .app r (.app p s' t') (.natrec p q r A' z' s' t'),
      rfl, nofun, NoSuc.wk (.step (.step .id)), ?_, ?_, .natrec_succ⟩
    · rw [unfoldState_eq_substStack]; rfl
    · rw [unfoldState_eq_substStack]
      dsimp only
      rw [substStack_wk2_cons2]
      congr 1
      simp only [GTerm.wk, GTerm.subst, wkVar]
      have hs_eq : GTerm.subst (toSubstₕ H₂)
          (GTerm.wk (.lift (.lift ρ')) (GTerm.wk (.step (.step .id)) s)) = s' := by
        rw [GTerm.wk_comp (.lift (.lift ρ')) (.step (.step .id)) s]
        apply subst_wk_wk_congr
        intro x
        rw [← wkVar_comp]
        rfl
      have ht_eq : toSubstₕ H₂ 1 = t' := rfl
      have hnr_eq : toSubstₕ H₂ 0 = .natrec p q r A' z' s' t' := by
        simp only [H₂, nr_term, toSubstₕ, GTerm.consSubst, GTerm.wk, GTerm.subst, wkVar]
        have hA_eq : GTerm.subst (GTerm.liftSubst (toSubstₕ H₁))
            (GTerm.wk (.lift (.lift ρ')) (GTerm.wk (.lift (.step .id)) A)) = A' := by
          rw [GTerm.wk_comp (.lift (.lift ρ')) (.lift (.step .id)) A]
          apply subst_wk_wk_congr
          intro x
          rw [← wkVar_comp]
          cases x <;> rfl
        have hz_eq : GTerm.subst (toSubstₕ H₁) (GTerm.wk (.lift ρ') (GTerm.wk1 z)) = z' := by
          unfold GTerm.wk1
          rw [GTerm.wk_comp (.lift ρ') (.step .id) z]
          apply subst_wk_wk_congr
          intro x
          rw [← wkVar_comp]
          rfl
        have hs1_eq : GTerm.subst (toSubstₕ H₁) (GTerm.wk (.lift ρ') (GTerm.wk1 s)) = s' := by
          unfold GTerm.wk1
          rw [GTerm.wk_comp (.lift ρ') (.step .id) s]
          apply subst_wk_wk_congr
          intro x
          rw [← wkVar_comp]
          rfl
        rw [hA_eq, hz_eq, hs1_eq]
        rfl
      rw [hs_eq, ht_eq, hnr_eq]
  | @starWeakₕ H p q A u ρ ρ' S =>
    let A' := GTerm.subst (GTerm.liftSubst (toSubstₕ H)) (GTerm.wk (.lift ρ') A)
    let u' := GTerm.subst (toSubstₕ H) (GTerm.wk ρ' u)
    refine ⟨.unitrecₑ p q A u ρ', S, .unitrec p q A' .star u', u',
      rfl, nofun, id, ?_, unfoldState_eq_substStack _, .unitrec_beta⟩
    rw [unfoldState_eq_substStack]; rfl

/-- **M3 Lemma 4.7d (`⇒ᵥ`-unfolding)**:
    if `NoSuc s₁.stack` and `ValStep 𝕄 nr₂ s₁ s₂`, then `unfoldState s₁` steps in one `GStep`
    to `unfoldState s₂`, and `NoSuc s₂.stack` holds. -/
theorem unfold_valStep {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {s₁ s₂ : State M} (hns : NoSuc s₁.stack) (h : ValStep 𝕄 nr₂ s₁ s₂) :
    GStep 𝕄 (unfoldState s₁) (unfoldState s₂) ∧ NoSuc s₂.stack := by
  rcases valStep_inner_gstep 𝕄 nr₂ h with ⟨c, S, v₁, v₂, hstack, _, hns₂, hunf₁, hunf₂, hstep⟩
  rw [hstack] at hns
  rcases hns with ⟨_, hns_S⟩
  rw [hunf₁, hunf₂]
  exact ⟨substStack_gstep (toSubstₕ s₁.heap) hns_S hstep, hns₂ hns_S⟩

theorem noSuc_pres_elimStep {M : Type} {s₁ s₂ : State M}
    (hns : NoSuc s₁.stack) (h : ElimStep s₁ s₂) : NoSuc s₂.stack := by
  cases h <;> exact ⟨nofun, hns⟩

theorem noSuc_pres_trackElimStep {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {s₁ s₂ : State M} (hns : NoSuc s₁.stack) (h : TrackElimStep 𝕄 nr₂ s₁ s₂) : NoSuc s₂.stack := by
  cases h with
  | var _ => exact hns
  | elim he => exact noSuc_pres_elimStep hns he

theorem noSuc_pres_untrackElimStep {M : Type}
    {s₁ s₂ : State M} (hns : NoSuc s₁.stack) (h : UntrackElimStep s₁ s₂) : NoSuc s₂.stack := by
  cases h with
  | var _ => exact hns
  | elim he => exact noSuc_pres_elimStep hns he

/-- **M3 Theorem 4.7 (`⇾`-unfolding in `Graded.Heap.Reduction.Properties`)**:
    single-step tracked WHNF heap evaluation unfolds to `GStar 𝕄`. -/
theorem unfold_heapStep {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {s₁ s₂ : State M} (hns : NoSuc s₁.stack) (h : HeapStep 𝕄 nr₂ s₁ s₂) :
    GStar 𝕄 (unfoldState s₁) (unfoldState s₂) ∧ NoSuc s₂.stack := by
  cases h with
  | elimStep he =>
    rw [unfold_trackElimStep he]
    exact ⟨.refl _, noSuc_pres_trackElimStep hns he⟩
  | valStep hv =>
    rcases unfold_valStep hns hv with ⟨hgstep, hns₂⟩
    exact ⟨.step hgstep (.refl _), hns₂⟩

/-- **M3 Theorem 4.7 Multi-step (`⇾*`-unfolding in `Graded.Heap.Reduction.Properties`)**:
    multi-step tracked WHNF heap evaluation unfolds to `GStar 𝕄`. -/
theorem unfold_heapStar {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {s₁ s₂ : State M} (hns : NoSuc s₁.stack) (h : HeapStar 𝕄 nr₂ s₁ s₂) :
    GStar 𝕄 (unfoldState s₁) (unfoldState s₂) ∧ NoSuc s₂.stack := by
  induction h with
  | refl _ => exact ⟨.refl _, hns⟩
  | step hs _ ih =>
    rcases unfold_heapStep hns hs with ⟨hg₁, hns_mid⟩
    rcases ih hns_mid with ⟨hg₂, hns₂⟩
    exact ⟨GStar.trans hg₁ hg₂, hns₂⟩

/-- **M3 Theorem 4.8 (`⇢*`-unfolding in `Graded.Heap.Reduction.Properties`)**:
    multi-step untracked WHNF heap evaluation unfolds to `GStar 𝕄`. -/
theorem unfold_heapStarUntracked {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {s₁ s₂ : State M} (hns : NoSuc s₁.stack) (h : HeapStarUntracked 𝕄 nr₂ s₁ s₂) :
    GStar 𝕄 (unfoldState s₁) (unfoldState s₂) ∧ NoSuc s₂.stack := by
  induction h with
  | refl _ => exact ⟨.refl _, hns⟩
  | step hs _ ih =>
    cases hs with
    | elimStep he =>
      rw [unfold_untrackElimStep he]
      exact ih (noSuc_pres_untrackElimStep hns he)
    | valStep hv =>
      rcases unfold_valStep hns hv with ⟨hgstep, hns_mid⟩
      rcases ih hns_mid with ⟨hg₂, hns₂⟩
      exact ⟨.step hgstep hg₂, hns₂⟩

/-! ### Unfolding Soundness for Full Numeral Evaluation `↠*` (M3 Theorem 4.9) -/

@[simp] theorem Stack.wk_append {M : Type} (ρ : Wk) (S₁ S₂ : Stack M) :
    Stack.wk ρ (S₁ ++ S₂) = Stack.wk ρ S₁ ++ Stack.wk ρ S₂ := by
  induction S₁ with
  | nil => rfl
  | cons c S₁ ih => simp [Stack.wk, ih]

/-- Valid evaluation stacks during full numeral reduction `↠*`:
    a `.sucₑ`-free prefix `S₀` followed by `ℓ` outer `.sucₑ` frames (`S₀ ++ Stack.sucs ℓ`). -/
def ValidNumStack {M : Type} (S : Stack M) : Prop :=
  ∃ (S₀ : Stack M) (ℓ : Nat), NoSuc S₀ ∧ S = S₀ ++ Stack.sucs ℓ

theorem ValidNumStack.nil {M : Type} : ValidNumStack (M := M) [] :=
  ⟨[], 0, trivial, rfl⟩

theorem ValidNumStack.sucs {M : Type} (ℓ : Nat) : ValidNumStack (Stack.sucs (M := M) ℓ) :=
  ⟨[], ℓ, trivial, rfl⟩

theorem ValidNumStack.cons_non_suc {M : Type} {c : Cont M} {S : Stack M}
    (hc : c ≠ .sucₑ) (hS : ValidNumStack S) : ValidNumStack (c :: S) := by
  rcases hS with ⟨S₀, ℓ, hns, rfl⟩
  exact ⟨c :: S₀, ℓ, ⟨hc, hns⟩, rfl⟩

theorem ValidNumStack.wk {M : Type} (τ : Wk) {S : Stack M}
    (hS : ValidNumStack S) : ValidNumStack (Stack.wk τ S) := by
  rcases hS with ⟨S₀, ℓ, hns, rfl⟩
  refine ⟨Stack.wk τ S₀, ℓ, hns.wk τ, ?_⟩
  simp [Stack.wk_append, Stack.wk_sucs]

theorem ValidNumStack.inv_cons_non_suc {M : Type} {c : Cont M} {S : Stack M}
    (hc : c ≠ .sucₑ) (h : ValidNumStack (c :: S)) :
    ∃ (S₀ : Stack M) (ℓ : Nat), NoSuc S₀ ∧ S = S₀ ++ Stack.sucs ℓ := by
  rcases h with ⟨S₀, ℓ, hns, heq⟩
  cases S₀ with
  | nil =>
    cases ℓ with
    | zero => cases heq
    | succ ℓ =>
      simp only [List.nil_append, Stack.sucs, List.cons.injEq] at heq
      exact False.elim (hc heq.1)
  | cons c' S₀' =>
    simp only [List.cons_append, List.cons.injEq] at heq
    exact ⟨S₀', ℓ, hns.2, heq.2⟩

theorem ValidNumStack.inv_cons_suc {M : Type} {S : Stack M}
    (h : ValidNumStack (.sucₑ :: S)) : ValidNumStack S := by
  rcases h with ⟨S₀, ℓ, hns, heq⟩
  cases S₀ with
  | nil =>
    cases ℓ with
    | zero => cases heq
    | succ ℓ =>
      simp only [List.nil_append, Stack.sucs, List.cons.injEq] at heq
      rw [heq.2]
      exact ValidNumStack.sucs ℓ
  | cons c' S₀' =>
    simp only [List.cons_append, List.cons.injEq] at heq
    exact False.elim (hns.1 heq.1.symm)

theorem substStack_sucs_gstarNum {M : Type} {𝕄 : Modality M} (σ : GTerm.GSubst M)
    (ℓ : Nat) {v₁ v₂ : GTerm M} (h : GStarNum 𝕄 v₁ v₂) :
    GStarNum 𝕄 (substStack σ (Stack.sucs ℓ) v₁) (substStack σ (Stack.sucs ℓ) v₂) := by
  induction ℓ generalizing v₁ v₂ with
  | zero => exact h
  | succ ℓ ih =>
    simp only [Stack.sucs, substStack, substCont]
    exact ih (.succ_cong h)

/-- **M3 Theorem 4.9 (`↠`-unfolding in `Graded.Heap.Reduction.Properties`)**:
    single-step full numeral heap evaluation unfolds to `GStarNum 𝕄`. -/
theorem unfold_heapNumStep {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {s₁ s₂ : State M} (hvalid : ValidNumStack s₁.stack) (h : HeapNumStep 𝕄 nr₂ s₁ s₂) :
    GStarNum 𝕄 (unfoldState s₁) (unfoldState s₂) ∧ ValidNumStack s₂.stack := by
  cases h with
  | elimStep he =>
    rw [unfold_trackElimStep he]
    refine ⟨.refl _, ?_⟩
    cases he with
    | var _ => exact hvalid
    | elim helim =>
      cases helim <;> exact hvalid.cons_non_suc nofun
  | valStep hv =>
    rcases valStep_inner_gstep 𝕄 nr₂ hv with ⟨c, S, v₁, v₂, hstack, hc, _, hunf₁, hunf₂, hstep⟩
    rw [hstack] at hvalid
    rcases hvalid.inv_cons_non_suc hc with ⟨S₀, ℓ, hns₀, hS_eq⟩
    have hvalid_S : ValidNumStack S := ⟨S₀, ℓ, hns₀, hS_eq⟩
    have hvalid₂ : ValidNumStack s₂.stack := by
      cases hv with
      | lamₕ =>
        injection hstack with _ hS'
        subst hS'
        exact ValidNumStack.wk (.step .id) hvalid_S
      | prodStrongₕ₁ =>
        injection hstack with _ hS'
        subst hS'
        exact hvalid_S
      | prodStrongₕ₂ =>
        injection hstack with _ hS'
        subst hS'
        exact hvalid_S
      | prodWeakₕ =>
        injection hstack with _ hS'
        subst hS'
        exact ValidNumStack.wk (.step (.step .id)) hvalid_S
      | zeroₕ =>
        injection hstack with _ hS'
        subst hS'
        exact hvalid_S
      | sucₕ =>
        injection hstack with _ hS'
        subst hS'
        exact ValidNumStack.wk (.step (.step .id)) hvalid_S
      | starWeakₕ =>
        injection hstack with _ hS'
        subst hS'
        exact hvalid_S
    subst hS_eq
    rw [hunf₁, hunf₂, substStack_append, substStack_append]
    have hg₀ : GStep 𝕄 (substStack (toSubstₕ s₁.heap) S₀ v₁)
        (substStack (toSubstₕ s₁.heap) S₀ v₂) :=
      substStack_gstep (toSubstₕ s₁.heap) hns₀ hstep
    exact ⟨substStack_sucs_gstarNum (toSubstₕ s₁.heap) ℓ (.whnf_step hg₀ (.refl _)), hvalid₂⟩
  | numStep hn =>
    rw [unfold_numStep hn]
    refine ⟨.refl _, ?_⟩
    cases hn with
    | @sucₕ H t ρ ℓ _ => exact ValidNumStack.sucs (ℓ + 1)
    | numₕ _ => exact hvalid.inv_cons_suc

/-- **M3 Theorem 4.9 Multi-step (`↠*`-unfolding in `Graded.Heap.Reduction.Properties`)**:
    multi-step full numeral heap evaluation unfolds to `GStarNum 𝕄`. -/
theorem unfold_heapNumStar {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {s₁ s₂ : State M} (hvalid : ValidNumStack s₁.stack) (h : HeapNumStar 𝕄 nr₂ s₁ s₂) :
    GStarNum 𝕄 (unfoldState s₁) (unfoldState s₂) ∧ ValidNumStack s₂.stack := by
  induction h with
  | refl _ => exact ⟨.refl _, hvalid⟩
  | step hs _ ih =>
    rcases unfold_heapNumStep hvalid hs with ⟨hg₁, hvalid_mid⟩
    rcases ih hvalid_mid with ⟨hg₂, hvalid₂⟩
    exact ⟨GStarNum.trans hg₁ hg₂, hvalid₂⟩

@[simp] theorem wk_suck {M : Type} (ρ : Wk) (k : Nat) :
    GTerm.wk ρ (GTerm.suck (M := M) k) = GTerm.suck k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [GTerm.suck, GTerm.wk, ih]

@[simp] theorem subst_suck {M : Type} (σ : GTerm.GSubst M) (k : Nat) :
    GTerm.subst σ (GTerm.suck (M := M) k) = GTerm.suck k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [GTerm.suck, GTerm.subst, ih]

/-- **M3 Theorem 4.10 (Initial-to-Numeral Unfolding & Resource Soundness)**:
    if `initialState k t` is well-resourced (`Usage 𝕄 γ .oneMode t` with `γ ≤ 𝟘`) and
    evaluates via `↠*` to a numeral state `⟨ H , suck n , ρ , [] ⟩`, then:
    1. the final state is well-resourced (`StateUsage 𝕄 nr₂ ⟨ H , suck n , ρ , [] ⟩`), and
    2. the source term `t` reduces via `GStarNum 𝕄 t (GTerm.suck n)`. -/
theorem initial_eval_numeral_sound {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {k n : Nat} {t : GTerm M} {H : Heap M} {ρ : Wk}
    (hs₀ : StateUsage 𝕄 nr₂ (initialState k t))
    (hstar : HeapNumStar 𝕄 nr₂ (initialState k t) ⟨H, GTerm.suck n, ρ, []⟩) :
    StateUsage 𝕄 nr₂ ⟨H, GTerm.suck n, ρ, []⟩ ∧ GStarNum 𝕄 t (GTerm.suck n) := by
  have hs_final := usage_pres_numStar_empty hw hnr hs₀ hstar
  have hunf := (unfold_heapNumStar ValidNumStack.nil hstar).1
  rw [unfoldState_initial] at hunf
  simp only [unfoldState, unfoldStack, wk_suck, subst_suck] at hunf
  exact ⟨hs_final, hunf⟩

/-! ## 6. Non-Interference for the Security Lattice (`Graded.Heap.Non-interference`, M3 Section 6, Theorem 6.1) -/

namespace SecurityLevel

/-- In `securityModality` (`Public = 𝟙`, `Secret = 𝟘`, `add = meetLat`, `mul = join`),
    the constant function `securityNr₂ p r = .publicLvl` satisfies `NatrecMultFn`. -/
def securityNr₂ : SecurityLevel → SecurityLevel → SecurityLevel :=
  fun _ _ ↦ .publicLvl

theorem securityNatrecMultFn : NatrecMultFn securityModality securityNr₂ where
  le_one _ _ := rfl
  le_step _ _ := rfl
  maximal hx1 _ := hx1

theorem securityWellBehavedZero : securityModality.HasWellBehavedZero where
  nonTrivial := by decide
  zero_product {p q} h := by cases p <;> cases q <;> revert h <;> decide
  add_positive_left {p q} h := by cases p <;> cases q <;> revert h <;> decide
  meet_positive_left {p q} h := by cases p <;> cases q <;> revert h <;> decide

theorem security_subEq_public {r : SecurityLevel}
    (h : securityModality.SubEq .publicLvl .publicLvl r) : r = .publicLvl :=
  securityModality.subEq_unique h
    (securityModality.addEqMeet_subEq (fun _ _ ↦ rfl) (securityModality.le_refl .publicLvl))

theorem security_not_subEq_secret_public {r : SecurityLevel} :
    ¬ securityModality.SubEq .secretLvl .publicLvl r := by
  intro h
  have hzero := (securityWellBehavedZero.zero_sub_eq h).2
  exact SecurityLevel.noConfusion hzero

/-- A `.secretLvl` binding at the head of the heap can never be looked up at `.publicLvl`. -/
theorem secret_not_lookup_public {H H' : Heap SecurityLevel} {e e' : Entry SecurityLevel} :
    ¬ HeapLookup securityModality (.cons H .secretLvl e) 0 .publicLvl e' H' := by
  intro hl
  cases hl with
  | here hsub => exact security_not_subEq_secret_public hsub

/-- Initial state for M3 Section 6 Non-Interference: a single `.secretLvl` input `u`
    allocated on the heap, evaluating open term `t` in the empty stack. -/
def secretInputState (u t : GTerm SecurityLevel) : State SecurityLevel :=
  ⟨.cons .nil .secretLvl ⟨u, .id⟩, t, .id, []⟩

@[simp] theorem unfold_secretInputState (u t : GTerm SecurityLevel) :
    unfoldState (secretInputState u t) = GTerm.subst0 t u := by
  simp [secretInputState, unfoldState, unfoldStack, toSubstₕ, GTerm.wk_id, GTerm.subst_id,
    GTerm.subst0, GTerm.sgSubst]

theorem NumStep.not_valStep {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {s s₁ s₂ : State M} (hv : ValStep 𝕄 nr₂ s s₁) (hn : NumStep s s₂) : False := by
  rcases valStep_inner_gstep 𝕄 nr₂ hv with ⟨c, S, _, _, hstack, hc, _, _, _, _⟩
  cases hn with
  | @sucₕ _ _ _ ℓ _ =>
    cases ℓ with
    | zero => simp [Stack.sucs] at hstack
    | succ ℓ =>
      simp [Stack.sucs] at hstack
      exact hc hstack.1.symm
  | numₕ _ =>
    simp at hstack
    exact hc hstack.1.symm

theorem NumStep.not_trackElimStep {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {s s₁ s₂ : State M} (he : TrackElimStep 𝕄 nr₂ s s₁) (hn : NumStep s s₂) : False := by
  have hnotnum : ¬ GNumeral s.head := by
    intro hnum
    cases he with
    | var _ => cases hnum
    | elim hel => cases hel <;> cases hnum
  have hnotsucc : ∀ t, s.head ≠ .succ t := by
    intro t ht
    cases he with
    | var _ => cases ht
    | elim hel => cases hel <;> cases ht
  cases hn with
  | sucₕ _ => exact hnotsucc _ rfl
  | numₕ hnum => exact hnotnum hnum

theorem NumStep.det {M : Type} {s s₁ s₂ : State M}
    (h₁ : NumStep s s₁) (h₂ : NumStep s s₂) : s₁ = s₂ := by
  generalize hs : s = s₀ at h₁
  cases h₁ with
  | @sucₕ H₁ t₁ ρ₁ ℓ₁ hnotnum₁ =>
    cases h₂ with
    | @sucₕ H₂ t₂ ρ₂ ℓ₂ hnotnum₂ =>
      injection hs with hH ht hρ hS
      injection ht with ht'
      subst hH; subst ht'; subst hρ
      rw [hS]
    | numₕ hnum₂ =>
      injection hs with _ ht _ _
      rw [ht] at hnum₂
      cases hnum₂ with
      | succ h => exact False.elim (hnotnum₁ h)
  | numₕ hnum₁ =>
    cases h₂ with
    | sucₕ hnotnum₂ =>
      injection hs with _ ht _ _
      rw [← ht] at hnum₁
      cases hnum₁ with
      | succ h => exact False.elim (hnotnum₂ h)
    | numₕ hnum₂ =>
      injection hs with hH ht hρ hS
      subst hH; subst ht; subst hρ
      injection hS with _ hS'
      subst hS'
      rfl

/-- Determinism of `HeapNumStep`: at most one transition applies to any state. -/
theorem heapNumStep_det {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {s s₁ s₂ : State M}
    (h₁ : HeapNumStep 𝕄 nr₂ s s₁) (h₂ : HeapNumStep 𝕄 nr₂ s s₂) : s₁ = s₂ := by
  cases h₁ with
  | elimStep he₁ =>
    cases h₂ with
    | elimStep he₂ =>
      cases he₁ with
      | var hl₁ =>
        cases he₂ with
        | var hl₂ =>
          rcases hl₁.det hl₂ with ⟨h_eq, rfl⟩
          injection h_eq with ht hρ
          subst ht; subst hρ; rfl
        | elim hel₂ => cases hel₂
      | elim hel₁ =>
        cases he₂ with
        | var _ => cases hel₁
        | elim hel₂ => cases hel₁ <;> cases hel₂ <;> rfl
    | valStep hv₂ =>
      cases he₁ with
      | var _ => cases hv₂
      | elim hel₁ => cases hel₁ <;> cases hv₂
    | numStep hn₂ =>
      exact False.elim (NumStep.not_trackElimStep he₁ hn₂)
  | valStep hv₁ =>
    cases h₂ with
    | elimStep he₂ =>
      cases he₂ with
      | var _ => cases hv₁
      | elim hel₂ => cases hel₂ <;> cases hv₁
    | valStep hv₂ =>
      cases hv₁ <;> cases hv₂ <;> rfl
    | numStep hn₂ =>
      exact False.elim (NumStep.not_valStep hv₁ hn₂)
  | numStep hn₁ =>
    cases h₂ with
    | elimStep he₂ =>
      exact False.elim (NumStep.not_trackElimStep he₂ hn₁)
    | valStep hv₂ =>
      exact False.elim (NumStep.not_valStep hv₂ hn₁)
    | numStep hn₂ =>
      exact NumStep.det hn₁ hn₂

/-- Canonical numeral states with an empty stack are irreducible under `HeapNumStep`. -/
theorem suck_empty_no_heapNumStep {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {H : Heap M} {k : Nat} {ρ : Wk} {s' : State M}
    (h : HeapNumStep 𝕄 nr₂ ⟨H, GTerm.suck k, ρ, []⟩ s') : False := by
  generalize hs : (⟨H, GTerm.suck k, ρ, []⟩ : State M) = s₀ at h
  cases h with
  | elimStep he =>
    cases he with
    | var _ =>
      injection hs with _ ht _ _
      cases k <;> cases ht
    | elim hel =>
      cases hel <;> (injection hs with _ ht _ _; cases k <;> cases ht)
  | valStep hv =>
    rcases valStep_inner_gstep 𝕄 nr₂ hv with ⟨c, S, _, _, hstack, _, _, _, _, _⟩
    have hS : s₀.stack = [] := by rw [← hs]
    rw [hS] at hstack
    cases hstack
  | numStep hn =>
    cases hn with
    | @sucₕ _ t _ ℓ hnotnum =>
      injection hs with _ ht _ _
      cases k with
      | zero => cases ht
      | succ k =>
        injection ht with ht'
        subst ht'
        exact hnotnum (GNumeral.of_suck k)
    | numₕ _ =>
      injection hs with _ _ _ hS
      cases hS

/-- Public-equivalent heaps where `.publicLvl` entries satisfy `NoErasedMatches`
    and `.secretLvl` entries contain arbitrary terms. -/
inductive HeapEquivPublicNEM : Heap SecurityLevel → Heap SecurityLevel → Prop where
  | nil : HeapEquivPublicNEM .nil .nil
  | cons_public {H₁ H₂ : Heap SecurityLevel} {e : Entry SecurityLevel} :
      NoErasedMatches securityModality e.term →
      HeapEquivPublicNEM H₁ H₂ →
      HeapEquivPublicNEM (.cons H₁ .publicLvl e) (.cons H₂ .publicLvl e)
  | cons_secret {H₁ H₂ : Heap SecurityLevel} {e₁ e₂ : Entry SecurityLevel} :
      HeapEquivPublicNEM H₁ H₂ →
      HeapEquivPublicNEM (.cons H₁ .secretLvl e₁) (.cons H₂ .secretLvl e₂)
  | dummy {H₁ H₂ : Heap SecurityLevel} :
      HeapEquivPublicNEM H₁ H₂ →
      HeapEquivPublicNEM (.dummy H₁) (.dummy H₂)

theorem HeapEquivPublicNEM.cons_same {H₁ H₂ : Heap SecurityLevel}
    (p : SecurityLevel) (e : Entry SecurityLevel)
    (hnem : p = .publicLvl → NoErasedMatches securityModality e.term)
    (hH : HeapEquivPublicNEM H₁ H₂) :
    HeapEquivPublicNEM (.cons H₁ p e) (.cons H₂ p e) := by
  cases p with
  | publicLvl => exact .cons_public (hnem rfl) hH
  | secretLvl => exact .cons_secret hH

theorem NoErasedMatches.wk {M : Type} {𝕄 : Modality M} (ρ : Wk) {t : GTerm M}
    (h : NoErasedMatches 𝕄 t) : NoErasedMatches 𝕄 (GTerm.wk ρ t) := by
  induction t generalizing ρ with
  | var _ | univ | nat | unit | zero | star => trivial
  | pi _ _ _ _ ihA ihB | sigma _ _ _ _ _ ihA ihB => exact ⟨ihA ρ h.1, ihB (.lift ρ) h.2⟩
  | lam _ _ ih => exact ih (.lift ρ) h
  | fst _ _ ih | snd _ _ ih | succ _ ih => exact ih ρ h
  | app _ _ _ iht ihu | prod _ _ _ _ iht ihu => exact ⟨iht ρ h.1, ihu ρ h.2⟩
  | prodrec _ _ _ _ _ _ _ iht ihu => exact ⟨h.1, iht ρ h.2.1, ihu ρ h.2.2⟩
  | unitrec _ _ _ _ _ _ iht ihu => exact ⟨h.1, iht ρ h.2.1, ihu ρ h.2.2⟩
  | natrec _ _ _ _ _ _ _ _ ihz ihs ihn => exact ⟨ihz ρ h.1, ihs ρ h.2.1, ihn ρ h.2.2⟩

theorem HeapEquivPublicNEM.lookup_public {H₁ H₂ H₁' H₂' : Heap SecurityLevel}
    {y : Nat} {e₁ e₂ : Entry SecurityLevel}
    (hH : HeapEquivPublicNEM H₁ H₂)
    (hl₁ : HeapLookup securityModality H₁ y .publicLvl e₁ H₁')
    (hl₂ : HeapLookup securityModality H₂ y .publicLvl e₂ H₂') :
    e₁ = e₂ ∧ NoErasedMatches securityModality e₁.term ∧ HeapEquivPublicNEM H₁' H₂' := by
  induction hH generalizing y e₁ e₂ H₁' H₂' with
  | nil => cases hl₁
  | @cons_public H₁ H₂ e hnem hH ih =>
    cases hl₁ with
    | here hsub₁ =>
      cases hl₂ with
      | here hsub₂ =>
        have hr₁ := security_subEq_public hsub₁
        have hr₂ := security_subEq_public hsub₂
        subst hr₁; subst hr₂
        exact ⟨rfl, hnem, .cons_public hnem hH⟩
    | there hl₁' =>
      cases hl₂ with
      | there hl₂' =>
        rcases ih hl₁' hl₂' with ⟨rfl, hnem', hH'⟩
        exact ⟨rfl, hnem', .cons_public hnem hH'⟩
  | cons_secret hH ih =>
    cases hl₁ with
    | here hsub₁ =>
      exact False.elim (security_not_subEq_secret_public hsub₁)
    | there hl₁' =>
      cases hl₂ with
      | there hl₂' =>
        rcases ih hl₁' hl₂' with ⟨rfl, hnem', hH'⟩
        exact ⟨rfl, hnem', .cons_secret hH'⟩
  | dummy hH ih =>
    cases hl₁ with
    | thereDummy hl₁' =>
      cases hl₂ with
      | thereDummy hl₂' =>
        rcases ih hl₁' hl₂' with ⟨rfl, hnem', hH'⟩
        exact ⟨rfl, hnem', .dummy hH'⟩

/-- Continuation frames without erased (`Secret`) pattern matches. -/
def ContNoErasedMatches : Cont SecurityLevel → Prop
  | .appₑ _ u _ => NoErasedMatches securityModality u
  | .fstₑ _ | .sndₑ _ | .sucₑ => True
  | .prodrecₑ r _ _ _ u _ => r ≠ .secretLvl ∧ NoErasedMatches securityModality u
  | .unitrecₑ p _ _ u _ => p ≠ .secretLvl ∧ NoErasedMatches securityModality u
  | .natrecₑ _ _ _ _ z s _ =>
      NoErasedMatches securityModality z ∧ NoErasedMatches securityModality s

/-- Evaluation stacks without erased (`Secret`) pattern matches. -/
def StackNoErasedMatches : Stack SecurityLevel → Prop
  | [] => True
  | c :: S => ContNoErasedMatches c ∧ StackNoErasedMatches S

theorem ContNoErasedMatches.mult_eq_public {c : Cont SecurityLevel}
    (hc : ContNoErasedMatches c) :
    Cont.mult securityModality securityNr₂ c = .publicLvl := by
  cases c with
  | appₑ _ _ _ | fstₑ _ | sndₑ _ | sucₑ | natrecₑ _ _ _ _ _ _ _ => rfl
  | prodrecₑ r _ _ _ _ _ =>
    rcases hc with ⟨hr, _⟩
    cases r with
    | publicLvl => rfl
    | secretLvl => exact False.elim (hr rfl)
  | unitrecₑ p _ _ _ _ =>
    rcases hc with ⟨hp, _⟩
    cases p with
    | publicLvl => rfl
    | secretLvl => exact False.elim (hp rfl)

theorem StackNoErasedMatches.mult_eq_public {S : Stack SecurityLevel}
    (hS : StackNoErasedMatches S) :
    Stack.mult securityModality securityNr₂ S = .publicLvl := by
  induction S with
  | nil => rfl
  | cons c S ih =>
    rcases hS with ⟨hc, hS'⟩
    simp only [Stack.mult_cons, hc.mult_eq_public, ih hS']
    rfl

theorem StackNoErasedMatches.wk (τ : Wk) {S : Stack SecurityLevel}
    (hS : StackNoErasedMatches S) : StackNoErasedMatches (Stack.wk τ S) := by
  induction S with
  | nil => trivial
  | cons c S ih =>
    rcases hS with ⟨hc, hS'⟩
    refine ⟨?_, ih hS'⟩
    cases c <;> simp [Cont.wk, ContNoErasedMatches] at hc ⊢ <;> exact hc

/-- Lockstep invariant for two states agreeing on `.publicLvl` heap cells, head term,
    environment, and stack, with `NoErasedMatches` on public code. -/
structure StateEquivPublicNEM (s₁ s₂ : State SecurityLevel) : Prop where
  heapEquiv : HeapEquivPublicNEM s₁.heap s₂.heap
  headEq : s₁.head = s₂.head
  envEq : s₁.env = s₂.env
  stackEq : s₁.stack = s₂.stack
  headNEM : NoErasedMatches securityModality s₁.head
  stackNEM : StackNoErasedMatches s₁.stack

/-- Lockstep bisimulation of `HeapNumStep` on `StateEquivPublicNEM`:
    if `s₁` and `s₂` are public-equivalent and both take a `HeapNumStep`, their
    successor states remain public-equivalent. -/
theorem stateEquivPublicNEM_lockstep {s₁ s₂ s₁' s₂' : State SecurityLevel}
    (heq : StateEquivPublicNEM s₁ s₂)
    (hstep₁ : HeapNumStep securityModality securityNr₂ s₁ s₁')
    (hstep₂ : HeapNumStep securityModality securityNr₂ s₂ s₂') :
    StateEquivPublicNEM s₁' s₂' := by
  rcases s₁ with ⟨H₁, t, ρ, S⟩
  rcases s₂ with ⟨H₂, t₂, ρ₂, S₂⟩
  rcases heq with ⟨hH, ht, hρ, hS, hnem_t, hnem_S⟩
  dsimp only at hH ht hρ hS hnem_t hnem_S
  subst ht; subst hρ; subst hS
  cases hstep₁ with
  | elimStep he₁ =>
    cases he₁ with
    | @var _ H₁' x u₁ ρ_e ρ₁' S hl₁ =>
      cases hstep₂ with
      | elimStep he₂ =>
        cases he₂ with
        | @var _ H₂' _ u₂ _ ρ₂' _ hl₂ =>
          have hmult : Stack.mult securityModality securityNr₂ S = .publicLvl :=
            hnem_S.mult_eq_public
          rw [hmult] at hl₁ hl₂
          rcases hH.lookup_public hl₁ hl₂ with ⟨he_eq, hnem_u, hH'⟩
          injection he_eq with hu_eq hρ_eq
          subst hu_eq; subst hρ_eq
          exact ⟨hH', rfl, rfl, rfl, hnem_u, hnem_S⟩
        | elim hel₂ => cases hel₂
      | valStep hv₂ => cases hv₂
      | numStep hn₂ =>
        cases hn₂ with
        | numₕ hnum => cases hnum
    | elim hel₁ =>
      have hs₂_eq : s₂' = ⟨H₂, s₁'.head, s₁'.env, s₁'.stack⟩ := by
        have hstep₂_expected : HeapNumStep securityModality securityNr₂
            ⟨H₂, t, ρ, S⟩ ⟨H₂, s₁'.head, s₁'.env, s₁'.stack⟩ := by
          cases hel₁ <;> exact .elimStep (.elim (by constructor))
        exact heapNumStep_det hstep₂ hstep₂_expected
      subst hs₂_eq
      cases hel₁ with
      | appₕ =>
        exact ⟨hH, rfl, rfl, rfl, hnem_t.1, ⟨hnem_t.2, hnem_S⟩⟩
      | fstₕ | sndₕ =>
        exact ⟨hH, rfl, rfl, rfl, hnem_t, ⟨trivial, hnem_S⟩⟩
      | prodrecₕ =>
        exact ⟨hH, rfl, rfl, rfl, hnem_t.2.1, ⟨⟨hnem_t.1, hnem_t.2.2⟩, hnem_S⟩⟩
      | unitrecₕ =>
        exact ⟨hH, rfl, rfl, rfl, hnem_t.2.1, ⟨⟨hnem_t.1, hnem_t.2.2⟩, hnem_S⟩⟩
      | natrecₕ =>
        exact ⟨hH, rfl, rfl, rfl, hnem_t.2.2, ⟨⟨hnem_t.1, hnem_t.2.1⟩, hnem_S⟩⟩
  | valStep hv₁ =>
    cases hv₁ with
    | @lamₕ _ p body u ρ ρ' S₀ =>
      have hs₂ : s₂' = ⟨.cons H₂ (securityModality.mul (Stack.mult securityModality securityNr₂ S₀) p) ⟨u, ρ'⟩,
          body, .lift ρ, Stack.wk1 S₀⟩ :=
        heapNumStep_det hstep₂ (.valStep .lamₕ)
      subst hs₂
      rcases hnem_S with ⟨hc, hS₀⟩
      exact ⟨hH.cons_same _ ⟨u, ρ'⟩ (fun _ ↦ hc), rfl, rfl, rfl, hnem_t, hS₀.wk (.step .id)⟩
    | @prodStrongₕ₁ _ p t₁ t₂ ρ S₀ =>
      have hs₂ : s₂' = ⟨H₂, t₁, ρ, S₀⟩ :=
        heapNumStep_det hstep₂ (.valStep .prodStrongₕ₁)
      subst hs₂
      exact ⟨hH, rfl, rfl, rfl, hnem_t.1, hnem_S.2⟩
    | @prodStrongₕ₂ _ p t₁ t₂ ρ S₀ =>
      have hs₂ : s₂' = ⟨H₂, t₂, ρ, S₀⟩ :=
        heapNumStep_det hstep₂ (.valStep .prodStrongₕ₂)
      subst hs₂
      exact ⟨hH, rfl, rfl, rfl, hnem_t.2, hnem_S.2⟩
    | @prodWeakₕ _ r p q t₁ t₂ A u ρ ρ' S₀ =>
      have hs₂ := heapNumStep_det hstep₂ (.valStep .prodWeakₕ)
      subst hs₂
      rcases hnem_S with ⟨⟨_, hnem_u⟩, hS₀⟩
      exact ⟨(hH.cons_same _ ⟨t₁, ρ⟩ (fun _ ↦ hnem_t.1)).cons_same _ ⟨t₂, .step ρ⟩ (fun _ ↦ hnem_t.2),
        rfl, rfl, rfl,
        ⟨⟨NoErasedMatches.wk (.step (.step .id)) hnem_u, trivial⟩, trivial⟩,
        hS₀.wk (.step (.step .id))⟩
    | @zeroₕ _ p q r A z s ρ ρ' S₀ =>
      have hs₂ : s₂' = ⟨H₂, z, ρ', S₀⟩ :=
        heapNumStep_det hstep₂ (.valStep .zeroₕ)
      subst hs₂
      rcases hnem_S with ⟨⟨hnem_z, _⟩, hS₀⟩
      exact ⟨hH, rfl, rfl, rfl, hnem_z, hS₀⟩
    | @sucₕ _ p q r pred A z s ρ ρ' S₀ =>
      have hs₂ := heapNumStep_det hstep₂ (.valStep .sucₕ)
      subst hs₂
      rcases hnem_S with ⟨⟨hnem_z, hnem_s⟩, hS₀⟩
      have hnem_nr : NoErasedMatches securityModality
          (.natrec p q r (GTerm.wk (.lift (.step .id)) A) (GTerm.wk1 z) (GTerm.wk1 s) (.var 0)) :=
        ⟨NoErasedMatches.wk (.step .id) hnem_z, NoErasedMatches.wk (.step .id) hnem_s, trivial⟩
      exact ⟨(hH.cons_same _ ⟨pred, ρ⟩ (fun _ ↦ hnem_t)).cons_same _
          ⟨.natrec p q r (GTerm.wk (.lift (.step .id)) A) (GTerm.wk1 z) (GTerm.wk1 s) (.var 0), .lift ρ'⟩
          (fun _ ↦ hnem_nr),
        rfl, rfl, rfl,
        ⟨⟨NoErasedMatches.wk (.step (.step .id)) hnem_s, trivial⟩, trivial⟩,
        hS₀.wk (.step (.step .id))⟩
    | @starWeakₕ _ p q A u ρ ρ' S₀ =>
      have hs₂ : s₂' = ⟨H₂, u, ρ', S₀⟩ :=
        heapNumStep_det hstep₂ (.valStep .starWeakₕ)
      subst hs₂
      rcases hnem_S with ⟨⟨_, hnem_u⟩, hS₀⟩
      exact ⟨hH, rfl, rfl, rfl, hnem_u, hS₀⟩
  | numStep hn₁ =>
    have hs₂_eq : s₂' = ⟨H₂, s₁'.head, s₁'.env, s₁'.stack⟩ := by
      have hstep₂_expected : HeapNumStep securityModality securityNr₂
          ⟨H₂, t, ρ, S⟩ ⟨H₂, s₁'.head, s₁'.env, s₁'.stack⟩ := by
        cases hn₁ with
        | sucₕ hnotnum => exact .numStep (.sucₕ hnotnum)
        | numₕ hnum => exact .numStep (.numₕ hnum)
      exact heapNumStep_det hstep₂ hstep₂_expected
    subst hs₂_eq
    cases hn₁ with
    | sucₕ _ =>
      exact ⟨hH, rfl, rfl, rfl, hnem_t, ⟨trivial, hnem_S⟩⟩
    | numₕ _ =>
      exact ⟨hH, rfl, rfl, rfl, hnem_t, hnem_S.2⟩

/-- Multi-step lockstep theorem for `HeapNumStar` on `StateEquivPublicNEM`. -/
theorem stateEquivPublicNEM_numStar_suck
    {s₁ s₂ : State SecurityLevel} {H₁' H₂' : Heap SecurityLevel}
    {k₁ k₂ : Nat} {ρ₁ ρ₂ : Wk}
    (heq : StateEquivPublicNEM s₁ s₂)
    (hstar₁ : HeapNumStar securityModality securityNr₂ s₁ ⟨H₁', GTerm.suck k₁, ρ₁, []⟩)
    (hstar₂ : HeapNumStar securityModality securityNr₂ s₂ ⟨H₂', GTerm.suck k₂, ρ₂, []⟩) :
    k₁ = k₂ := by
  generalize hs₁_final : (⟨H₁', GTerm.suck k₁, ρ₁, []⟩ : State SecurityLevel) = f₁ at hstar₁
  induction hstar₁ generalizing s₂ H₂' k₂ ρ₂ with
  | refl _ =>
    subst hs₁_final
    cases hstar₂ with
    | refl _ =>
      have hhead : GTerm.suck (M := SecurityLevel) k₁ = GTerm.suck k₂ := heq.headEq
      exact GStarNum.suck_inj hhead
    | step hs₂ _ =>
      rcases s₂ with ⟨H₂, t₂, ρ₂', S₂⟩
      have ht₂ : t₂ = GTerm.suck k₁ := heq.headEq.symm
      have hS₂ : S₂ = [] := heq.stackEq.symm
      subst ht₂; subst hS₂
      exact False.elim (suck_empty_no_heapNumStep hs₂)
  | @step s₁₀ s₁_mid _ hs₁ _ ih =>
    cases hstar₂ with
    | refl _ =>
      rcases s₁₀ with ⟨H₁, t₁, ρ₁', S₁⟩
      have ht₁ : t₁ = GTerm.suck k₂ := heq.headEq
      have hS₁ : S₁ = [] := heq.stackEq
      subst ht₁; subst hS₁
      exact False.elim (suck_empty_no_heapNumStep hs₁)
    | step hs₂ hrest₂ =>
      exact ih (stateEquivPublicNEM_lockstep heq hs₁ hs₂) hrest₂ hs₁_final

/-- **M3 Theorem 6.1 (Non-Interference for the Graded Heap Machine, `Graded.Heap.Non-interference`)**:
    for any open term `t` with no erased (`Secret`) pattern matches (`NoErasedMatches securityModality t`),
    and any two secret inputs `u₁, u₂ : GTerm SecurityLevel` allocated at `.secretLvl` on the heap,
    if `secretInputState u₁ t` evaluates via `HeapNumStar` to a numeral `suck k₁` and
    `secretInputState u₂ t` evaluates via `HeapNumStar` to a numeral `suck k₂`, then `k₁ = k₂`. -/
theorem non_interference
    {t u₁ u₂ : GTerm SecurityLevel}
    {H₁' H₂' : Heap SecurityLevel} {k₁ k₂ : Nat} {ρ₁ ρ₂ : Wk}
    (hnem : NoErasedMatches securityModality t)
    (hstar₁ : HeapNumStar securityModality securityNr₂
      (secretInputState u₁ t) ⟨H₁', GTerm.suck k₁, ρ₁, []⟩)
    (hstar₂ : HeapNumStar securityModality securityNr₂
      (secretInputState u₂ t) ⟨H₂', GTerm.suck k₂, ρ₂, []⟩) :
    k₁ = k₂ := by
  have heq : StateEquivPublicNEM (secretInputState u₁ t) (secretInputState u₂ t) :=
    ⟨.cons_secret .nil, rfl, rfl, rfl, hnem, trivial⟩
  exact stateEquivPublicNEM_numStar_suck heq hstar₁ hstar₂

end SecurityLevel

end FeasibleUnivalence
