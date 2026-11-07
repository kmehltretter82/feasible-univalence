/-
Copyright (c) 2023–2026 Andreas Abel, Nils Anders Danielsson, Oskar Eriksson.
Lean 4 translation and extension prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Sources:
- M2: Graded Modal Dependent Type Theory with a Universe and Erasure, Formalized
  (arXiv:2603.29716v2 / ICFP 2023), Agda tag `jfp-submission-2026-04-30`
  (`75c23df3b1421184cffe35ffd492bb9743dff240`), `Graded/Context.agda`,
  `Graded/Mode.agda`, `Graded/Usage.agda`, `Graded/Substitution.agda`,
  `Graded/Substitution/Properties.agda` (Theorem 5.3 `substₘ-lemma`), and
  `Graded/Reduction.agda` (Theorem 5.4 `usagePresTerm`).
- M3: On Recursion in Graded Modal Type Theory (ICFP 2026, DOI 10.1145/3828677),
  Agda tag `icfp26` (`93987e3ddc11f583fc3ecdc05472e1dac4094c4f`),
  `Graded/Reduction/Necessary.agda` and `Graded/Context/Properties/Natrec.agda`.
-/
import Abel2018.Syntax
import Abel2018.UntypedProperties
import Abel2018.Judgments
import FeasibleUnivalence.Modality

namespace FeasibleUnivalence

open Abel2018

instance {M : Type} (𝕄 : Modality M) (p : M) : Decidable (p = 𝕄.zero) :=
  𝕄.decEqZero p

/-! ## 1. Modes (`Graded.Mode`) -/

/-- The two modes of M2/M3 (`𝟘ᵐ` for erased/type-level contexts and `𝟙ᵐ` for runtime contexts). -/
inductive Mode where
  | zeroMode : Mode
  | oneMode : Mode
  deriving DecidableEq, Repr

namespace Mode

variable {M : Type} (𝕄 : Modality M)

/-- Embedding `⌜ m ⌝` of a mode into the modality (`⌜ 𝟘ᵐ ⌝ = 𝟘`, `⌜ 𝟙ᵐ ⌝ = 𝟙`). -/
def toGrade : Mode → M
  | .zeroMode => 𝕄.zero
  | .oneMode => 𝕄.one

/-- Mode scaling `m ᵐ· p`: if `m = 𝟘ᵐ` or `p = 𝟘`, returns `𝟘ᵐ`, else `𝟙ᵐ`. -/
def scale (m : Mode) (p : M) : Mode :=
  match m with
  | .zeroMode => .zeroMode
  | .oneMode => if p = 𝕄.zero then .zeroMode else .oneMode

/-- Grade-to-mode map `⌞ p ⌟`: `𝟘ᵐ` if `p = 𝟘`, else `𝟙ᵐ`. -/
def ofGrade (p : M) : Mode :=
  if p = 𝕄.zero then .zeroMode else .oneMode

@[simp] theorem scale_zeroMode (p : M) : scale 𝕄 .zeroMode p = .zeroMode := rfl

@[simp] theorem scale_zero_grade (m : Mode) : scale 𝕄 m 𝕄.zero = .zeroMode := by
  cases m <;> simp [scale]

theorem scale_oneMode_ne_zero {p : M} (hp : p ≠ 𝕄.zero) :
    scale 𝕄 .oneMode p = .oneMode := by
  simp [scale, hp]

theorem ofGrade_zero : ofGrade 𝕄 𝕄.zero = .zeroMode := by
  simp [ofGrade]

theorem ofGrade_ne_zero {p : M} (hp : p ≠ 𝕄.zero) : ofGrade 𝕄 p = .oneMode := by
  simp [ofGrade, hp]

theorem scale_oneMode (p : M) : scale 𝕄 .oneMode p = ofGrade 𝕄 p := rfl

theorem ofGrade_toGrade {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero) (m : Mode) :
    ofGrade 𝕄 (toGrade 𝕄 m) = m := by
  cases m with
  | zeroMode => exact ofGrade_zero 𝕄
  | oneMode => exact ofGrade_ne_zero 𝕄 hw.nonTrivial

theorem scale_mul {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero) (m : Mode) (r p : M) :
    scale 𝕄 (scale 𝕄 m r) p = scale 𝕄 m (𝕄.mul r p) := by
  cases m with
  | zeroMode => rfl
  | oneMode =>
    by_cases hr : r = 𝕄.zero
    · subst hr
      simp [scale, 𝕄.zero_mul]
    · by_cases hp : p = 𝕄.zero
      · subst hp
        simp [scale, hr, 𝕄.mul_zero]
      · have hrp : 𝕄.mul r p ≠ 𝕄.zero := by
          intro h0
          rcases hw.zero_product h0 with h | h
          · exact hr h
          · exact hp h
        simp [scale, hr, hp, hrp]

end Mode

/-! ## 2. Usage Contexts (`Conₘ`, M2 Definition 3.1) -/

/-- Usage contexts `Conₘ M`: infinite de Bruijn grade maps `Nat → M`
    (matching `Abel2018.Subst := Nat → Term`), forming a left semimodule over `Modality M`. -/
abbrev Conₘ (M : Type) := Nat → M

namespace Conₘ

variable {M : Type} (𝕄 : Modality M)

/-- The all-zero usage context `𝟘ᶜ`. -/
def zero : Conₘ M := fun _ ↦ 𝕄.zero

/-- Pointwise addition `γ +ᶜ δ`. -/
def add (γ δ : Conₘ M) : Conₘ M := fun x ↦ 𝕄.add (γ x) (δ x)

/-- Scalar multiplication `p ·ᶜ γ`. -/
def scale (p : M) (γ : Conₘ M) : Conₘ M := fun x ↦ 𝕄.mul p (γ x)

/-- Pointwise meet `γ ∧ᶜ δ`. -/
def meet (γ δ : Conₘ M) : Conₘ M := fun x ↦ 𝕄.meet (γ x) (δ x)

/-- Pointwise partial order `γ ≤ᶜ δ`. -/
def le (γ δ : Conₘ M) : Prop := ∀ x, 𝕄.le (γ x) (δ x)

/-- Context extension `γ ∙ p` (putting `p` at de Bruijn index `0`). -/
def cons (γ : Conₘ M) (p : M) : Conₘ M
  | 0 => p
  | x + 1 => γ x

/-- Head grade `γ 0`. -/
def head (γ : Conₘ M) : M := γ 0

/-- Tail usage context `fun x ↦ γ (x + 1)`. -/
def tail (γ : Conₘ M) : Conₘ M := fun x ↦ γ (x + 1)

/-- Single-variable usage context `𝟘ᶜ , x ≔ p`. -/
def single (x : Nat) (p : M) : Conₘ M :=
  fun y ↦ if y = x then p else 𝕄.zero

/-- Sequence of usage contexts `nrᵢᶜ r γ δ` for `natrec` GLB rule. -/
def nrᵢ (r : M) (γ δ : Conₘ M) (i : Nat) : Conₘ M :=
  fun x ↦ 𝕄.nrᵢ r (γ x) (δ x) i

/-- Pointwise greatest lower bound `Greatest-lower-boundᶜ χ seq`. -/
def GLB (χ : Conₘ M) (seq : Nat → Conₘ M) : Prop :=
  ∀ x, 𝕄.GreatestLowerBound (χ x) (fun i ↦ seq i x)

/-! ### Semimodule Laws for `Conₘ` -/

theorem add_assoc (γ δ η : Conₘ M) :
    add 𝕄 (add 𝕄 γ δ) η = add 𝕄 γ (add 𝕄 δ η) := by
  funext x; exact 𝕄.add_assoc (γ x) (δ x) (η x)

theorem add_comm (γ δ : Conₘ M) : add 𝕄 γ δ = add 𝕄 δ γ := by
  funext x; exact 𝕄.add_comm (γ x) (δ x)

@[simp] theorem zero_add (γ : Conₘ M) : add 𝕄 (zero 𝕄) γ = γ := by
  funext x; exact 𝕄.zero_add (γ x)

@[simp] theorem add_zero (γ : Conₘ M) : add 𝕄 γ (zero 𝕄) = γ := by
  funext x; exact 𝕄.add_zero (γ x)

theorem scale_assoc (p q : M) (γ : Conₘ M) :
    scale 𝕄 (𝕄.mul p q) γ = scale 𝕄 p (scale 𝕄 q γ) := by
  funext x; exact 𝕄.mul_assoc p q (γ x)

@[simp] theorem one_scale (γ : Conₘ M) : scale 𝕄 𝕄.one γ = γ := by
  funext x; exact 𝕄.one_mul (γ x)

@[simp] theorem zero_scale (γ : Conₘ M) : scale 𝕄 𝕄.zero γ = zero 𝕄 := by
  funext x; exact 𝕄.zero_mul (γ x)

@[simp] theorem scale_zero (p : M) : scale 𝕄 p (zero 𝕄) = zero 𝕄 := by
  funext _; exact 𝕄.mul_zero p

theorem scale_add_distrib (p : M) (γ δ : Conₘ M) :
    scale 𝕄 p (add 𝕄 γ δ) = add 𝕄 (scale 𝕄 p γ) (scale 𝕄 p δ) := by
  funext x; exact 𝕄.left_distrib p (γ x) (δ x)

theorem add_scale_distrib (p q : M) (γ : Conₘ M) :
    scale 𝕄 (𝕄.add p q) γ = add 𝕄 (scale 𝕄 p γ) (scale 𝕄 q γ) := by
  funext x; exact 𝕄.right_distrib p q (γ x)

theorem le_refl (γ : Conₘ M) : le 𝕄 γ γ :=
  fun x ↦ 𝕄.le_refl (γ x)

theorem le_antisymm {γ δ : Conₘ M} (h1 : le 𝕄 γ δ) (h2 : le 𝕄 δ γ) : γ = δ := by
  funext x; exact 𝕄.le_antisymm (h1 x) (h2 x)

theorem le_trans {γ δ η : Conₘ M} (h1 : le 𝕄 γ δ) (h2 : le 𝕄 δ η) : le 𝕄 γ η :=
  fun x ↦ 𝕄.le_trans (h1 x) (h2 x)

theorem add_mono {γ₁ γ₂ δ₁ δ₂ : Conₘ M}
    (hγ : le 𝕄 γ₁ γ₂) (hδ : le 𝕄 δ₁ δ₂) :
    le 𝕄 (add 𝕄 γ₁ δ₁) (add 𝕄 γ₂ δ₂) :=
  fun x ↦ 𝕄.add_mono (hγ x) (hδ x)

theorem scale_mono {p₁ p₂ : M} {γ₁ γ₂ : Conₘ M}
    (hp : 𝕄.le p₁ p₂) (hγ : le 𝕄 γ₁ γ₂) :
    le 𝕄 (scale 𝕄 p₁ γ₁) (scale 𝕄 p₂ γ₂) :=
  fun x ↦ 𝕄.mul_mono hp (hγ x)

theorem scale_mono_right (p : M) {γ₁ γ₂ : Conₘ M} (hγ : le 𝕄 γ₁ γ₂) :
    le 𝕄 (scale 𝕄 p γ₁) (scale 𝕄 p γ₂) :=
  fun x ↦ 𝕄.mul_mono_right p (hγ x)

theorem meet_mono {γ₁ γ₂ δ₁ δ₂ : Conₘ M}
    (hγ : le 𝕄 γ₁ γ₂) (hδ : le 𝕄 δ₁ δ₂) :
    le 𝕄 (meet 𝕄 γ₁ δ₁) (meet 𝕄 γ₂ δ₂) :=
  fun x ↦ 𝕄.meet_mono (hγ x) (hδ x)

theorem cons_le_cons {γ δ : Conₘ M} {p q : M}
    (hγ : le 𝕄 γ δ) (hp : 𝕄.le p q) :
    le 𝕄 (cons γ p) (cons δ q)
  | 0 => hp
  | x + 1 => hγ x

theorem tail_le_tail {γ δ : Conₘ M} (h : le 𝕄 γ δ) : le 𝕄 (tail γ) (tail δ) :=
  fun x ↦ h (x + 1)

theorem head_le_head {γ δ : Conₘ M} (h : le 𝕄 γ δ) : 𝕄.le (head γ) (head δ) :=
  h 0

@[simp] theorem cons_zero_zero : cons (zero 𝕄) 𝕄.zero = zero 𝕄 := by
  funext x; cases x <;> rfl

@[simp] theorem cons_add (γ δ : Conₘ M) (p q : M) :
    add 𝕄 (cons γ p) (cons δ q) = cons (add 𝕄 γ δ) (𝕄.add p q) := by
  funext x; cases x <;> rfl

@[simp] theorem cons_scale (p q : M) (γ : Conₘ M) :
    scale 𝕄 p (cons γ q) = cons (scale 𝕄 p γ) (𝕄.mul p q) := by
  funext x; cases x <;> rfl

@[simp] theorem cons_meet (γ δ : Conₘ M) (p q : M) :
    meet 𝕄 (cons γ p) (cons δ q) = cons (meet 𝕄 γ δ) (𝕄.meet p q) := by
  funext x; cases x <;> rfl

@[simp] theorem cons_tail_head (γ : Conₘ M) : cons (tail γ) (head γ) = γ := by
  funext x; cases x <;> rfl

@[simp] theorem single_zero (p : M) : single 𝕄 0 p = cons (zero 𝕄) p := by
  funext x; cases x <;> rfl

@[simp] theorem single_succ (x : Nat) (p : M) :
    single 𝕄 (x + 1) p = cons (single 𝕄 x p) 𝕄.zero := by
  funext y
  cases y with
  | zero => rfl
  | succ y =>
    simp only [single, cons]
    by_cases h : y = x <;> simp [h]

theorem scale_single (p q : M) (x : Nat) :
    scale 𝕄 p (single 𝕄 x q) = single 𝕄 x (𝕄.mul p q) := by
  funext y
  simp only [scale, single]
  by_cases h : y = x
  · simp [h]
  · simp [h, 𝕄.mul_zero]

/-! ### Weakening of Usage Contexts (`wkConₘ`, `Graded.Context.Weakening`) -/

/-- Weakening of a usage context along `ρ : Wk`. -/
def wk (ρ : Wk) (γ : Conₘ M) : Conₘ M :=
  match ρ with
  | .id => γ
  | .step ρ => cons (wk ρ γ) 𝕄.zero
  | .lift ρ => cons (wk ρ (tail γ)) (head γ)

@[simp] theorem wk_id (γ : Conₘ M) : wk 𝕄 .id γ = γ := rfl

@[simp] theorem wk_zero (ρ : Wk) : wk 𝕄 ρ (zero 𝕄) = zero 𝕄 := by
  induction ρ with
  | id => rfl
  | step ρ ih => simp [wk, ih]
  | lift ρ ih =>
    have ht : tail (zero 𝕄) = zero 𝕄 := rfl
    have hh : head (zero 𝕄) = 𝕄.zero := rfl
    simp [wk, ht, hh, ih]

theorem wk_add (ρ : Wk) (γ δ : Conₘ M) :
    wk 𝕄 ρ (add 𝕄 γ δ) = add 𝕄 (wk 𝕄 ρ γ) (wk 𝕄 ρ δ) := by
  induction ρ generalizing γ δ with
  | id => rfl
  | step ρ ih =>
    simp only [wk, ih, cons_add, 𝕄.add_zero]
  | lift ρ ih =>
    have ht : tail (add 𝕄 γ δ) = add 𝕄 (tail γ) (tail δ) := rfl
    have hh : head (add 𝕄 γ δ) = 𝕄.add (head γ) (head δ) := rfl
    simp only [wk, ht, hh, ih, cons_add]

theorem wk_scale (ρ : Wk) (p : M) (γ : Conₘ M) :
    wk 𝕄 ρ (scale 𝕄 p γ) = scale 𝕄 p (wk 𝕄 ρ γ) := by
  induction ρ generalizing γ with
  | id => rfl
  | step ρ ih =>
    simp only [wk, ih, cons_scale, 𝕄.mul_zero]
  | lift ρ ih =>
    have ht : tail (scale 𝕄 p γ) = scale 𝕄 p (tail γ) := rfl
    have hh : head (scale 𝕄 p γ) = 𝕄.mul p (head γ) := rfl
    simp only [wk, ht, hh, ih, cons_scale]

theorem wk_meet (ρ : Wk) (γ δ : Conₘ M) :
    wk 𝕄 ρ (meet 𝕄 γ δ) = meet 𝕄 (wk 𝕄 ρ γ) (wk 𝕄 ρ δ) := by
  induction ρ generalizing γ δ with
  | id => rfl
  | step ρ ih =>
    simp only [wk, ih, cons_meet, 𝕄.meet_idem]
  | lift ρ ih =>
    have ht : tail (meet 𝕄 γ δ) = meet 𝕄 (tail γ) (tail δ) := rfl
    have hh : head (meet 𝕄 γ δ) = 𝕄.meet (head γ) (head δ) := rfl
    simp only [wk, ht, hh, ih, cons_meet]

theorem wk_single (ρ : Wk) (x : Nat) (p : M) :
    wk 𝕄 ρ (single 𝕄 x p) = single 𝕄 (wkVar ρ x) p := by
  induction ρ generalizing x with
  | id => rfl
  | step ρ ih =>
    simp only [wk, ih, wkVar, single_succ]
  | lift ρ ih =>
    cases x with
    | zero =>
      have ht : tail (single 𝕄 0 p) = zero 𝕄 := rfl
      have hh : head (single 𝕄 0 p) = p := rfl
      rw [wk, ht, hh, wk_zero, wkVar, single_zero]
    | succ x =>
      have ht : tail (single 𝕄 (x + 1) p) = single 𝕄 x p := by
        rw [single_succ]; rfl
      have hh : head (single 𝕄 (x + 1) p) = 𝕄.zero := rfl
      rw [wk, ht, hh, ih, wkVar, single_succ]

theorem wk_mono (ρ : Wk) {γ δ : Conₘ M} (h : le 𝕄 γ δ) :
    le 𝕄 (wk 𝕄 ρ γ) (wk 𝕄 ρ δ) := by
  induction ρ generalizing γ δ with
  | id => exact h
  | step ρ ih =>
    exact cons_le_cons 𝕄 (ih h) (𝕄.le_refl 𝕄.zero)
  | lift ρ ih =>
    exact cons_le_cons 𝕄 (ih (tail_le_tail 𝕄 h)) (head_le_head 𝕄 h)

@[simp] theorem nrᵢ_zero (r : M) (γ δ : Conₘ M) :
    nrᵢ 𝕄 r γ δ 0 = γ := rfl

@[simp] theorem nrᵢ_succ (r : M) (γ δ : Conₘ M) (i : Nat) :
    nrᵢ 𝕄 r γ δ (i + 1) = add 𝕄 δ (scale 𝕄 r (nrᵢ 𝕄 r γ δ i)) := rfl

theorem wk_nrᵢ (ρ : Wk) (r : M) (γ δ : Conₘ M) (i : Nat) :
    wk 𝕄 ρ (nrᵢ 𝕄 r γ δ i) = nrᵢ 𝕄 r (wk 𝕄 ρ γ) (wk 𝕄 ρ δ) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [nrᵢ_succ, wk_add, wk_scale, ih]

theorem wk_GLB (ρ : Wk) {r : M} {γ δ χ : Conₘ M}
    (h : GLB 𝕄 χ (nrᵢ 𝕄 r γ δ)) :
    GLB 𝕄 (wk 𝕄 ρ χ) (nrᵢ 𝕄 r (wk 𝕄 ρ γ) (wk 𝕄 ρ δ)) := by
  induction ρ generalizing γ δ χ with
  | id => exact h
  | step ρ ih =>
    intro y
    cases y with
    | zero =>
      simp only [wk, cons, nrᵢ]
      exact 𝕄.GLB_nrᵢ_zero r
    | succ y =>
      exact ih h y
  | lift ρ ih =>
    intro y
    cases y with
    | zero =>
      exact h 0
    | succ y =>
      have htail : GLB 𝕄 (tail χ) (nrᵢ 𝕄 r (tail γ) (tail δ)) :=
        fun z ↦ h (z + 1)
      exact ih htail y

theorem GLB_nrᵢ_le₀ {r : M} {γ δ χ : Conₘ M}
    (h : GLB 𝕄 χ (nrᵢ 𝕄 r γ δ)) : le 𝕄 χ γ :=
  fun x ↦ 𝕄.nrᵢ_GLB_le₀ (h x)

theorem GLB_nrᵢ_le_step {𝕄 : Modality M} (hwb : 𝕄.HasWellBehavedGLBs) {r : M} {γ δ χ : Conₘ M}
    (h : GLB 𝕄 χ (nrᵢ 𝕄 r γ δ)) :
    le 𝕄 χ (add 𝕄 δ (scale 𝕄 r χ)) :=
  fun x ↦ 𝕄.nrᵢ_GLB_le_step hwb (h x)

end Conₘ

/-! ## 3. Graded Syntax (`GTerm`) and Underlying `Abel2018.Term` Projection -/

/-- Strength of Σ and unit types (`strong` projections `fst`/`snd` vs `weak` eliminator `prodrec`). -/
inductive Strength where
  | strong : Strength
  | weak : Strength
  deriving DecidableEq, Repr

/-- Graded de Bruijn syntax for the M2/M3 calculus (`Definition/Untyped.agda`).
    Binders match `Abel2018.Term` (codomain of `pi`/`sigma`, body of `lam`, and motive of `natrec`),
    so weakening and substitution commute strictly with `eraseGrades : GTerm M → Abel2018.Term`. -/
inductive GTerm (M : Type) where
  | univ : GTerm M
  | pi : M → M → GTerm M → GTerm M → GTerm M
  | sigma : Strength → M → M → GTerm M → GTerm M → GTerm M
  | nat : GTerm M
  | unit : GTerm M
  | var : Nat → GTerm M
  | lam : M → GTerm M → GTerm M
  | app : M → GTerm M → GTerm M → GTerm M
  | prod : Strength → M → GTerm M → GTerm M → GTerm M
  | fst : M → GTerm M → GTerm M
  | snd : M → GTerm M → GTerm M
  | prodrec : M → M → M → GTerm M → GTerm M → GTerm M → GTerm M
  | zero : GTerm M
  | succ : GTerm M → GTerm M
  | natrec : M → M → M → GTerm M → GTerm M → GTerm M → GTerm M → GTerm M
  | star : GTerm M
  | unitrec : M → M → GTerm M → GTerm M → GTerm M → GTerm M
  deriving DecidableEq, Repr

namespace GTerm

variable {M : Type}

/-- Forget grade annotations into `Abel2018.Term` (for the Π-ℕ-U core; pairs/unit map to standard encodings). -/
def eraseGrades : GTerm M → Abel2018.Term
  | .univ => .univ
  | .pi _ _ A B => .pi (eraseGrades A) (eraseGrades B)
  | .sigma _ _ _ A B => .pi (eraseGrades A) (eraseGrades B)
  | .nat => .nat
  | .unit => .nat
  | .var x => .var x
  | .lam _ t => .lam (eraseGrades t)
  | .app _ t u => .app (eraseGrades t) (eraseGrades u)
  | .prod _ _ t u => .app (eraseGrades t) (eraseGrades u)
  | .fst _ t => eraseGrades t
  | .snd _ t => eraseGrades t
  | .prodrec _ _ _ _ t u => .app (eraseGrades u) (eraseGrades t)
  | .zero => .zero
  | .succ t => .succ (eraseGrades t)
  | .natrec _ _ _ A z s n =>
      .natrec (eraseGrades A) (eraseGrades z) (eraseGrades s) (eraseGrades n)
  | .star => .zero
  | .unitrec _ _ _ _ u => eraseGrades u

/-- Embed an `Abel2018.Term` into `GTerm M` using default grade `𝟙`. -/
def ofAbelTerm (𝕄 : Modality M) : Abel2018.Term → GTerm M
  | .univ => .univ
  | .pi A B => .pi 𝕄.one 𝕄.one (ofAbelTerm 𝕄 A) (ofAbelTerm 𝕄 B)
  | .nat => .nat
  | .var x => .var x
  | .lam t => .lam 𝕄.one (ofAbelTerm 𝕄 t)
  | .app t u => .app 𝕄.one (ofAbelTerm 𝕄 t) (ofAbelTerm 𝕄 u)
  | .zero => .zero
  | .succ t => .succ (ofAbelTerm 𝕄 t)
  | .natrec A z s n =>
      .natrec 𝕄.one 𝕄.one 𝕄.one
        (ofAbelTerm 𝕄 A) (ofAbelTerm 𝕄 z) (ofAbelTerm 𝕄 s) (ofAbelTerm 𝕄 n)

@[simp] theorem eraseGrades_ofAbelTerm (𝕄 : Modality M) (t : Abel2018.Term) :
    eraseGrades (ofAbelTerm 𝕄 t) = t := by
  induction t <;> simp [ofAbelTerm, eraseGrades, *]

/-- Weakening on graded terms. -/
def wk (ρ : Wk) : GTerm M → GTerm M
  | .univ => .univ
  | .pi p q A B => .pi p q (wk ρ A) (wk (.lift ρ) B)
  | .sigma s p q A B => .sigma s p q (wk ρ A) (wk (.lift ρ) B)
  | .nat => .nat
  | .unit => .unit
  | .var x => .var (wkVar ρ x)
  | .lam p t => .lam p (wk (.lift ρ) t)
  | .app p t u => .app p (wk ρ t) (wk ρ u)
  | .prod s p t u => .prod s p (wk ρ t) (wk ρ u)
  | .fst p t => .fst p (wk ρ t)
  | .snd p t => .snd p (wk ρ t)
  | .prodrec r p q A t u => .prodrec r p q (wk (.lift ρ) A) (wk ρ t) (wk ρ u)
  | .zero => .zero
  | .succ t => .succ (wk ρ t)
  | .natrec p q r A z s n =>
      .natrec p q r (wk (.lift ρ) A) (wk ρ z) (wk ρ s) (wk ρ n)
  | .star => .star
  | .unitrec p q A t u => .unitrec p q (wk (.lift ρ) A) (wk ρ t) (wk ρ u)

def wk1 : GTerm M → GTerm M := wk (.step .id)

abbrev GSubst (M : Type) := Nat → GTerm M

def liftSubst (σ : GSubst M) : GSubst M
  | 0 => .var 0
  | n + 1 => wk1 (σ n)

def subst (σ : GSubst M) : GTerm M → GTerm M
  | .univ => .univ
  | .pi p q A B => .pi p q (subst σ A) (subst (liftSubst σ) B)
  | .sigma s p q A B => .sigma s p q (subst σ A) (subst (liftSubst σ) B)
  | .nat => .nat
  | .unit => .unit
  | .var x => σ x
  | .lam p t => .lam p (subst (liftSubst σ) t)
  | .app p t u => .app p (subst σ t) (subst σ u)
  | .prod s p t u => .prod s p (subst σ t) (subst σ u)
  | .fst p t => .fst p (subst σ t)
  | .snd p t => .snd p (subst σ t)
  | .prodrec r p q A t u =>
      .prodrec r p q (subst (liftSubst σ) A) (subst σ t) (subst σ u)
  | .zero => .zero
  | .succ t => .succ (subst σ t)
  | .natrec p q r A z s n =>
      .natrec p q r (subst (liftSubst σ) A) (subst σ z) (subst σ s) (subst σ n)
  | .star => .star
  | .unitrec p q A t u =>
      .unitrec p q (subst (liftSubst σ) A) (subst σ t) (subst σ u)

def idSubst : GSubst M := GTerm.var

def consSubst (σ : GSubst M) (a : GTerm M) : GSubst M
  | 0 => a
  | n + 1 => σ n

def sgSubst (a : GTerm M) : GSubst M := consSubst idSubst a

def subst0 (t a : GTerm M) : GTerm M := subst (sgSubst a) t

/-- Canonical graded numeral `suc^k 0`. -/
def suck : Nat → GTerm M
  | 0 => .zero
  | k + 1 => .succ (suck k)

@[simp] theorem eraseGrades_wk (ρ : Wk) (t : GTerm M) :
    eraseGrades (wk ρ t) = Abel2018.wk ρ (eraseGrades t) := by
  induction t generalizing ρ <;> simp [wk, Abel2018.wk, eraseGrades, *]

theorem eraseGrades_liftSubst (σ : GSubst M) :
    (fun x ↦ eraseGrades (liftSubst σ x)) = Abel2018.liftSubst (fun x ↦ eraseGrades (σ x)) := by
  funext x
  cases x with
  | zero => rfl
  | succ x =>
    simp [liftSubst, Abel2018.liftSubst, wk1, Abel2018.wk1, eraseGrades_wk]

@[simp] theorem eraseGrades_subst (σ : GSubst M) (t : GTerm M) :
    eraseGrades (subst σ t) = Abel2018.subst (fun x ↦ eraseGrades (σ x)) (eraseGrades t) := by
  induction t generalizing σ <;>
    simp [subst, Abel2018.subst, eraseGrades, eraseGrades_liftSubst, *]

end GTerm

/-! ## 4. Mode-Indexed Usage Relation (`γ ▸[m] t`, M2 Definition 5.1 & M3 Section 5.2) -/

/-- Mode-indexed usage judgment `Usage 𝕄 γ m t` (`γ ▸[ m ] t`), corresponding to
    `Graded/Usage.agda`. Includes both the inequality-based `natrec` rule (`natrec_ineq`)
    and the M3 Section 5.2 GLB-based `natrec` rule (`natrec_glb`). -/
inductive Usage {M : Type} (𝕄 : Modality M) : Conₘ M → Mode → GTerm M → Prop where
  | sub {γ δ m t} :
      Usage 𝕄 γ m t →
      Conₘ.le 𝕄 δ γ →
      Usage 𝕄 δ m t
  | var {m x} :
      Usage 𝕄 (Conₘ.single 𝕄 x (Mode.toGrade 𝕄 m)) m (.var x)
  | univ {m} :
      Usage 𝕄 (Conₘ.zero 𝕄) m .univ
  | nat {m} :
      Usage 𝕄 (Conₘ.zero 𝕄) m .nat
  | unit {m} :
      Usage 𝕄 (Conₘ.zero 𝕄) m .unit
  | star {m} :
      Usage 𝕄 (Conₘ.zero 𝕄) m .star
  | zero {m} :
      Usage 𝕄 (Conₘ.zero 𝕄) m .zero
  | succ {γ m t} :
      Usage 𝕄 γ m t →
      Usage 𝕄 γ m (.succ t)
  | pi {γ δ m p q A B} :
      Usage 𝕄 γ (Mode.scale 𝕄 m p) A →
      Usage 𝕄 (Conₘ.cons δ (𝕄.mul (Mode.toGrade 𝕄 m) q)) m B →
      Usage 𝕄 (Conₘ.add 𝕄 (Conₘ.scale 𝕄 p γ) δ) m (.pi p q A B)
  | sigma {γ δ m s p q A B} :
      Usage 𝕄 γ (Mode.scale 𝕄 m p) A →
      Usage 𝕄 (Conₘ.cons δ (𝕄.mul (Mode.toGrade 𝕄 m) q)) m B →
      Usage 𝕄 (Conₘ.add 𝕄 (Conₘ.scale 𝕄 p γ) δ) m (.sigma s p q A B)
  | lam {γ m p t} :
      Usage 𝕄 (Conₘ.cons γ (𝕄.mul (Mode.toGrade 𝕄 m) p)) m t →
      Usage 𝕄 γ m (.lam p t)
  | app {γ δ m p t u} :
      Usage 𝕄 γ m t →
      Usage 𝕄 δ (Mode.scale 𝕄 m p) u →
      Usage 𝕄 (Conₘ.add 𝕄 γ (Conₘ.scale 𝕄 p δ)) m (.app p t u)
  | prodStrong {γ δ m p t u} :
      Usage 𝕄 γ (Mode.scale 𝕄 m p) t →
      Usage 𝕄 δ m u →
      Usage 𝕄 (Conₘ.meet 𝕄 (Conₘ.scale 𝕄 p γ) δ) m (.prod .strong p t u)
  | prodWeak {γ δ m p t u} :
      Usage 𝕄 γ (Mode.scale 𝕄 m p) t →
      Usage 𝕄 δ m u →
      Usage 𝕄 (Conₘ.add 𝕄 (Conₘ.scale 𝕄 p γ) δ) m (.prod .weak p t u)
  | fst {γ m p t} :
      Usage 𝕄 γ m t →
      𝕄.le (𝕄.mul (Mode.toGrade 𝕄 m) p) (Mode.toGrade 𝕄 m) →
      Usage 𝕄 γ m (.fst p t)
  | snd {γ m p t} :
      Usage 𝕄 γ m t →
      Usage 𝕄 γ m (.snd p t)
  | prodrec {γ δ η m r p q A t u} :
      Usage 𝕄 γ (Mode.scale 𝕄 m r) t →
      Usage 𝕄 δ m u →
      Usage 𝕄 (Conₘ.cons η 𝕄.zero) .zeroMode A →
      Usage 𝕄 (Conₘ.add 𝕄 (Conₘ.scale 𝕄 r γ) δ) m (.prodrec r p q A t u)
  | unitrec {γ δ η m p q A t u} :
      Usage 𝕄 γ (Mode.scale 𝕄 m p) t →
      Usage 𝕄 δ m u →
      Usage 𝕄 (Conₘ.cons η 𝕄.zero) .zeroMode A →
      Usage 𝕄 (Conₘ.add 𝕄 (Conₘ.scale 𝕄 p γ) δ) m (.unitrec p q A t u)
  | natrec_fix {γ δ η θ χ m x p q r A z s n} :
      Usage 𝕄 γ m z →
      Usage 𝕄 δ m s →
      Usage 𝕄 η m n →
      Usage 𝕄 (Conₘ.cons θ 𝕄.zero) .zeroMode A →
      𝕄.le x 𝕄.one →
      𝕄.le (𝕄.mul (Mode.toGrade 𝕄 m) x) (𝕄.mul (Mode.toGrade 𝕄 m) (𝕄.add p (𝕄.mul r x))) →
      Conₘ.le 𝕄 χ γ →
      Conₘ.le 𝕄 χ (Conₘ.add 𝕄 δ (Conₘ.scale 𝕄 r χ)) →
      Usage 𝕄 (Conₘ.add 𝕄 (Conₘ.scale 𝕄 x η) χ) m (.natrec p q r A z s n)

namespace Usage

variable {M : Type} {𝕄 : Modality M}

/-- M3 Section 5.2 GLB-based `natrec` usage rule (`natrec-no-nr-glbₘ`), derived from
    `natrec_fix` via M3 Lemma 5.3 (`nrᵢ_GLB_le₀` and `nrᵢ_GLB_le_step`). -/
theorem natrec_glb (hwb : 𝕄.HasWellBehavedGLBs) {γ δ η θ χ : Conₘ M} {m : Mode} {x p q r : M}
    {A z s n : GTerm M}
    (hz : Usage 𝕄 γ m z)
    (hs : Usage 𝕄 δ m s)
    (hn : Usage 𝕄 η m n)
    (hA : Usage 𝕄 (Conₘ.cons θ 𝕄.zero) .zeroMode A)
    (hx : 𝕄.GreatestLowerBound x (𝕄.nrᵢ r 𝕄.one p))
    (hχ : Conₘ.GLB 𝕄 χ (Conₘ.nrᵢ 𝕄 r γ δ)) :
    Usage 𝕄 (Conₘ.add 𝕄 (Conₘ.scale 𝕄 x η) χ) m (.natrec p q r A z s n) :=
  .natrec_fix hz hs hn hA
    (𝕄.nrᵢ_GLB_le₀ hx)
    (𝕄.mul_mono_right (Mode.toGrade 𝕄 m) (𝕄.nrᵢ_GLB_le_step hwb hx))
    (Conₘ.GLB_nrᵢ_le₀ 𝕄 hχ)
    (Conₘ.GLB_nrᵢ_le_step hwb hχ)

/-- Zero-mode usage (`𝟘ᵐ`): every term is resourced by `𝟘ᶜ` at mode `𝟘ᵐ`. -/
theorem zeroMode_usage (t : GTerm M) : Usage 𝕄 (Conₘ.zero 𝕄) .zeroMode t := by
  induction t with
  | univ => exact .univ
  | nat => exact .nat
  | unit => exact .unit
  | star => exact .star
  | zero => exact .zero
  | var x =>
    have h : Conₘ.single 𝕄 x (Mode.toGrade 𝕄 .zeroMode) = Conₘ.zero 𝕄 := by
      funext y; simp [Conₘ.single, Mode.toGrade, Conₘ.zero]
    rw [← h]
    exact .var
  | succ t ih => exact .succ ih
  | pi p q A B ihA ihB =>
    have hB : Usage 𝕄 (Conₘ.cons (Conₘ.zero 𝕄) (𝕄.mul (Mode.toGrade 𝕄 .zeroMode) q)) .zeroMode B := by
      simp only [Mode.toGrade, 𝕄.zero_mul, Conₘ.cons_zero_zero]
      exact ihB
    have h := Usage.pi (p := p) (q := q) (by simp [Mode.scale]; exact ihA) hB
    simp only [Conₘ.scale_zero, Conₘ.zero_add] at h
    exact h
  | sigma s p q A B ihA ihB =>
    have hB : Usage 𝕄 (Conₘ.cons (Conₘ.zero 𝕄) (𝕄.mul (Mode.toGrade 𝕄 .zeroMode) q)) .zeroMode B := by
      simp only [Mode.toGrade, 𝕄.zero_mul, Conₘ.cons_zero_zero]
      exact ihB
    have h := Usage.sigma (s := s) (p := p) (q := q) (by simp [Mode.scale]; exact ihA) hB
    simp only [Conₘ.scale_zero, Conₘ.zero_add] at h
    exact h
  | lam p t ih =>
    have ht : Usage 𝕄 (Conₘ.cons (Conₘ.zero 𝕄) (𝕄.mul (Mode.toGrade 𝕄 .zeroMode) p)) .zeroMode t := by
      simp only [Mode.toGrade, 𝕄.zero_mul, Conₘ.cons_zero_zero]
      exact ih
    exact .lam ht
  | app p t u iht ihu =>
    have h := Usage.app (p := p) iht (by simp [Mode.scale]; exact ihu)
    simp only [Conₘ.scale_zero, Conₘ.add_zero] at h
    exact h
  | prod s p t u iht ihu =>
    cases s with
    | strong =>
      have h := Usage.prodStrong (p := p) (by simp [Mode.scale]; exact iht) ihu
      have hm : Conₘ.meet 𝕄 (Conₘ.scale 𝕄 p (Conₘ.zero 𝕄)) (Conₘ.zero 𝕄) = Conₘ.zero 𝕄 := by
        funext x; simp [Conₘ.meet, Conₘ.scale, Conₘ.zero, 𝕄.mul_zero, 𝕄.meet_idem]
      rw [hm] at h
      exact h
    | weak =>
      have h := Usage.prodWeak (p := p) (by simp [Mode.scale]; exact iht) ihu
      simp only [Conₘ.scale_zero, Conₘ.zero_add] at h
      exact h
  | fst p t ih =>
    refine .fst ih ?_
    simp only [Mode.toGrade, 𝕄.zero_mul]
    exact 𝕄.le_refl 𝕄.zero
  | snd p t ih => exact .snd ih
  | prodrec r p q A t u ihA iht ihu =>
    have hA : Usage 𝕄 (Conₘ.cons (Conₘ.zero 𝕄) 𝕄.zero) .zeroMode A := by
      rw [Conₘ.cons_zero_zero]; exact ihA
    have h := Usage.prodrec (r := r) (p := p) (q := q) (by simp [Mode.scale]; exact iht) ihu hA
    simp only [Conₘ.scale_zero, Conₘ.zero_add] at h
    exact h
  | unitrec p q A t u ihA iht ihu =>
    have hA : Usage 𝕄 (Conₘ.cons (Conₘ.zero 𝕄) 𝕄.zero) .zeroMode A := by
      rw [Conₘ.cons_zero_zero]; exact ihA
    have h := Usage.unitrec (p := p) (q := q) (by simp [Mode.scale]; exact iht) ihu hA
    simp only [Conₘ.scale_zero, Conₘ.zero_add] at h
    exact h
  | natrec p q r A z s n ihA ihz ihs ihn =>
    have hA : Usage 𝕄 (Conₘ.cons (Conₘ.zero 𝕄) 𝕄.zero) .zeroMode A := by
      rw [Conₘ.cons_zero_zero]; exact ihA
    have h := Usage.natrec_fix (x := 𝕄.one) (p := p) (q := q) (r := r) ihz ihs ihn hA
      (𝕄.le_refl 𝕄.one)
      (by simp only [Mode.toGrade, 𝕄.zero_mul]; exact 𝕄.le_refl 𝕄.zero)
      (Conₘ.le_refl 𝕄 _)
      (by simp only [Conₘ.scale_zero, Conₘ.add_zero]; exact Conₘ.le_refl 𝕄 _)
    simp only [Conₘ.scale_zero, Conₘ.add_zero] at h
    exact h

/-- Any usage at mode `𝟘ᵐ` can be replaced by `𝟘ᶜ`. -/
theorem zeroMode_any_zero {γ : Conₘ M} {t : GTerm M} (h : Usage 𝕄 γ .zeroMode t) :
    Usage 𝕄 (Conₘ.zero 𝕄) .zeroMode t := by
  let _ := h
  exact zeroMode_usage t

/-- Every usage context at mode `𝟘ᵐ` is bounded by `𝟘ᶜ` (`▸-𝟘ᵐ` in `Graded/Usage/Properties.agda`). -/
theorem zeroMode_le_zero {γ : Conₘ M} {t : GTerm M}
    (h : Usage 𝕄 γ .zeroMode t) : Conₘ.le 𝕄 γ (Conₘ.zero 𝕄) := by
  generalize hm : Mode.zeroMode = m at h
  induction h with
  | sub _ hle ih =>
    exact Conₘ.le_trans 𝕄 hle (ih hm)
  | var =>
    subst hm
    intro x
    simp only [Conₘ.single, Mode.toGrade, Conₘ.zero]
    split <;> exact 𝕄.le_refl 𝕄.zero
  | univ | nat | unit | star | zero =>
    exact Conₘ.le_refl 𝕄 _
  | succ _ ih => exact ih hm
  | @pi γA δB m' p q A B _ _ ihA ihB | @sigma γA δB m' s p q A B _ _ ihA ihB =>
    subst hm
    have hA := ihA rfl
    have hB := Conₘ.tail_le_tail 𝕄 (ihB rfl)
    have h1 := Conₘ.scale_mono_right 𝕄 p hA
    rw [Conₘ.scale_zero] at h1
    have hsum := Conₘ.add_mono 𝕄 h1 hB
    rw [Conₘ.zero_add] at hsum
    exact hsum
  | lam _ ih =>
    subst hm
    exact Conₘ.tail_le_tail 𝕄 (ih rfl)
  | @app γf δu m' p f u _ _ iht ihu =>
    subst hm
    have ht := iht rfl
    have hu := ihu rfl
    have h2 := Conₘ.scale_mono_right 𝕄 p hu
    rw [Conₘ.scale_zero] at h2
    have hsum := Conₘ.add_mono 𝕄 ht h2
    rw [Conₘ.add_zero] at hsum
    exact hsum
  | @prodStrong γt δu m' p t1 t2 _ _ iht ihu =>
    subst hm
    have ht := iht rfl
    have hu := ihu rfl
    have h1 := Conₘ.scale_mono_right 𝕄 p ht
    rw [Conₘ.scale_zero] at h1
    have hm0 : Conₘ.meet 𝕄 (Conₘ.zero 𝕄) (Conₘ.zero 𝕄) = Conₘ.zero 𝕄 := by
      funext x; exact 𝕄.meet_idem 𝕄.zero
    have hmeet := Conₘ.meet_mono 𝕄 h1 hu
    rw [hm0] at hmeet
    exact hmeet
  | @prodWeak γt δu m' p t1 t2 _ _ iht ihu
  | @prodrec γt δu ηA m' p _ _ _ _ _ _ _ _ iht ihu _
  | @unitrec γt δu ηA m' p _ _ _ _ _ _ _ iht ihu _ =>
    subst hm
    have ht := iht rfl
    have hu := ihu rfl
    have h1 := Conₘ.scale_mono_right 𝕄 p ht
    rw [Conₘ.scale_zero] at h1
    have hsum := Conₘ.add_mono 𝕄 h1 hu
    rw [Conₘ.zero_add] at hsum
    exact hsum
  | fst _ _ ih | snd _ ih => exact ih hm
  | @natrec_fix γz δs ηn θA χ m' x p q r A z s n _ _ _ _ _ _ hχ1 _ ihz _ ihn _ =>
    subst hm
    have hz := ihz rfl
    have hn := ihn rfl
    have h1 := Conₘ.scale_mono_right 𝕄 x hn
    rw [Conₘ.scale_zero] at h1
    have h2 := Conₘ.le_trans 𝕄 hχ1 hz
    have hsum := Conₘ.add_mono 𝕄 h1 h2
    rw [Conₘ.zero_add] at hsum
    exact hsum

/-- Mode-scaling inequality `p ·ᶜ γ ≤ᶜ (⌜ m ⌝ · p) ·ᶜ γ` when `γ ▸[m ᵐ· p] t` (`▸ᵐ-ᵐ·`). -/
theorem usage_scale_mode_le {γ : Conₘ M} {m : Mode} {p : M} {t : GTerm M}
    (h : Usage 𝕄 γ (Mode.scale 𝕄 m p) t) :
    Conₘ.le 𝕄 (Conₘ.scale 𝕄 p γ) (Conₘ.scale 𝕄 (𝕄.mul (Mode.toGrade 𝕄 m) p) γ) := by
  cases m with
  | oneMode =>
    simp only [Mode.toGrade, 𝕄.one_mul]
    exact Conₘ.le_refl 𝕄 _
  | zeroMode =>
    simp only [Mode.scale_zeroMode] at h
    have h0 := zeroMode_le_zero h
    simp only [Mode.toGrade, 𝕄.zero_mul, Conₘ.zero_scale]
    have h1 := Conₘ.scale_mono_right 𝕄 p h0
    rw [Conₘ.scale_zero] at h1
    exact h1

/-- Scaling mode of a usage derivation (`▸→▸[ᵐ·]`). -/
theorem scale_usage {γ : Conₘ M} {m : Mode} {r : M} {t : GTerm M}
    (h : Usage 𝕄 γ m t) :
    ∃ γ' : Conₘ M, Usage 𝕄 γ' (Mode.scale 𝕄 m r) t ∧
      Conₘ.scale 𝕄 r γ' = Conₘ.scale 𝕄 r γ := by
  cases m with
  | zeroMode =>
    exact ⟨γ, h, rfl⟩
  | oneMode =>
    by_cases hr : r = 𝕄.zero
    · subst hr
      refine ⟨Conₘ.zero 𝕄, ?_, ?_⟩
      · simp only [Mode.scale_zero_grade]
        exact zeroMode_usage t
      · simp only [Conₘ.zero_scale]
    · refine ⟨γ, ?_, rfl⟩
      rw [Mode.scale_oneMode_ne_zero 𝕄 hr]
      exact h

/-- Application when both function and argument are resourced at the same mode `m`. -/
theorem app_same_mode {γ δ : Conₘ M} {m : Mode} {r : M} {f t : GTerm M}
    (hf : Usage 𝕄 δ m f) (ht : Usage 𝕄 γ m t) :
    Usage 𝕄 (Conₘ.add 𝕄 δ (Conₘ.scale 𝕄 r γ)) m (.app r f t) := by
  rcases scale_usage ht (r := r) with ⟨γ', ht', hscale⟩
  rw [← hscale]
  exact .app hf ht'

/-- M2 Theorem 6.2 (`valid-var-usage`): under `HasWellBehavedZero`, if `γ ▸[𝟙ᵐ] var x`,
    then `γ x ≠ 𝟘`. -/
theorem var_usage_ne_zero (hw : 𝕄.HasWellBehavedZero) {γ : Conₘ M} {x : Nat}
    (h : Usage 𝕄 γ .oneMode (.var x)) : γ x ≠ 𝕄.zero := by
  generalize hm : Mode.oneMode = m at h
  generalize ht : GTerm.var x = t at h
  induction h with
  | sub h hle ih =>
    intro h0
    have hle_x := hle x
    rw [h0] at hle_x
    have hgx := hw.zero_le_eq_zero hle_x
    exact ih hm ht hgx
  | var =>
    rename_i m' y
    injection ht with hy
    subst hy; subst hm
    simp only [Conₘ.single, ↓reduceIte, Mode.toGrade]
    exact hw.nonTrivial
  | _ => nomatch ht

/-- Weakening preserves usage (`wkUsage`, `Graded.Usage.Weakening`). -/
theorem wkUsage (ρ : Wk) {γ : Conₘ M} {m : Mode} {t : GTerm M}
    (h : Usage 𝕄 γ m t) : Usage 𝕄 (Conₘ.wk 𝕄 ρ γ) m (GTerm.wk ρ t) := by
  induction h generalizing ρ with
  | sub _ hle ih =>
    exact .sub (ih ρ) (Conₘ.wk_mono 𝕄 ρ hle)
  | var =>
    rw [Conₘ.wk_single]
    exact .var
  | univ => rw [Conₘ.wk_zero]; exact .univ
  | nat => rw [Conₘ.wk_zero]; exact .nat
  | unit => rw [Conₘ.wk_zero]; exact .unit
  | star => rw [Conₘ.wk_zero]; exact .star
  | zero => rw [Conₘ.wk_zero]; exact .zero
  | succ _ ih => exact .succ (ih ρ)
  | pi _ _ ihA ihB =>
    rw [Conₘ.wk_add, Conₘ.wk_scale]
    exact .pi (ihA ρ) (ihB (.lift ρ))
  | sigma _ _ ihA ihB =>
    rw [Conₘ.wk_add, Conₘ.wk_scale]
    exact .sigma (ihA ρ) (ihB (.lift ρ))
  | lam _ ih =>
    exact .lam (ih (.lift ρ))
  | app _ _ iht ihu =>
    rw [Conₘ.wk_add, Conₘ.wk_scale]
    exact .app (iht ρ) (ihu ρ)
  | prodStrong _ _ iht ihu =>
    rw [Conₘ.wk_meet, Conₘ.wk_scale]
    exact .prodStrong (iht ρ) (ihu ρ)
  | prodWeak _ _ iht ihu =>
    rw [Conₘ.wk_add, Conₘ.wk_scale]
    exact .prodWeak (iht ρ) (ihu ρ)
  | fst _ hle ih =>
    exact .fst (ih ρ) hle
  | snd _ ih =>
    exact .snd (ih ρ)
  | prodrec _ _ _ iht ihu ihA =>
    rw [Conₘ.wk_add, Conₘ.wk_scale]
    exact .prodrec (iht ρ) (ihu ρ) (ihA (.lift ρ))
  | unitrec _ _ _ iht ihu ihA =>
    rw [Conₘ.wk_add, Conₘ.wk_scale]
    exact .unitrec (iht ρ) (ihu ρ) (ihA (.lift ρ))
  | @natrec_fix γz δs ηn θA χ m' x p q r A z s n _ _ _ _ hx1 hx2 hχ1 hχ2 ihz ihs ihn ihA =>
    have hχstep : Conₘ.le 𝕄 (Conₘ.wk 𝕄 ρ χ)
        (Conₘ.add 𝕄 (Conₘ.wk 𝕄 ρ δs) (Conₘ.scale 𝕄 r (Conₘ.wk 𝕄 ρ χ))) := by
      rw [← Conₘ.wk_scale, ← Conₘ.wk_add]
      exact Conₘ.wk_mono 𝕄 ρ hχ2
    rw [Conₘ.wk_add, Conₘ.wk_scale]
    exact .natrec_fix (ihz ρ) (ihs ρ) (ihn ρ) (ihA (.lift ρ))
      hx1 hx2 (Conₘ.wk_mono 𝕄 ρ hχ1) hχstep

end Usage

/-! ## 5. Substitution Matrices (`Substₘ`) and M2 Theorem 5.3 (`substₘ_lemma`) -/

/-- Substitution matrices (`Graded.Substitution`): a finite prefix of row usage contexts
    followed by a weakening base `id ρ`. -/
inductive Substₘ (M : Type) where
  | id : Wk → Substₘ M
  | snoc : Substₘ M → Conₘ M → Substₘ M

namespace Substₘ

variable {M : Type} (𝕄 : Modality M)

/-- Vector-matrix multiplication `γ <* Ψ` (`substₘ Ψ γ` in `Graded/Substitution.agda`). -/
def vecMatMul (Ψ : Substₘ M) (γ : Conₘ M) : Conₘ M :=
  match Ψ with
  | .id ρ => Conₘ.wk 𝕄 ρ γ
  | .snoc Ψ δ =>
      Conₘ.add 𝕄 (Conₘ.scale 𝕄 (Conₘ.head γ) δ) (vecMatMul Ψ (Conₘ.tail γ))

/-- The `x`-th row of a substitution matrix `Ψ`. -/
def row : Substₘ M → Nat → Conₘ M
  | .id ρ, x => Conₘ.single 𝕄 (wkVar ρ x) 𝕄.one
  | .snoc _ δ, 0 => δ
  | .snoc Ψ _, x + 1 => row Ψ x

/-- Single-step weakening of a substitution matrix (`wk1Substₘ`). -/
def wk1 : Substₘ M → Substₘ M
  | .id ρ => .id (.step ρ)
  | .snoc Ψ δ => .snoc (wk1 Ψ) (Conₘ.wk 𝕄 (.step .id) δ)

/-- Lifting a substitution matrix under a binder (`liftSubstₘ`). -/
def lift (Ψ : Substₘ M) : Substₘ M :=
  .snoc (wk1 𝕄 Ψ) (Conₘ.cons (Conₘ.zero 𝕄) 𝕄.one)

/-- Identity substitution matrix (`idSubstₘ`). -/
def idMat : Substₘ M := .id .id

/-- Single-term substitution matrix (`sgSubstₘ δ`). -/
def sgMat (δ : Conₘ M) : Substₘ M := .snoc idMat δ

@[simp] theorem vecMatMul_idMat (γ : Conₘ M) :
    vecMatMul 𝕄 idMat γ = γ := rfl

@[simp] theorem vecMatMul_zero (Ψ : Substₘ M) :
    vecMatMul 𝕄 Ψ (Conₘ.zero 𝕄) = Conₘ.zero 𝕄 := by
  induction Ψ with
  | id ρ => exact Conₘ.wk_zero 𝕄 ρ
  | snoc Ψ δ ih =>
    have hh : Conₘ.head (Conₘ.zero 𝕄) = 𝕄.zero := rfl
    have ht : Conₘ.tail (Conₘ.zero 𝕄) = Conₘ.zero 𝕄 := rfl
    simp [vecMatMul, hh, ht, ih]

theorem vecMatMul_add (Ψ : Substₘ M) (γ₁ γ₂ : Conₘ M) :
    vecMatMul 𝕄 Ψ (Conₘ.add 𝕄 γ₁ γ₂) =
      Conₘ.add 𝕄 (vecMatMul 𝕄 Ψ γ₁) (vecMatMul 𝕄 Ψ γ₂) := by
  induction Ψ generalizing γ₁ γ₂ with
  | id ρ => exact Conₘ.wk_add 𝕄 ρ γ₁ γ₂
  | snoc Ψ δ ih =>
    have hh : Conₘ.head (Conₘ.add 𝕄 γ₁ γ₂) = 𝕄.add (Conₘ.head γ₁) (Conₘ.head γ₂) := rfl
    have ht : Conₘ.tail (Conₘ.add 𝕄 γ₁ γ₂) = Conₘ.add 𝕄 (Conₘ.tail γ₁) (Conₘ.tail γ₂) := rfl
    simp only [vecMatMul, hh, ht, Conₘ.add_scale_distrib, ih]
    funext x
    simp only [Conₘ.add, Conₘ.scale]
    rw [𝕄.add_assoc, ← 𝕄.add_assoc (𝕄.mul (Conₘ.head γ₂) (δ x)),
        𝕄.add_comm (𝕄.mul (Conₘ.head γ₂) (δ x)), 𝕄.add_assoc, ← 𝕄.add_assoc]

theorem vecMatMul_scale (Ψ : Substₘ M) (p : M) (γ : Conₘ M) :
    vecMatMul 𝕄 Ψ (Conₘ.scale 𝕄 p γ) =
      Conₘ.scale 𝕄 p (vecMatMul 𝕄 Ψ γ) := by
  induction Ψ generalizing γ with
  | id ρ => exact Conₘ.wk_scale 𝕄 ρ p γ
  | snoc Ψ δ ih =>
    have hh : Conₘ.head (Conₘ.scale 𝕄 p γ) = 𝕄.mul p (Conₘ.head γ) := rfl
    have ht : Conₘ.tail (Conₘ.scale 𝕄 p γ) = Conₘ.scale 𝕄 p (Conₘ.tail γ) := rfl
    simp only [vecMatMul, hh, ht, Conₘ.scale_assoc, Conₘ.scale_add_distrib, ih]

theorem vecMatMul_mono (Ψ : Substₘ M) {γ₁ γ₂ : Conₘ M}
    (h : Conₘ.le 𝕄 γ₁ γ₂) :
    Conₘ.le 𝕄 (vecMatMul 𝕄 Ψ γ₁) (vecMatMul 𝕄 Ψ γ₂) := by
  induction Ψ generalizing γ₁ γ₂ with
  | id ρ => exact Conₘ.wk_mono 𝕄 ρ h
  | snoc Ψ δ ih =>
    exact Conₘ.add_mono 𝕄
      (Conₘ.scale_mono 𝕄 (Conₘ.head_le_head 𝕄 h) (Conₘ.le_refl 𝕄 δ))
      (ih (Conₘ.tail_le_tail 𝕄 h))

theorem vecMatMul_sub_distrib_meet (Ψ : Substₘ M) (γ₁ γ₂ : Conₘ M) :
    Conₘ.le 𝕄 (vecMatMul 𝕄 Ψ (Conₘ.meet 𝕄 γ₁ γ₂))
      (Conₘ.meet 𝕄 (vecMatMul 𝕄 Ψ γ₁) (vecMatMul 𝕄 Ψ γ₂)) := by
  induction Ψ generalizing γ₁ γ₂ with
  | id ρ =>
    simp only [vecMatMul, Conₘ.wk_meet]
    exact Conₘ.le_refl 𝕄 _
  | snoc Ψ δ ih =>
    intro x
    have hh : Conₘ.head (Conₘ.meet 𝕄 γ₁ γ₂) = 𝕄.meet (Conₘ.head γ₁) (Conₘ.head γ₂) := rfl
    have ht : Conₘ.tail (Conₘ.meet 𝕄 γ₁ γ₂) = Conₘ.meet 𝕄 (Conₘ.tail γ₁) (Conₘ.tail γ₂) := rfl
    simp only [vecMatMul, hh, ht, Conₘ.add, Conₘ.scale, Conₘ.meet]
    rw [𝕄.mul_right_distrib_meet]
    have h1 : 𝕄.le
        (𝕄.add (𝕄.meet (𝕄.mul (Conₘ.head γ₁) (δ x)) (𝕄.mul (Conₘ.head γ₂) (δ x)))
          (vecMatMul 𝕄 Ψ (Conₘ.meet 𝕄 (Conₘ.tail γ₁) (Conₘ.tail γ₂)) x))
        (𝕄.add (𝕄.meet (𝕄.mul (Conₘ.head γ₁) (δ x)) (𝕄.mul (Conₘ.head γ₂) (δ x)))
          (𝕄.meet (vecMatMul 𝕄 Ψ (Conₘ.tail γ₁) x) (vecMatMul 𝕄 Ψ (Conₘ.tail γ₂) x))) :=
      𝕄.add_mono_right _ (ih (Conₘ.tail γ₁) (Conₘ.tail γ₂) x)
    have h2 : 𝕄.le
        (𝕄.add (𝕄.meet (𝕄.mul (Conₘ.head γ₁) (δ x)) (𝕄.mul (Conₘ.head γ₂) (δ x)))
          (𝕄.meet (vecMatMul 𝕄 Ψ (Conₘ.tail γ₁) x) (vecMatMul 𝕄 Ψ (Conₘ.tail γ₂) x)))
        (𝕄.meet
          (𝕄.add (𝕄.mul (Conₘ.head γ₁) (δ x)) (vecMatMul 𝕄 Ψ (Conₘ.tail γ₁) x))
          (𝕄.add (𝕄.mul (Conₘ.head γ₂) (δ x)) (vecMatMul 𝕄 Ψ (Conₘ.tail γ₂) x))) :=
      𝕄.le_meet
        (𝕄.add_mono (𝕄.meet_le_left _ _) (𝕄.meet_le_left _ _))
        (𝕄.add_mono (𝕄.meet_le_right _ _) (𝕄.meet_le_right _ _))
    exact 𝕄.le_trans h1 h2

theorem vecMatMul_single (Ψ : Substₘ M) (x : Nat) (p : M) :
    vecMatMul 𝕄 Ψ (Conₘ.single 𝕄 x p) = Conₘ.scale 𝕄 p (row 𝕄 Ψ x) := by
  induction Ψ generalizing x with
  | id ρ =>
    simp only [vecMatMul, row, Conₘ.wk_single, Conₘ.scale_single, 𝕄.mul_one]
  | snoc Ψ δ ih =>
    cases x with
    | zero =>
      have hh : Conₘ.head (Conₘ.single 𝕄 0 p) = p := rfl
      have ht : Conₘ.tail (Conₘ.single 𝕄 0 p) = Conₘ.zero 𝕄 := rfl
      simp only [vecMatMul, row, hh, ht, vecMatMul_zero, Conₘ.add_zero]
    | succ x =>
      have hh : Conₘ.head (Conₘ.single 𝕄 (x + 1) p) = 𝕄.zero := rfl
      have ht : Conₘ.tail (Conₘ.single 𝕄 (x + 1) p) = Conₘ.single 𝕄 x p := by
        rw [Conₘ.single_succ]; rfl
      simp only [vecMatMul, row, hh, ht, Conₘ.zero_scale, Conₘ.zero_add, ih]

theorem vecMatMul_wk1 (Ψ : Substₘ M) (γ : Conₘ M) :
    vecMatMul 𝕄 (wk1 𝕄 Ψ) γ = Conₘ.wk 𝕄 (.step .id) (vecMatMul 𝕄 Ψ γ) := by
  induction Ψ generalizing γ with
  | id ρ => rfl
  | snoc Ψ δ ih =>
    simp only [wk1, vecMatMul, ih, Conₘ.wk_add, Conₘ.wk_scale]

theorem vecMatMul_lift (Ψ : Substₘ M) (γ : Conₘ M) (q : M) :
    vecMatMul 𝕄 (lift 𝕄 Ψ) (Conₘ.cons γ q) = Conₘ.cons (vecMatMul 𝕄 Ψ γ) q := by
  have hh : Conₘ.head (Conₘ.cons γ q) = q := rfl
  have ht : Conₘ.tail (Conₘ.cons γ q) = γ := rfl
  simp only [lift, vecMatMul, hh, ht, vecMatMul_wk1, Conₘ.wk,
    Conₘ.cons_scale, Conₘ.scale_zero, 𝕄.mul_one, Conₘ.cons_add, Conₘ.zero_add, 𝕄.add_zero]

theorem row_wk1 (Ψ : Substₘ M) (x : Nat) :
    row 𝕄 (wk1 𝕄 Ψ) x = Conₘ.wk 𝕄 (.step .id) (row 𝕄 Ψ x) := by
  induction Ψ generalizing x with
  | id ρ =>
    simp only [wk1, row, wkVar, Conₘ.wk, Conₘ.single_succ]
  | snoc Ψ δ ih =>
    cases x with
    | zero => rfl
    | succ x => exact ih x

@[simp] theorem row_lift_zero (Ψ : Substₘ M) :
    row 𝕄 (lift 𝕄 Ψ) 0 = Conₘ.single 𝕄 0 𝕄.one := by
  simp [lift, row]

theorem row_lift_succ (Ψ : Substₘ M) (x : Nat) :
    row 𝕄 (lift 𝕄 Ψ) (x + 1) = Conₘ.wk 𝕄 (.step .id) (row 𝕄 Ψ x) := by
  simp [lift, row, row_wk1]

end Substₘ

/-! ### Well-Resourced Substitutions and M2 Theorem 5.3 (`substₘ_lemma`) -/

/-- Uniformly well-resourced substitution (`∀ x, row Ψ x ▸[𝟙ᵐ] σ x`). -/
def SubstUsageOne {M : Type} (𝕄 : Modality M) (Ψ : Substₘ M) (σ : GTerm.GSubst M) : Prop :=
  ∀ x : Nat, Usage 𝕄 (Substₘ.row 𝕄 Ψ x) .oneMode (σ x)

/-- Context-filtered well-resourced substitution (`Ψ ▶[ ⌞ γ ⌟ᶜ ] σ` in M2 Section 5.2):
    every variable `x` with non-zero usage `γ x ≠ 𝟘` is resourced by `row Ψ x` at `𝟙ᵐ`. -/
def SubstUsage {M : Type} (𝕄 : Modality M) (Ψ : Substₘ M) (γ : Conₘ M)
    (σ : GTerm.GSubst M) : Prop :=
  ∀ x : Nat, γ x ≠ 𝕄.zero → Usage 𝕄 (Substₘ.row 𝕄 Ψ x) .oneMode (σ x)

namespace Usage

variable {M : Type} {𝕄 : Modality M}

theorem substUsage_of_one {Ψ : Substₘ M} {γ : Conₘ M} {σ : GTerm.GSubst M}
    (h : SubstUsageOne 𝕄 Ψ σ) : SubstUsage 𝕄 Ψ γ σ :=
  fun x _ ↦ h x

theorem substUsageOne_id : SubstUsageOne 𝕄 (Substₘ.idMat) GTerm.idSubst := by
  intro x
  simp only [Substₘ.idMat, Substₘ.row, wkVar, GTerm.idSubst]
  exact Usage.var (m := .oneMode)

theorem substUsageOne_lift {Ψ : Substₘ M} {σ : GTerm.GSubst M}
    (hσ : SubstUsageOne 𝕄 Ψ σ) :
    SubstUsageOne 𝕄 (Substₘ.lift 𝕄 Ψ) (GTerm.liftSubst σ) := by
  intro x
  cases x with
  | zero =>
    rw [Substₘ.row_lift_zero]
    exact Usage.var (m := .oneMode)
  | succ x =>
    rw [Substₘ.row_lift_succ]
    exact wkUsage (.step .id) (hσ x)

theorem substUsage_lift {Ψ : Substₘ M} {γ : Conₘ M} {q : M} {σ : GTerm.GSubst M}
    (hσ : SubstUsage 𝕄 Ψ γ σ) :
    SubstUsage 𝕄 (Substₘ.lift 𝕄 Ψ) (Conₘ.cons γ q) (GTerm.liftSubst σ) := by
  intro x hx
  cases x with
  | zero =>
    rw [Substₘ.row_lift_zero]
    exact Usage.var (m := .oneMode)
  | succ x =>
    rw [Substₘ.row_lift_succ]
    exact wkUsage (.step .id) (hσ x hx)

theorem substUsage_le (hw : 𝕄.HasWellBehavedZero) {Ψ : Substₘ M} {γ δ : Conₘ M}
    {σ : GTerm.GSubst M} (hle : Conₘ.le 𝕄 δ γ) (hσ : SubstUsage 𝕄 Ψ δ σ) :
    SubstUsage 𝕄 Ψ γ σ := by
  intro x hgx
  apply hσ x
  intro hdx
  have hle_x := hle x
  rw [hdx] at hle_x
  exact hgx (hw.zero_le_eq_zero hle_x)

theorem substUsage_add_left (hw : 𝕄.HasWellBehavedZero) {Ψ : Substₘ M} {γ δ : Conₘ M}
    {σ : GTerm.GSubst M} (hσ : SubstUsage 𝕄 Ψ (Conₘ.add 𝕄 γ δ) σ) :
    SubstUsage 𝕄 Ψ γ σ := by
  intro x hgx
  apply hσ x
  intro hadd
  exact hgx (hw.add_positive_left hadd)

theorem substUsage_add_right (hw : 𝕄.HasWellBehavedZero) {Ψ : Substₘ M} {γ δ : Conₘ M}
    {σ : GTerm.GSubst M} (hσ : SubstUsage 𝕄 Ψ (Conₘ.add 𝕄 γ δ) σ) :
    SubstUsage 𝕄 Ψ δ σ := by
  intro x hdx
  apply hσ x
  intro hadd
  exact hdx (hw.add_positive_right hadd)

theorem substUsage_scale (hw : 𝕄.HasWellBehavedZero) {Ψ : Substₘ M} {p : M} {γ : Conₘ M}
    {σ : GTerm.GSubst M} (hp : p ≠ 𝕄.zero)
    (hσ : SubstUsage 𝕄 Ψ (Conₘ.scale 𝕄 p γ) σ) :
    SubstUsage 𝕄 Ψ γ σ := by
  intro x hgx
  apply hσ x
  intro hmul
  rcases hw.zero_product hmul with rfl | h0
  · exact hp rfl
  · exact hgx h0

theorem substUsage_meet_left (hw : 𝕄.HasWellBehavedZero) {Ψ : Substₘ M} {γ δ : Conₘ M}
    {σ : GTerm.GSubst M} (hσ : SubstUsage 𝕄 Ψ (Conₘ.meet 𝕄 γ δ) σ) :
    SubstUsage 𝕄 Ψ γ σ :=
  substUsage_le hw (fun x ↦ 𝕄.meet_le_left (γ x) (δ x)) hσ

theorem substUsage_meet_right (hw : 𝕄.HasWellBehavedZero) {Ψ : Substₘ M} {γ δ : Conₘ M}
    {σ : GTerm.GSubst M} (hσ : SubstUsage 𝕄 Ψ (Conₘ.meet 𝕄 γ δ) σ) :
    SubstUsage 𝕄 Ψ δ σ :=
  substUsage_le hw (fun x ↦ 𝕄.meet_le_right (γ x) (δ x)) hσ

/-- M2 Theorem 5.3 (`substₘ-lemma` for uniform substitutions, holding for ANY modality `𝕄`
    without requiring `HasWellBehavedZero`). -/
theorem substₘ_lemma_one {Ψ : Substₘ M} {σ : GTerm.GSubst M} {γ : Conₘ M} {m : Mode} {t : GTerm M}
    (hσ : SubstUsageOne 𝕄 Ψ σ) (ht : Usage 𝕄 γ m t) :
    Usage 𝕄 (Substₘ.vecMatMul 𝕄 Ψ γ) m (GTerm.subst σ t) := by
  induction ht generalizing Ψ σ with
  | sub _ hle ih =>
    exact .sub (ih hσ) (Substₘ.vecMatMul_mono 𝕄 Ψ hle)
  | var =>
    rename_i m' x
    rw [Substₘ.vecMatMul_single]
    cases m' with
    | zeroMode =>
      simp only [Mode.toGrade, Conₘ.zero_scale, GTerm.subst]
      exact zeroMode_usage (σ x)
    | oneMode =>
      simp only [Mode.toGrade, Conₘ.one_scale, GTerm.subst]
      exact hσ x
  | univ => rw [Substₘ.vecMatMul_zero]; exact .univ
  | nat => rw [Substₘ.vecMatMul_zero]; exact .nat
  | unit => rw [Substₘ.vecMatMul_zero]; exact .unit
  | star => rw [Substₘ.vecMatMul_zero]; exact .star
  | zero => rw [Substₘ.vecMatMul_zero]; exact .zero
  | succ _ ih => exact .succ (ih hσ)
  | pi _ _ ihA ihB =>
    rw [Substₘ.vecMatMul_add, Substₘ.vecMatMul_scale]
    have hB := ihB (substUsageOne_lift hσ)
    rw [Substₘ.vecMatMul_lift] at hB
    exact .pi (ihA hσ) hB
  | sigma _ _ ihA ihB =>
    rw [Substₘ.vecMatMul_add, Substₘ.vecMatMul_scale]
    have hB := ihB (substUsageOne_lift hσ)
    rw [Substₘ.vecMatMul_lift] at hB
    exact .sigma (ihA hσ) hB
  | lam _ ih =>
    have ht' := ih (substUsageOne_lift hσ)
    rw [Substₘ.vecMatMul_lift] at ht'
    exact .lam ht'
  | app _ _ iht ihu =>
    rw [Substₘ.vecMatMul_add, Substₘ.vecMatMul_scale]
    exact .app (iht hσ) (ihu hσ)
  | @prodStrong γt δu m' p t1 t2 _ _ iht ihu =>
    have hm := Substₘ.vecMatMul_sub_distrib_meet 𝕄 Ψ (Conₘ.scale 𝕄 p γt) δu
    rw [Substₘ.vecMatMul_scale] at hm
    exact .sub (.prodStrong (iht hσ) (ihu hσ)) hm
  | prodWeak _ _ iht ihu =>
    rw [Substₘ.vecMatMul_add, Substₘ.vecMatMul_scale]
    exact .prodWeak (iht hσ) (ihu hσ)
  | fst _ hle ih =>
    exact .fst (ih hσ) hle
  | snd _ ih =>
    exact .snd (ih hσ)
  | @prodrec γt δu ηA m' r p q A t1 u1 _ _ _ iht ihu _ =>
    rw [Substₘ.vecMatMul_add, Substₘ.vecMatMul_scale]
    have hA : Usage 𝕄 (Conₘ.cons (Conₘ.zero 𝕄) 𝕄.zero) .zeroMode
        (GTerm.subst (GTerm.liftSubst σ) A) := by
      rw [Conₘ.cons_zero_zero]
      exact zeroMode_usage _
    exact .prodrec (iht hσ) (ihu hσ) hA
  | @unitrec γt δu ηA m' p q A t1 u1 _ _ _ iht ihu _ =>
    rw [Substₘ.vecMatMul_add, Substₘ.vecMatMul_scale]
    have hA : Usage 𝕄 (Conₘ.cons (Conₘ.zero 𝕄) 𝕄.zero) .zeroMode
        (GTerm.subst (GTerm.liftSubst σ) A) := by
      rw [Conₘ.cons_zero_zero]
      exact zeroMode_usage _
    exact .unitrec (iht hσ) (ihu hσ) hA
  | @natrec_fix γz δs ηn θA χ m' x p q r A z s n _ _ _ _ hx1 hx2 hχ1 hχ2 ihz ihs ihn _ =>
    have hA : Usage 𝕄 (Conₘ.cons (Conₘ.zero 𝕄) 𝕄.zero) .zeroMode
        (GTerm.subst (GTerm.liftSubst σ) A) := by
      rw [Conₘ.cons_zero_zero]
      exact zeroMode_usage _
    have hχstep : Conₘ.le 𝕄 (Substₘ.vecMatMul 𝕄 Ψ χ)
        (Conₘ.add 𝕄 (Substₘ.vecMatMul 𝕄 Ψ δs)
          (Conₘ.scale 𝕄 r (Substₘ.vecMatMul 𝕄 Ψ χ))) := by
      rw [← Substₘ.vecMatMul_scale, ← Substₘ.vecMatMul_add]
      exact Substₘ.vecMatMul_mono 𝕄 Ψ hχ2
    rw [Substₘ.vecMatMul_add, Substₘ.vecMatMul_scale]
    exact .natrec_fix (ihz hσ) (ihs hσ) (ihn hσ) hA
      hx1 hx2 (Substₘ.vecMatMul_mono 𝕄 Ψ hχ1) hχstep

/-- M2 Theorem 5.3 (`substₘ-lemma`): under `HasWellBehavedZero`, simultaneous substitution
    preserves usage (`Ψ ▶[ ⌞ γ ⌟ᶜ ] σ → γ ▸[m] t → (γ <* Ψ) ▸[m] t[σ]`). -/
theorem substₘ_lemma (hw : 𝕄.HasWellBehavedZero) {Ψ : Substₘ M} {σ : GTerm.GSubst M}
    {γ : Conₘ M} {m : Mode} {t : GTerm M}
    (hσ : SubstUsage 𝕄 Ψ γ σ) (ht : Usage 𝕄 γ m t) :
    Usage 𝕄 (Substₘ.vecMatMul 𝕄 Ψ γ) m (GTerm.subst σ t) := by
  induction ht generalizing Ψ σ with
  | sub _ hle ih =>
    exact .sub (ih (substUsage_le hw hle hσ)) (Substₘ.vecMatMul_mono 𝕄 Ψ hle)
  | var =>
    rename_i m' x
    rw [Substₘ.vecMatMul_single]
    cases m' with
    | zeroMode =>
      simp only [Mode.toGrade, Conₘ.zero_scale, GTerm.subst]
      exact zeroMode_usage (σ x)
    | oneMode =>
      simp only [Mode.toGrade, Conₘ.one_scale, GTerm.subst]
      apply hσ x
      simp only [Conₘ.single, ↓reduceIte, Mode.toGrade]
      exact hw.nonTrivial
  | univ => rw [Substₘ.vecMatMul_zero]; exact .univ
  | nat => rw [Substₘ.vecMatMul_zero]; exact .nat
  | unit => rw [Substₘ.vecMatMul_zero]; exact .unit
  | star => rw [Substₘ.vecMatMul_zero]; exact .star
  | zero => rw [Substₘ.vecMatMul_zero]; exact .zero
  | succ _ ih => exact .succ (ih hσ)
  | pi _ _ ihA ihB =>
    rename_i γA δB m' p q A B _ _
    rw [Substₘ.vecMatMul_add, Substₘ.vecMatMul_scale]
    have hB := ihB (substUsage_lift (q := 𝕄.mul (Mode.toGrade 𝕄 m') q)
      (substUsage_add_right hw hσ))
    rw [Substₘ.vecMatMul_lift] at hB
    by_cases hp : p = 𝕄.zero
    · subst hp
      simp only [Conₘ.zero_scale]
      have hA0 : Usage 𝕄 (Conₘ.zero 𝕄) (Mode.scale 𝕄 m' 𝕄.zero) (GTerm.subst σ A) := by
        simp only [Mode.scale_zero_grade]; exact zeroMode_usage _
      have hpi := Usage.pi (p := 𝕄.zero) hA0 hB
      simp only [Conₘ.zero_scale] at hpi
      exact hpi
    · have hσA := substUsage_scale hw hp (substUsage_add_left hw hσ)
      exact .pi (ihA hσA) hB
  | sigma _ _ ihA ihB =>
    rename_i γA δB m' s p q A B _ _
    rw [Substₘ.vecMatMul_add, Substₘ.vecMatMul_scale]
    have hB := ihB (substUsage_lift (q := 𝕄.mul (Mode.toGrade 𝕄 m') q)
      (substUsage_add_right hw hσ))
    rw [Substₘ.vecMatMul_lift] at hB
    by_cases hp : p = 𝕄.zero
    · subst hp
      simp only [Conₘ.zero_scale]
      have hA0 : Usage 𝕄 (Conₘ.zero 𝕄) (Mode.scale 𝕄 m' 𝕄.zero) (GTerm.subst σ A) := by
        simp only [Mode.scale_zero_grade]; exact zeroMode_usage _
      have hsig := Usage.sigma (s := s) (p := 𝕄.zero) hA0 hB
      simp only [Conₘ.zero_scale] at hsig
      exact hsig
    · have hσA := substUsage_scale hw hp (substUsage_add_left hw hσ)
      exact .sigma (ihA hσA) hB
  | lam _ ih =>
    rename_i γ' m' p body _
    have ht' := ih (substUsage_lift (q := 𝕄.mul (Mode.toGrade 𝕄 m') p) hσ)
    rw [Substₘ.vecMatMul_lift] at ht'
    exact .lam ht'
  | app _ _ iht ihu =>
    rename_i γf δu m' p f u _ _
    rw [Substₘ.vecMatMul_add, Substₘ.vecMatMul_scale]
    have hf := iht (substUsage_add_left hw hσ)
    by_cases hp : p = 𝕄.zero
    · subst hp
      simp only [Conₘ.zero_scale]
      have hu0 : Usage 𝕄 (Conₘ.zero 𝕄) (Mode.scale 𝕄 m' 𝕄.zero) (GTerm.subst σ u) := by
        simp only [Mode.scale_zero_grade]; exact zeroMode_usage _
      have happ := Usage.app (p := 𝕄.zero) hf hu0
      simp only [Conₘ.zero_scale] at happ
      exact happ
    · have hσu := substUsage_scale hw hp (substUsage_add_right hw hσ)
      exact .app hf (ihu hσu)
  | @prodStrong γt δu m' p t1 t2 _ _ iht ihu =>
    have hm := Substₘ.vecMatMul_sub_distrib_meet 𝕄 Ψ (Conₘ.scale 𝕄 p γt) δu
    rw [Substₘ.vecMatMul_scale] at hm
    have hu := ihu (substUsage_meet_right hw hσ)
    by_cases hp : p = 𝕄.zero
    · subst hp
      have ht0 : Usage 𝕄 (Conₘ.zero 𝕄) (Mode.scale 𝕄 m' 𝕄.zero) (GTerm.subst σ t1) := by
        simp only [Mode.scale_zero_grade]; exact zeroMode_usage _
      have hpS := Usage.prodStrong (p := 𝕄.zero) ht0 hu
      simp only [Conₘ.zero_scale] at hpS hm ⊢
      exact .sub hpS hm
    · have hσt := substUsage_scale hw hp (substUsage_meet_left hw hσ)
      exact .sub (.prodStrong (iht hσt) hu) hm
  | @prodWeak γt δu m' p t1 t2 _ _ iht ihu =>
    rw [Substₘ.vecMatMul_add, Substₘ.vecMatMul_scale]
    have hu := ihu (substUsage_add_right hw hσ)
    by_cases hp : p = 𝕄.zero
    · subst hp
      simp only [Conₘ.zero_scale]
      have ht0 : Usage 𝕄 (Conₘ.zero 𝕄) (Mode.scale 𝕄 m' 𝕄.zero) (GTerm.subst σ t1) := by
        simp only [Mode.scale_zero_grade]; exact zeroMode_usage _
      have hpW := Usage.prodWeak (p := 𝕄.zero) ht0 hu
      simp only [Conₘ.zero_scale] at hpW
      exact hpW
    · have hσt := substUsage_scale hw hp (substUsage_add_left hw hσ)
      exact .prodWeak (iht hσt) hu
  | fst _ hle ih =>
    exact .fst (ih hσ) hle
  | snd _ ih =>
    exact .snd (ih hσ)
  | @prodrec γt δu ηA m' r p q A t1 u1 _ _ _ iht ihu _ =>
    rw [Substₘ.vecMatMul_add, Substₘ.vecMatMul_scale]
    have hu := ihu (substUsage_add_right hw hσ)
    have hA : Usage 𝕄 (Conₘ.cons (Conₘ.zero 𝕄) 𝕄.zero) .zeroMode
        (GTerm.subst (GTerm.liftSubst σ) A) := by
      rw [Conₘ.cons_zero_zero]; exact zeroMode_usage _
    by_cases hr : r = 𝕄.zero
    · subst hr
      simp only [Conₘ.zero_scale]
      have ht0 : Usage 𝕄 (Conₘ.zero 𝕄) (Mode.scale 𝕄 m' 𝕄.zero) (GTerm.subst σ t1) := by
        simp only [Mode.scale_zero_grade]; exact zeroMode_usage _
      have hpr := Usage.prodrec (r := 𝕄.zero) (p := p) (q := q) ht0 hu hA
      simp only [Conₘ.zero_scale] at hpr
      exact hpr
    · have hσt := substUsage_scale hw hr (substUsage_add_left hw hσ)
      exact .prodrec (iht hσt) hu hA
  | @unitrec γt δu ηA m' p q A t1 u1 _ _ _ iht ihu _ =>
    rw [Substₘ.vecMatMul_add, Substₘ.vecMatMul_scale]
    have hu := ihu (substUsage_add_right hw hσ)
    have hA : Usage 𝕄 (Conₘ.cons (Conₘ.zero 𝕄) 𝕄.zero) .zeroMode
        (GTerm.subst (GTerm.liftSubst σ) A) := by
      rw [Conₘ.cons_zero_zero]; exact zeroMode_usage _
    by_cases hp : p = 𝕄.zero
    · subst hp
      simp only [Conₘ.zero_scale]
      have ht0 : Usage 𝕄 (Conₘ.zero 𝕄) (Mode.scale 𝕄 m' 𝕄.zero) (GTerm.subst σ t1) := by
        simp only [Mode.scale_zero_grade]; exact zeroMode_usage _
      have hur := Usage.unitrec (p := 𝕄.zero) (q := q) ht0 hu hA
      simp only [Conₘ.zero_scale] at hur
      exact hur
    · have hσt := substUsage_scale hw hp (substUsage_add_left hw hσ)
      exact .unitrec (iht hσt) hu hA
  | @natrec_fix γz δs ηn θA χ m' x p q r A z s n _ _ _ _ hx1 hx2 hχ1 hχ2 ihz ihs ihn _ =>
    have hA : Usage 𝕄 (Conₘ.cons (Conₘ.zero 𝕄) 𝕄.zero) .zeroMode
        (GTerm.subst (GTerm.liftSubst σ) A) := by
      rw [Conₘ.cons_zero_zero]; exact zeroMode_usage _
    have hχstep : Conₘ.le 𝕄 (Substₘ.vecMatMul 𝕄 Ψ χ)
        (Conₘ.add 𝕄 (Substₘ.vecMatMul 𝕄 Ψ δs)
          (Conₘ.scale 𝕄 r (Substₘ.vecMatMul 𝕄 Ψ χ))) := by
      rw [← Substₘ.vecMatMul_scale, ← Substₘ.vecMatMul_add]
      exact Substₘ.vecMatMul_mono 𝕄 Ψ hχ2
    have hσχ := substUsage_add_right hw hσ
    have hσz := substUsage_le hw hχ1 hσχ
    have hσs := substUsage_add_left hw (substUsage_le hw hχ2 hσχ)
    have hx_ne : x ≠ 𝕄.zero := by
      intro hx0
      have hx1' := hx1
      rw [hx0] at hx1'
      exact hw.nonTrivial (hw.zero_le_eq_zero hx1')
    have hσn := substUsage_scale hw hx_ne (substUsage_add_left hw hσ)
    rw [Substₘ.vecMatMul_add, Substₘ.vecMatMul_scale]
    exact .natrec_fix (ihz hσz) (ihs hσs) (ihn hσn) hA
      hx1 hx2 (Substₘ.vecMatMul_mono 𝕄 Ψ hχ1) hχstep

/-- Single-term substitution lemma (`sgSubstₘ-lemma₂` in `Graded/Substitution/Properties.agda`):
    if `γ ∙ (⌜ m ⌝ · p) ▸[m] t` and `δ ▸[m ᵐ· p] u`, then `γ +ᶜ p ·ᶜ δ ▸[m] t[u]₀`. -/
theorem sgSubstₘ_lemma (hw : 𝕄.HasWellBehavedZero) {γ δ : Conₘ M} {m : Mode} {p : M}
    {t u : GTerm M}
    (ht : Usage 𝕄 (Conₘ.cons γ (𝕄.mul (Mode.toGrade 𝕄 m) p)) m t)
    (hu : Usage 𝕄 δ (Mode.scale 𝕄 m p) u) :
    Usage 𝕄 (Conₘ.add 𝕄 γ (Conₘ.scale 𝕄 p δ)) m (GTerm.subst0 t u) := by
  have hσ : SubstUsage 𝕄 (Substₘ.sgMat δ) (Conₘ.cons γ (𝕄.mul (Mode.toGrade 𝕄 m) p))
      (GTerm.sgSubst u) := by
    intro x hx
    cases x with
    | zero =>
      simp only [Conₘ.cons] at hx
      have hm : Mode.toGrade 𝕄 m ≠ 𝕄.zero := by
        intro hm0
        apply hx
        rw [hm0, 𝕄.zero_mul]
      have hp : p ≠ 𝕄.zero := by
        intro hp0
        apply hx
        rw [hp0, 𝕄.mul_zero]
      have hm1 : m = .oneMode := by
        cases m with
        | zeroMode => exact False.elim (hm rfl)
        | oneMode => rfl
      subst hm1
      rw [Mode.scale_oneMode_ne_zero 𝕄 hp] at hu
      exact hu
    | succ x =>
      exact Usage.var (m := .oneMode)
  have hsub := substₘ_lemma hw hσ ht
  have heq : Substₘ.vecMatMul 𝕄 (Substₘ.sgMat δ) (Conₘ.cons γ (𝕄.mul (Mode.toGrade 𝕄 m) p)) =
      Conₘ.add 𝕄 (Conₘ.scale 𝕄 (𝕄.mul (Mode.toGrade 𝕄 m) p) δ) γ := rfl
  rw [heq] at hsub
  have hle : Conₘ.le 𝕄 (Conₘ.add 𝕄 γ (Conₘ.scale 𝕄 p δ))
      (Conₘ.add 𝕄 (Conₘ.scale 𝕄 (𝕄.mul (Mode.toGrade 𝕄 m) p) δ) γ) := by
    rw [Conₘ.add_comm 𝕄 γ]
    exact Conₘ.add_mono 𝕄 (usage_scale_mode_le hu) (Conₘ.le_refl 𝕄 γ)
  exact .sub hsub hle

/-- Uniform single-term substitution lemma (`sgSubstₘ-lemma₃` in M2, holding for ANY modality
    `𝕄` without requiring `HasWellBehavedZero`). -/
theorem sgSubstₘ_lemma_one {γ δ : Conₘ M} {m : Mode} {p : M} {t u : GTerm M}
    (ht : Usage 𝕄 (Conₘ.cons γ (𝕄.mul (Mode.toGrade 𝕄 m) p)) m t)
    (hu : Usage 𝕄 δ .oneMode u) :
    Usage 𝕄 (Conₘ.add 𝕄 γ (Conₘ.scale 𝕄 (𝕄.mul (Mode.toGrade 𝕄 m) p) δ)) m (GTerm.subst0 t u) := by
  have hσ : SubstUsageOne 𝕄 (Substₘ.sgMat δ) (GTerm.sgSubst u) := by
    intro x
    cases x with
    | zero => exact hu
    | succ x => exact Usage.var (m := .oneMode)
  have hsub := substₘ_lemma_one hσ ht
  have heq : Substₘ.vecMatMul 𝕄 (Substₘ.sgMat δ) (Conₘ.cons γ (𝕄.mul (Mode.toGrade 𝕄 m) p)) =
      Conₘ.add 𝕄 γ (Conₘ.scale 𝕄 (𝕄.mul (Mode.toGrade 𝕄 m) p) δ) := by
    change Conₘ.add 𝕄 (Conₘ.scale 𝕄 (𝕄.mul (Mode.toGrade 𝕄 m) p) δ) γ = _
    exact Conₘ.add_comm 𝕄 _ _
  rw [← heq]
  exact hsub

end Usage

/-! ## 6. Inversion Lemmas, Graded Reduction (`GStep`), and M2 Theorem 5.4 (`usagePresTerm`) -/

namespace Usage

variable {M : Type} {𝕄 : Modality M}

theorem inv_zero {γ : Conₘ M} {m : Mode} (h : Usage 𝕄 γ m .zero) :
    Conₘ.le 𝕄 γ (Conₘ.zero 𝕄) := by
  generalize ht : (GTerm.zero : GTerm M) = t at h
  induction h with
  | sub _ hle ih => exact Conₘ.le_trans 𝕄 hle (ih ht)
  | zero => exact Conₘ.le_refl 𝕄 _
  | _ => nomatch ht

theorem inv_star {γ : Conₘ M} {m : Mode} (h : Usage 𝕄 γ m .star) :
    Conₘ.le 𝕄 γ (Conₘ.zero 𝕄) := by
  generalize ht : (GTerm.star : GTerm M) = t at h
  induction h with
  | sub _ hle ih => exact Conₘ.le_trans 𝕄 hle (ih ht)
  | star => exact Conₘ.le_refl 𝕄 _
  | _ => nomatch ht

theorem inv_succ {γ : Conₘ M} {m : Mode} {n : GTerm M}
    (h : Usage 𝕄 γ m (.succ n)) : Usage 𝕄 γ m n := by
  generalize ht : GTerm.succ n = t at h
  induction h with
  | sub _ hle ih => exact .sub (ih ht) hle
  | succ hn =>
    injection ht with hn_eq
    subst hn_eq
    exact hn
  | _ => nomatch ht

theorem inv_lam {γ : Conₘ M} {m : Mode} {p : M} {body : GTerm M}
    (h : Usage 𝕄 γ m (.lam p body)) :
    Usage 𝕄 (Conₘ.cons γ (𝕄.mul (Mode.toGrade 𝕄 m) p)) m body := by
  generalize ht : GTerm.lam p body = t at h
  induction h with
  | sub _ hle ih =>
    exact .sub (ih ht) (Conₘ.cons_le_cons 𝕄 hle (𝕄.le_refl _))
  | lam hbody =>
    injection ht with hp hbody_eq
    subst hp; subst hbody_eq
    exact hbody
  | _ => nomatch ht

theorem inv_app {γ : Conₘ M} {m : Mode} {p : M} {f u : GTerm M}
    (h : Usage 𝕄 γ m (.app p f u)) :
    ∃ γf δu : Conₘ M,
      Usage 𝕄 γf m f ∧
      Usage 𝕄 δu (Mode.scale 𝕄 m p) u ∧
      Conₘ.le 𝕄 γ (Conₘ.add 𝕄 γf (Conₘ.scale 𝕄 p δu)) := by
  generalize ht : GTerm.app p f u = t at h
  induction h with
  | sub _ hle ih =>
    rcases ih ht with ⟨γf, δu, hf, hu, hle'⟩
    exact ⟨γf, δu, hf, hu, Conₘ.le_trans 𝕄 hle hle'⟩
  | app hf hu =>
    injection ht with hp hf_eq hu_eq
    subst hp; subst hf_eq; subst hu_eq
    exact ⟨_, _, hf, hu, Conₘ.le_refl 𝕄 _⟩
  | _ => nomatch ht

theorem inv_prodStrong {γ : Conₘ M} {m : Mode} {p : M} {t1 t2 : GTerm M}
    (h : Usage 𝕄 γ m (.prod .strong p t1 t2)) :
    ∃ γ1 γ2 : Conₘ M,
      Usage 𝕄 γ1 (Mode.scale 𝕄 m p) t1 ∧
      Usage 𝕄 γ2 m t2 ∧
      Conₘ.le 𝕄 γ (Conₘ.meet 𝕄 (Conₘ.scale 𝕄 p γ1) γ2) := by
  generalize ht : GTerm.prod .strong p t1 t2 = t at h
  induction h with
  | sub _ hle ih =>
    rcases ih ht with ⟨γ1, γ2, h1, h2, hle'⟩
    exact ⟨γ1, γ2, h1, h2, Conₘ.le_trans 𝕄 hle hle'⟩
  | prodStrong h1 h2 =>
    injection ht with _ hp h1_eq h2_eq
    subst hp; subst h1_eq; subst h2_eq
    exact ⟨_, _, h1, h2, Conₘ.le_refl 𝕄 _⟩
  | _ => nomatch ht

theorem inv_prodWeak {γ : Conₘ M} {m : Mode} {p : M} {t1 t2 : GTerm M}
    (h : Usage 𝕄 γ m (.prod .weak p t1 t2)) :
    ∃ γ1 γ2 : Conₘ M,
      Usage 𝕄 γ1 (Mode.scale 𝕄 m p) t1 ∧
      Usage 𝕄 γ2 m t2 ∧
      Conₘ.le 𝕄 γ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 p γ1) γ2) := by
  generalize ht : GTerm.prod .weak p t1 t2 = t at h
  induction h with
  | sub _ hle ih =>
    rcases ih ht with ⟨γ1, γ2, h1, h2, hle'⟩
    exact ⟨γ1, γ2, h1, h2, Conₘ.le_trans 𝕄 hle hle'⟩
  | prodWeak h1 h2 =>
    injection ht with _ hp h1_eq h2_eq
    subst hp; subst h1_eq; subst h2_eq
    exact ⟨_, _, h1, h2, Conₘ.le_refl 𝕄 _⟩
  | _ => nomatch ht

theorem inv_fst {γ : Conₘ M} {m : Mode} {p : M} {u : GTerm M}
    (h : Usage 𝕄 γ m (.fst p u)) :
    Usage 𝕄 γ m u ∧ 𝕄.le (𝕄.mul (Mode.toGrade 𝕄 m) p) (Mode.toGrade 𝕄 m) := by
  generalize ht : GTerm.fst p u = t at h
  induction h with
  | sub _ hle ih =>
    rcases ih ht with ⟨hu, hcond⟩
    exact ⟨.sub hu hle, hcond⟩
  | fst hu hcond =>
    injection ht with hp hu_eq
    subst hp; subst hu_eq
    exact ⟨hu, hcond⟩
  | _ => nomatch ht

theorem inv_snd {γ : Conₘ M} {m : Mode} {p : M} {u : GTerm M}
    (h : Usage 𝕄 γ m (.snd p u)) : Usage 𝕄 γ m u := by
  generalize ht : GTerm.snd p u = t at h
  induction h with
  | sub _ hle ih => exact .sub (ih ht) hle
  | snd hu =>
    injection ht with _ hu_eq
    subst hu_eq
    exact hu
  | _ => nomatch ht

theorem inv_prodrec {γ : Conₘ M} {m : Mode} {r p q : M} {A t1 u1 : GTerm M}
    (h : Usage 𝕄 γ m (.prodrec r p q A t1 u1)) :
    ∃ γt δu ηA : Conₘ M,
      Usage 𝕄 γt (Mode.scale 𝕄 m r) t1 ∧
      Usage 𝕄 δu m u1 ∧
      Usage 𝕄 (Conₘ.cons ηA 𝕄.zero) .zeroMode A ∧
      Conₘ.le 𝕄 γ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 r γt) δu) := by
  generalize ht : GTerm.prodrec r p q A t1 u1 = t at h
  induction h with
  | sub _ hle ih =>
    rcases ih ht with ⟨γt, δu, ηA, ht1, hu1, hA, hle'⟩
    exact ⟨γt, δu, ηA, ht1, hu1, hA, Conₘ.le_trans 𝕄 hle hle'⟩
  | prodrec ht1 hu1 hA =>
    injection ht with hr hp hq hA_eq ht1_eq hu1_eq
    subst hr; subst hp; subst hq; subst hA_eq; subst ht1_eq; subst hu1_eq
    exact ⟨_, _, _, ht1, hu1, hA, Conₘ.le_refl 𝕄 _⟩
  | _ => nomatch ht

theorem inv_unitrec {γ : Conₘ M} {m : Mode} {p q : M} {A t1 u1 : GTerm M}
    (h : Usage 𝕄 γ m (.unitrec p q A t1 u1)) :
    ∃ γt δu ηA : Conₘ M,
      Usage 𝕄 γt (Mode.scale 𝕄 m p) t1 ∧
      Usage 𝕄 δu m u1 ∧
      Usage 𝕄 (Conₘ.cons ηA 𝕄.zero) .zeroMode A ∧
      Conₘ.le 𝕄 γ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 p γt) δu) := by
  generalize ht : GTerm.unitrec p q A t1 u1 = t at h
  induction h with
  | sub _ hle ih =>
    rcases ih ht with ⟨γt, δu, ηA, ht1, hu1, hA, hle'⟩
    exact ⟨γt, δu, ηA, ht1, hu1, hA, Conₘ.le_trans 𝕄 hle hle'⟩
  | unitrec ht1 hu1 hA =>
    injection ht with hp hq hA_eq ht1_eq hu1_eq
    subst hp; subst hq; subst hA_eq; subst ht1_eq; subst hu1_eq
    exact ⟨_, _, _, ht1, hu1, hA, Conₘ.le_refl 𝕄 _⟩
  | _ => nomatch ht

end Usage

/-- One-step weak-head reduction on graded terms (`Graded/Reduction.agda`). -/
inductive GStep {M : Type} (𝕄 : Modality M) : GTerm M → GTerm M → Prop where
  | app_subst {p t t' u} :
      GStep 𝕄 t t' →
      GStep 𝕄 (.app p t u) (.app p t' u)
  | beta {p t u} :
      GStep 𝕄 (.app p (.lam p t) u) (GTerm.subst0 t u)
  | fst_subst {p t t'} :
      GStep 𝕄 t t' →
      GStep 𝕄 (.fst p t) (.fst p t')
  | snd_subst {p t t'} :
      GStep 𝕄 t t' →
      GStep 𝕄 (.snd p t) (.snd p t')
  | sigma_beta1 {p t u} :
      GStep 𝕄 (.fst p (.prod .strong p t u)) t
  | sigma_beta2 {p t u} :
      GStep 𝕄 (.snd p (.prod .strong p t u)) u
  | prodrec_subst {r p q A t t' u} :
      GStep 𝕄 t t' →
      GStep 𝕄 (.prodrec r p q A t u) (.prodrec r p q A t' u)
  | prodrec_beta {r p q A t1 t2 u} :
      GStep 𝕄 (.prodrec r p q A (.prod .weak p t1 t2) u)
        (.app r (.app (𝕄.mul r p) u t1) t2)
  | unitrec_subst {p q A t t' u} :
      GStep 𝕄 t t' →
      GStep 𝕄 (.unitrec p q A t u) (.unitrec p q A t' u)
  | unitrec_beta {p q A u} :
      GStep 𝕄 (.unitrec p q A .star u) u
  | natrec_subst {p q r A z s n n'} :
      GStep 𝕄 n n' →
      GStep 𝕄 (.natrec p q r A z s n) (.natrec p q r A z s n')
  | natrec_zero {p q r A z s} :
      GStep 𝕄 (.natrec p q r A z s .zero) z
  | natrec_succ {p q r A z s n} :
      GStep 𝕄 (.natrec p q r A z s (.succ n))
        (.app r (.app p s n) (.natrec p q r A z s n))

/-- Reflexive-transitive closure of `GStep`. -/
inductive GStar {M : Type} (𝕄 : Modality M) : GTerm M → GTerm M → Prop where
  | refl (t : GTerm M) : GStar 𝕄 t t
  | step {t t' u : GTerm M} : GStep 𝕄 t t' → GStar 𝕄 t' u → GStar 𝕄 t u

namespace Usage

variable {M : Type} {𝕄 : Modality M}

/-- Inversion of `natrec` usage. -/
theorem inv_natrec {γ : Conₘ M} {m : Mode} {p q r : M} {A z s n : GTerm M}
    (h : Usage 𝕄 γ m (.natrec p q r A z s n)) :
    ∃ (γz δs ηn θA χ : Conₘ M) (x : M),
      Usage 𝕄 γz m z ∧
      Usage 𝕄 δs m s ∧
      Usage 𝕄 ηn m n ∧
      Usage 𝕄 (Conₘ.cons θA 𝕄.zero) .zeroMode A ∧
      𝕄.le x 𝕄.one ∧
      𝕄.le (𝕄.mul (Mode.toGrade 𝕄 m) x) (𝕄.mul (Mode.toGrade 𝕄 m) (𝕄.add p (𝕄.mul r x))) ∧
      Conₘ.le 𝕄 χ γz ∧
      Conₘ.le 𝕄 χ (Conₘ.add 𝕄 δs (Conₘ.scale 𝕄 r χ)) ∧
      Conₘ.le 𝕄 γ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 x ηn) χ) := by
  generalize ht : GTerm.natrec p q r A z s n = t at h
  induction h with
  | sub _ hle ih =>
    rcases ih ht with ⟨γz, δs, ηn, θA, χ, x, hz, hs, hn, hA, hx1, hx2, hχ1, hχ2, hle'⟩
    exact ⟨γz, δs, ηn, θA, χ, x, hz, hs, hn, hA, hx1, hx2, hχ1, hχ2,
      Conₘ.le_trans 𝕄 hle hle'⟩
  | natrec_fix hz hs hn hA hx1 hx2 hχ1 hχ2 =>
    injection ht with hp hq hr hA_eq hz_eq hs_eq hn_eq
    subst hp; subst hq; subst hr; subst hA_eq; subst hz_eq; subst hs_eq; subst hn_eq
    exact ⟨_, _, _, _, _, _, hz, hs, hn, hA, hx1, hx2, hχ1, hχ2, Conₘ.le_refl 𝕄 _⟩
  | _ => nomatch ht

/-- M2 Theorem 5.4 (`usagePresTerm` / Subject Reduction for Usage, `Graded/Reduction.agda`):
    under `HasWellBehavedZero`, graded reduction preserves usage (`γ ▸[m] t → t ⇒ u → γ ▸[m] u`). -/
theorem usagePresTerm (hw : 𝕄.HasWellBehavedZero) {γ : Conₘ M} {m : Mode} {t u : GTerm M}
    (ht : Usage 𝕄 γ m t) (hstep : GStep 𝕄 t u) : Usage 𝕄 γ m u := by
  induction hstep generalizing γ m with
  | app_subst hred ih =>
    rcases inv_app ht with ⟨γf, δu, hf, hu, hle⟩
    exact .sub (.app (ih hf) hu) hle
  | beta =>
    rcases inv_app ht with ⟨γf, δu, hf, hu, hle⟩
    have hbody := inv_lam hf
    exact .sub (sgSubstₘ_lemma hw hbody hu) hle
  | fst_subst hred ih =>
    rcases inv_fst ht with ⟨hu, hcond⟩
    exact .fst (ih hu) hcond
  | snd_subst hred ih =>
    exact .snd (ih (inv_snd ht))
  | sigma_beta1 =>
    rename_i p t1 t2
    rcases inv_fst ht with ⟨hprod, hcond⟩
    rcases inv_prodStrong hprod with ⟨γ1, γ2, ht1, _, hle⟩
    have hle1 : Conₘ.le 𝕄 γ (Conₘ.scale 𝕄 p γ1) :=
      Conₘ.le_trans 𝕄 hle (fun x ↦ 𝕄.meet_le_left _ _)
    cases m with
    | zeroMode =>
      have h0 := zeroMode_le_zero ht
      exact .sub (zeroMode_usage t1) h0
    | oneMode =>
      simp only [Mode.toGrade, 𝕄.one_mul] at hcond
      have hp_ne : p ≠ 𝕄.zero := by
        intro hp0
        rw [hp0] at hcond
        exact hw.nonTrivial (hw.zero_le_eq_zero hcond)
      rw [Mode.scale_oneMode_ne_zero 𝕄 hp_ne] at ht1
      have hp1 : Conₘ.le 𝕄 (Conₘ.scale 𝕄 p γ1) γ1 := by
        have hp1' := Conₘ.scale_mono 𝕄 hcond (Conₘ.le_refl 𝕄 γ1)
        rw [Conₘ.one_scale] at hp1'
        exact hp1'
      exact .sub ht1 (Conₘ.le_trans 𝕄 hle1 hp1)
  | sigma_beta2 =>
    rcases inv_prodStrong (inv_snd ht) with ⟨γ1, γ2, _, ht2, hle⟩
    have hle2 : Conₘ.le 𝕄 γ γ2 :=
      Conₘ.le_trans 𝕄 hle (fun x ↦ 𝕄.meet_le_right _ _)
    exact .sub ht2 hle2
  | prodrec_subst hred ih =>
    rcases inv_prodrec ht with ⟨γt, δu, ηA, ht1, hu1, hA, hle⟩
    exact .sub (.prodrec (ih ht1) hu1 hA) hle
  | prodrec_beta =>
    rename_i r p q A t1 t2 u1
    rcases inv_prodrec ht with ⟨γt, δu, _, hprod, hu1, _, hle⟩
    rcases inv_prodWeak hprod with ⟨γ1, γ2, ht1, ht2, hle_prod⟩
    rw [Mode.scale_mul hw] at ht1
    have happ1 : Usage 𝕄 (Conₘ.add 𝕄 δu (Conₘ.scale 𝕄 (𝕄.mul r p) γ1)) m
        (.app (𝕄.mul r p) u1 t1) := .app hu1 ht1
    have happ2 : Usage 𝕄
        (Conₘ.add 𝕄 (Conₘ.add 𝕄 δu (Conₘ.scale 𝕄 (𝕄.mul r p) γ1)) (Conₘ.scale 𝕄 r γ2)) m
        (.app r (.app (𝕄.mul r p) u1 t1) t2) := .app happ1 ht2
    have hle_total : Conₘ.le 𝕄 γ
        (Conₘ.add 𝕄 (Conₘ.add 𝕄 δu (Conₘ.scale 𝕄 (𝕄.mul r p) γ1)) (Conₘ.scale 𝕄 r γ2)) := by
      have hstep1 : Conₘ.le 𝕄 γ
          (Conₘ.add 𝕄 (Conₘ.scale 𝕄 r (Conₘ.add 𝕄 (Conₘ.scale 𝕄 p γ1) γ2)) δu) :=
        Conₘ.le_trans 𝕄 hle
          (Conₘ.add_mono 𝕄 (Conₘ.scale_mono_right 𝕄 r hle_prod) (Conₘ.le_refl 𝕄 δu))
      have heq : Conₘ.add 𝕄 (Conₘ.scale 𝕄 r (Conₘ.add 𝕄 (Conₘ.scale 𝕄 p γ1) γ2)) δu =
          Conₘ.add 𝕄 (Conₘ.add 𝕄 δu (Conₘ.scale 𝕄 (𝕄.mul r p) γ1)) (Conₘ.scale 𝕄 r γ2) := by
        rw [Conₘ.scale_add_distrib, ← Conₘ.scale_assoc,
            Conₘ.add_comm 𝕄 _ δu, Conₘ.add_assoc]
      rw [← heq]
      exact hstep1
    exact .sub happ2 hle_total
  | unitrec_subst hred ih =>
    rcases inv_unitrec ht with ⟨γt, δu, ηA, ht1, hu1, hA, hle⟩
    exact .sub (.unitrec (ih ht1) hu1 hA) hle
  | unitrec_beta =>
    rename_i p q A u1
    rcases inv_unitrec ht with ⟨γt, δu, _, hstar, hu1, _, hle⟩
    have h0 := inv_star hstar
    have hle_u : Conₘ.le 𝕄 γ δu := by
      have hscale := Conₘ.scale_mono_right 𝕄 p h0
      rw [Conₘ.scale_zero] at hscale
      have h1 := Conₘ.add_mono 𝕄 hscale (Conₘ.le_refl 𝕄 δu)
      rw [Conₘ.zero_add] at h1
      exact Conₘ.le_trans 𝕄 hle h1
    exact .sub hu1 hle_u
  | natrec_subst hred ih =>
    rcases inv_natrec ht with ⟨γz, δs, ηn, θA, χ, x, hz, hs, hn, hA, hx1, hx2, hχ1, hχ2, hle⟩
    exact .sub (.natrec_fix hz hs (ih hn) hA hx1 hx2 hχ1 hχ2) hle
  | natrec_zero =>
    rcases inv_natrec ht with ⟨γz, _, ηn, _, χ, x, hz, _, hn, _, _, _, hχ1, _, hle⟩
    have hn0 := inv_zero hn
    have h1 : Conₘ.le 𝕄 (Conₘ.add 𝕄 (Conₘ.scale 𝕄 x ηn) χ) χ := by
      have hscale := Conₘ.scale_mono_right 𝕄 x hn0
      rw [Conₘ.scale_zero] at hscale
      have hsum := Conₘ.add_mono 𝕄 hscale (Conₘ.le_refl 𝕄 χ)
      rw [Conₘ.zero_add] at hsum
      exact hsum
    exact .sub hz (Conₘ.le_trans 𝕄 hle (Conₘ.le_trans 𝕄 h1 hχ1))
  | natrec_succ =>
    rename_i p q r A z s n
    cases m with
    | zeroMode =>
      exact .sub (zeroMode_usage _) (zeroMode_le_zero ht)
    | oneMode =>
      rcases inv_natrec ht with ⟨γz, δs, ηn, θA, χ, x, hz, hs, hsucc, hA, hx1, hx2, hχ1, hχ2, hle⟩
      have hn := inv_succ hsucc
      have hrec : Usage 𝕄 (Conₘ.add 𝕄 (Conₘ.scale 𝕄 x ηn) χ) .oneMode (.natrec p q r A z s n) :=
        .natrec_fix hz hs hn hA hx1 hx2 hχ1 hχ2
      have happ1 := app_same_mode (r := p) hs hn
      have happ2 := app_same_mode (r := r) happ1 hrec
      have hx2' : 𝕄.le x (𝕄.add p (𝕄.mul r x)) := by
        simpa only [Mode.toGrade, 𝕄.one_mul] using hx2
      have hbound : Conₘ.le 𝕄 (Conₘ.add 𝕄 (Conₘ.scale 𝕄 x ηn) χ)
          (Conₘ.add 𝕄 (Conₘ.add 𝕄 δs (Conₘ.scale 𝕄 p ηn))
            (Conₘ.scale 𝕄 r (Conₘ.add 𝕄 (Conₘ.scale 𝕄 x ηn) χ))) := by
        intro y
        simp only [Conₘ.add, Conₘ.scale]
        have hxy : 𝕄.le (𝕄.mul x (ηn y)) (𝕄.mul (𝕄.add p (𝕄.mul r x)) (ηn y)) :=
          𝕄.mul_mono_left (ηn y) hx2'
        rw [𝕄.right_distrib, 𝕄.mul_assoc] at hxy
        have hχy : 𝕄.le (χ y) (𝕄.add (δs y) (𝕄.mul r (χ y))) := hχ2 y
        have hsum := 𝕄.add_mono hxy hχy
        have heq : 𝕄.add (𝕄.add (𝕄.mul p (ηn y)) (𝕄.mul r (𝕄.mul x (ηn y))))
            (𝕄.add (δs y) (𝕄.mul r (χ y))) =
            𝕄.add (𝕄.add (δs y) (𝕄.mul p (ηn y)))
              (𝕄.mul r (𝕄.add (𝕄.mul x (ηn y)) (χ y))) := by
          rw [𝕄.left_distrib, 𝕄.add_assoc,
              ← 𝕄.add_assoc (𝕄.mul r (𝕄.mul x (ηn y))),
              𝕄.add_comm (𝕄.mul r (𝕄.mul x (ηn y))) (δs y),
              𝕄.add_assoc, ← 𝕄.add_assoc (𝕄.mul p (ηn y)),
              𝕄.add_comm (𝕄.mul p (ηn y)) (δs y)]
        rw [← heq]
        exact hsum
      exact .sub happ2 (Conₘ.le_trans 𝕄 hle hbound)

/-- Multi-step subject reduction for usage (`γ ▸[m] t → t ⇒* u → γ ▸[m] u`). -/
theorem usagePresStar (hw : 𝕄.HasWellBehavedZero) {γ : Conₘ M} {m : Mode} {t u : GTerm M}
    (ht : Usage 𝕄 γ m t) (hstar : GStar 𝕄 t u) : Usage 𝕄 γ m u := by
  induction hstar with
  | refl _ => exact ht
  | step hstep _ ih => exact ih (usagePresTerm hw ht hstep)

/-- M2 Counterexample (`no-subject-reduction` in `Graded/Reduction.agda` line 76):
    if weak unit had an η-reduction rule `unitrec 𝟙 𝟘 ℕ (var 0) zero ↦ zero` on a variable,
    then subject reduction would fail for any modality where `¬ (𝟙 ≤ 𝟘)` (such as `Linearity`). -/
theorem no_subject_reduction_unit_eta (hnot : ¬ 𝕄.le 𝕄.one 𝕄.zero) :
    let γ' : Conₘ M := Conₘ.single 𝕄 0 𝕄.one
    let t' : GTerm M := .unitrec 𝕄.one 𝕄.zero .nat (.var 0) .zero
    let u' : GTerm M := .zero
    Usage 𝕄 γ' .oneMode t' ∧ ¬ Usage 𝕄 γ' .oneMode u' := by
  intro γ' t' u'
  refine ⟨?_, ?_⟩
  · have hvar : Usage 𝕄 γ' (Mode.scale 𝕄 .oneMode 𝕄.one) (.var 0) := by
      by_cases h10 : 𝕄.one = 𝕄.zero
      · exfalso; exact hnot (by rw [h10]; exact 𝕄.le_refl 𝕄.zero)
      · rw [Mode.scale_oneMode_ne_zero 𝕄 h10]
        exact Usage.var (m := .oneMode)
    have hzero : Usage 𝕄 (Conₘ.zero 𝕄) .oneMode .zero := .zero
    have hA : Usage 𝕄 (Conₘ.cons (Conₘ.zero 𝕄) 𝕄.zero) .zeroMode .nat := by
      rw [Conₘ.cons_zero_zero]; exact .nat
    have hur := Usage.unitrec (p := 𝕄.one) (q := 𝕄.zero) hvar hzero hA
    simp only [Conₘ.one_scale, Conₘ.add_zero] at hur
    exact hur
  · intro hu'
    have hle := inv_zero hu'
    have h0 := hle 0
    simp only [γ', Conₘ.single, ↓reduceIte, Conₘ.zero] at h0
    exact hnot h0

end Usage

end FeasibleUnivalence
