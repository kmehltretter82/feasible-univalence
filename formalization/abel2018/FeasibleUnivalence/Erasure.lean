import FeasibleUnivalence.Modality
import FeasibleUnivalence.Usage

/-!
# M2 (Section 6): Extraction, Untyped Target Language, and Erasure Soundness

This module formalizes Section 6 of:
- **M2**: Andreas Abel, Nils Anders Danielsson, and Oskar Eriksson,
  *A Graded Modal Dependent Type Theory with a Universe and Erasure, Formalized*
  (ICFP 2023 / JFP 2026 extended version, `Graded.Erasure.*`).

Specifically, we formalize:
1. **The Untyped Target Calculus (`TargetTerm`, M2 Section 6.1 / `Graded.Erasure.Target`)**:
   - Call-by-name (`nonStrict`) and call-by-value (`strict`) evaluation (`Strictness`),
   - Target terms (`var`, `lam`, `app`, `prod`, `fst`, `snd`, `prodrec`, `zero`, `succ`,
     `natrec`, `star`, `unitrec`, `undef`),
   - Syntactic variable occurrence (`HasX`), weakening (`wk`), capture-avoiding
     parallel substitution (`subst`), values (`Value`), numerals (`Numeral`, `suck`),
   - Small-step operational semantics (`TargetStep`, `TargetStar`, and full numeral
     reduction `TargetStarNum`).
2. **The Extraction Function (`erase`, M2 Section 6.1 / `Graded.Erasure.Extraction`)**:
   - Grade-directed erasure of types, `𝟘`-graded arguments, first projections/components
     of `𝟘`-graded pairs, and `𝟘`-graded unit/product eliminators,
   - Commutation of extraction with weakening (`wk_erase_comm`) and substitution
     (`subst_erase_comm`, `subst0_erase_comm`).
3. **Erasure of Unused Variables (M2 Theorem 6.4 / `Graded.Erasure.Extraction.Properties.Usage`)**:
   - Invariance of extraction under substitutions that only modify `𝟘`-graded variables
     (`erase_subst_erased`),
   - **M2 Theorem 6.4 (`erased_not_hasX`)**: under `HasWellBehavedZero`, if `γ ▸[𝟙ᵐ] t`
     and `γ x = 𝟘`, then `x` does not occur free in `erase 𝕄 remove str t`.
4. **Operational Simulation & Logical Relation for Erasure (M2 Section 6.2, Theorems 6.8–6.9)**:
   - Step-by-step operational simulation (`erase_gstep_sim`) under
     `HasWellBehavedZero` and `NoErasedMatches`,
   - Reducibility relation for natural numbers (`ErasedRelNat`, `t ® v ∷ℕ`),
   - Semantic type witnesses (`SemType`) and the type-indexed erasure logical relation
     (`ErasedRel`, `ErasedRelGraded`),
   - Backwards closure under source and target reduction (`erasedRel_backwards_closed`)
     and grade subsumption (`subsumption_erasedRelGraded`),
   - **M2 Theorem 6.8 (`fundamentalErased`)**: the fundamental lemma of the erasure
     logical relation for well-typed, well-resourced graded terms,
   - **M2 Theorem 6.9 (`soundness_nat` and `soundness_nat_canonical`)**: soundness of
     erasure for closed programs of type `ℕ`.
5. **Scope Counterexamples (M2 Section 6.3)**:
   - Formalized counterexamples showing why `HasWellBehavedZero` (`zero_divisor_breaks_erasure`)
     and the restriction against open erased matches (`erased_match_open_counterexample`)
     are necessary.
-/

namespace FeasibleUnivalence

open Abel2018

/-! ## 1. Untyped Target Language (`Graded.Erasure.Target`) -/

/-- Evaluation strategy of the target language: call-by-value (`strict`) or
    call-by-name (`nonStrict`). -/
inductive Strictness : Type where
  | strict : Strictness
  | nonStrict : Strictness
  deriving DecidableEq, Repr

/-- Untyped target language terms (`Graded.Erasure.Target.Term`).
    In alignment with `GTerm` in `Usage.lean` (and `Abel2018`), `prodrec` and `natrec`
    take their branch/step arguments as curried functions; `prodrec` and `natrec` carry
    boolean erasure flags (`pz`, `rz`) recording whether the eliminated components had
    grade `𝟘` so that their β-rules match extracted applications. -/
inductive TargetTerm : Type where
  | var : Nat → TargetTerm
  | lam : TargetTerm → TargetTerm
  | app : Strictness → TargetTerm → TargetTerm → TargetTerm
  | prod : TargetTerm → TargetTerm → TargetTerm
  | fst : TargetTerm → TargetTerm
  | snd : TargetTerm → TargetTerm
  | prodrec : Bool → Strictness → Bool → TargetTerm → TargetTerm → TargetTerm
  | zero : TargetTerm
  | succ : TargetTerm → TargetTerm
  | natrec : Bool → Strictness → Bool → Bool → TargetTerm → TargetTerm → TargetTerm → TargetTerm
  | star : TargetTerm
  | unitrec : TargetTerm → TargetTerm → TargetTerm
  | undef : TargetTerm
  deriving DecidableEq, Repr

/-- Application of a target term to an erased (`𝟘`-graded) argument
    (`Graded.Erasure.Extraction.app-𝟘′`). -/
def appZero (remove : Bool) (str : Strictness) (t : TargetTerm) : TargetTerm :=
  if remove then t else .app str t .undef

/-- Application helper selecting `appZero` when `isZero = true` and `.app str` otherwise. -/
def appOrZero (remove : Bool) (str : Strictness) (isZero : Bool)
    (t u : TargetTerm) : TargetTerm :=
  if isZero then appZero remove str t else .app str t u

namespace TargetTerm

/-- Syntactic variable occurrence `HasX x v` (`Graded.Erasure.Target.HasX`). -/
inductive HasX : Nat → TargetTerm → Prop where
  | var (x : Nat) : HasX x (.var x)
  | lam {x : Nat} {t : TargetTerm} :
      HasX (x + 1) t → HasX x (.lam t)
  | app_left {x : Nat} {s : Strictness} {t u : TargetTerm} :
      HasX x t → HasX x (.app s t u)
  | app_right {x : Nat} {s : Strictness} {t u : TargetTerm} :
      HasX x u → HasX x (.app s t u)
  | prod_left {x : Nat} {t u : TargetTerm} :
      HasX x t → HasX x (.prod t u)
  | prod_right {x : Nat} {t u : TargetTerm} :
      HasX x u → HasX x (.prod t u)
  | fst {x : Nat} {t : TargetTerm} :
      HasX x t → HasX x (.fst t)
  | snd {x : Nat} {t : TargetTerm} :
      HasX x t → HasX x (.snd t)
  | prodrec_left {x : Nat} {rem : Bool} {s : Strictness} {pz : Bool} {t u : TargetTerm} :
      HasX x t → HasX x (.prodrec rem s pz t u)
  | prodrec_right {x : Nat} {rem : Bool} {s : Strictness} {pz : Bool} {t u : TargetTerm} :
      HasX x u → HasX x (.prodrec rem s pz t u)
  | succ {x : Nat} {t : TargetTerm} :
      HasX x t → HasX x (.succ t)
  | natrec_zero {x : Nat} {rem : Bool} {str : Strictness} {pz rz : Bool} {z s n : TargetTerm} :
      HasX x z → HasX x (.natrec rem str pz rz z s n)
  | natrec_succ {x : Nat} {rem : Bool} {str : Strictness} {pz rz : Bool} {z s n : TargetTerm} :
      HasX x s → HasX x (.natrec rem str pz rz z s n)
  | natrec_arg {x : Nat} {rem : Bool} {str : Strictness} {pz rz : Bool} {z s n : TargetTerm} :
      HasX x n → HasX x (.natrec rem str pz rz z s n)
  | unitrec_left {x : Nat} {t u : TargetTerm} :
      HasX x t → HasX x (.unitrec t u)
  | unitrec_right {x : Nat} {t u : TargetTerm} :
      HasX x u → HasX x (.unitrec t u)

@[simp]
theorem not_hasX_zero (x : Nat) : ¬ HasX x .zero := by
  intro h; cases h

@[simp]
theorem not_hasX_star (x : Nat) : ¬ HasX x .star := by
  intro h; cases h

@[simp]
theorem not_hasX_undef (x : Nat) : ¬ HasX x .undef := by
  intro h; cases h

theorem hasX_var_iff (x y : Nat) : HasX x (.var y) ↔ x = y := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; exact .var x

theorem not_hasX_appZero {x : Nat} {remove : Bool} {str : Strictness} {t : TargetTerm}
    (h : ¬ HasX x t) : ¬ HasX x (appZero remove str t) := by
  unfold appZero
  split
  · exact h
  · intro hx
    cases hx with
    | app_left h1 => exact h h1
    | app_right h2 => cases h2

/-- Weakening of target terms using `Wk` from `Abel2018`. -/
def wk (ρ : Wk) : TargetTerm → TargetTerm
  | .var x => .var (wkVar ρ x)
  | .lam t => .lam (wk (.lift ρ) t)
  | .app s t u => .app s (wk ρ t) (wk ρ u)
  | .prod t u => .prod (wk ρ t) (wk ρ u)
  | .fst t => .fst (wk ρ t)
  | .snd t => .snd (wk ρ t)
  | .prodrec rem s pz t u => .prodrec rem s pz (wk ρ t) (wk ρ u)
  | .zero => .zero
  | .succ t => .succ (wk ρ t)
  | .natrec rem str pz rz z s n => .natrec rem str pz rz (wk ρ z) (wk ρ s) (wk ρ n)
  | .star => .star
  | .unitrec t u => .unitrec (wk ρ t) (wk ρ u)
  | .undef => .undef

def wk1 : TargetTerm → TargetTerm := wk (.step .id)

theorem wkVar_to_wk {ρ ρ' : Wk} (h : ∀ x, wkVar ρ x = wkVar ρ' x) :
    ∀ t : TargetTerm, wk ρ t = wk ρ' t
  | .var x => congrArg TargetTerm.var (h x)
  | .lam t => congrArg TargetTerm.lam (wkVar_to_wk (wkVar_lift h) t)
  | .app s t u => by simp [wk, wkVar_to_wk h t, wkVar_to_wk h u]
  | .prod t u => by simp [wk, wkVar_to_wk h t, wkVar_to_wk h u]
  | .fst t => congrArg TargetTerm.fst (wkVar_to_wk h t)
  | .snd t => congrArg TargetTerm.snd (wkVar_to_wk h t)
  | .prodrec rem s pz t u => by simp [wk, wkVar_to_wk h t, wkVar_to_wk h u]
  | .zero => rfl
  | .succ t => congrArg TargetTerm.succ (wkVar_to_wk h t)
  | .natrec rem str pz rz z s n => by
      simp [wk, wkVar_to_wk h z, wkVar_to_wk h s, wkVar_to_wk h n]
  | .star => rfl
  | .unitrec t u => by simp [wk, wkVar_to_wk h t, wkVar_to_wk h u]
  | .undef => rfl

@[simp]
theorem wk_id : ∀ t : TargetTerm, wk .id t = t
  | .var _ => rfl
  | .lam t => by rw [wk, wkVar_to_wk wkVar_lift_id t, wk_id t]
  | .app s t u => by rw [wk, wk_id t, wk_id u]
  | .prod t u => by rw [wk, wk_id t, wk_id u]
  | .fst t => congrArg TargetTerm.fst (wk_id t)
  | .snd t => congrArg TargetTerm.snd (wk_id t)
  | .prodrec rem s pz t u => by rw [wk, wk_id t, wk_id u]
  | .zero => rfl
  | .succ t => congrArg TargetTerm.succ (wk_id t)
  | .natrec rem str pz rz z s n => by rw [wk, wk_id z, wk_id s, wk_id n]
  | .star => rfl
  | .unitrec t u => by rw [wk, wk_id t, wk_id u]
  | .undef => rfl

theorem wk_comp : ∀ (ρ ρ' : Wk) (t : TargetTerm),
    wk ρ (wk ρ' t) = wk (compWk ρ ρ') t
  | ρ, ρ', .var x => congrArg TargetTerm.var (wkVar_comp ρ ρ' x)
  | ρ, ρ', .lam t => by simp [wk, wk_comp (.lift ρ) (.lift ρ') t, compWk]
  | ρ, ρ', .app s t u => by simp [wk, wk_comp ρ ρ' t, wk_comp ρ ρ' u]
  | ρ, ρ', .prod t u => by simp [wk, wk_comp ρ ρ' t, wk_comp ρ ρ' u]
  | ρ, ρ', .fst t => congrArg TargetTerm.fst (wk_comp ρ ρ' t)
  | ρ, ρ', .snd t => congrArg TargetTerm.snd (wk_comp ρ ρ' t)
  | ρ, ρ', .prodrec rem s pz t u => by simp [wk, wk_comp ρ ρ' t, wk_comp ρ ρ' u]
  | _, _, .zero => rfl
  | ρ, ρ', .succ t => congrArg TargetTerm.succ (wk_comp ρ ρ' t)
  | ρ, ρ', .natrec rem str pz rz z s n => by
      simp [wk, wk_comp ρ ρ' z, wk_comp ρ ρ' s, wk_comp ρ ρ' n]
  | _, _, .star => rfl
  | ρ, ρ', .unitrec t u => by simp [wk, wk_comp ρ ρ' t, wk_comp ρ ρ' u]
  | _, _, .undef => rfl

theorem wk1_wk_eq_lift_wk1 (ρ : Wk) (t : TargetTerm) :
    wk1 (wk ρ t) = wk (.lift ρ) (wk1 t) := by
  unfold wk1
  rw [wk_comp (.step .id) ρ t, wk_comp (.lift ρ) (.step .id) t, lift_step_comp ρ]

/-- Parallel substitutions on target terms. -/
abbrev TSubst := Nat → TargetTerm

def liftSubst (σ : TSubst) : TSubst
  | 0 => .var 0
  | n + 1 => wk1 (σ n)

def subst (σ : TSubst) : TargetTerm → TargetTerm
  | .var x => σ x
  | .lam t => .lam (subst (liftSubst σ) t)
  | .app s t u => .app s (subst σ t) (subst σ u)
  | .prod t u => .prod (subst σ t) (subst σ u)
  | .fst t => .fst (subst σ t)
  | .snd t => .snd (subst σ t)
  | .prodrec rem s pz t u => .prodrec rem s pz (subst σ t) (subst σ u)
  | .zero => .zero
  | .succ t => .succ (subst σ t)
  | .natrec rem str pz rz z s n =>
      .natrec rem str pz rz (subst σ z) (subst σ s) (subst σ n)
  | .star => .star
  | .unitrec t u => .unitrec (subst σ t) (subst σ u)
  | .undef => .undef

def idSubst : TSubst := TargetTerm.var

def consSubst (σ : TSubst) (a : TargetTerm) : TSubst
  | 0 => a
  | n + 1 => σ n

def sgSubst (a : TargetTerm) : TSubst := consSubst idSubst a

def wkSubst (ρ : Wk) (σ : TSubst) : TSubst := fun n ↦ wk ρ (σ n)

def substWk (σ : TSubst) (ρ : Wk) : TSubst := fun n ↦ σ (wkVar ρ n)

def compSubst (σ τ : TSubst) : TSubst := fun n ↦ subst σ (τ n)

/-- Substitute `a` for index `0` in `t` (`t [ a ]₀`). -/
def subst0 (t a : TargetTerm) : TargetTerm := subst (sgSubst a) t

theorem substVar_lift {σ σ' : TSubst} (h : ∀ x, σ x = σ' x) :
    ∀ x, liftSubst σ x = liftSubst σ' x
  | 0 => rfl
  | x + 1 => congrArg wk1 (h x)

theorem substVar_to_subst {σ σ' : TSubst} (h : ∀ x, σ x = σ' x) :
    ∀ t : TargetTerm, subst σ t = subst σ' t
  | .var x => h x
  | .lam t => congrArg TargetTerm.lam (substVar_to_subst (substVar_lift h) t)
  | .app s t u => by simp [subst, substVar_to_subst h t, substVar_to_subst h u]
  | .prod t u => by simp [subst, substVar_to_subst h t, substVar_to_subst h u]
  | .fst t => congrArg TargetTerm.fst (substVar_to_subst h t)
  | .snd t => congrArg TargetTerm.snd (substVar_to_subst h t)
  | .prodrec rem s pz t u => by simp [subst, substVar_to_subst h t, substVar_to_subst h u]
  | .zero => rfl
  | .succ t => congrArg TargetTerm.succ (substVar_to_subst h t)
  | .natrec rem str pz rz z s n => by
      simp [subst, substVar_to_subst h z, substVar_to_subst h s, substVar_to_subst h n]
  | .star => rfl
  | .unitrec t u => by simp [subst, substVar_to_subst h t, substVar_to_subst h u]
  | .undef => rfl

theorem subst_lift_id : ∀ x, liftSubst idSubst x = idSubst x
  | 0 => rfl
  | _ + 1 => rfl

@[simp]
theorem subst_id : ∀ t : TargetTerm, subst idSubst t = t
  | .var _ => rfl
  | .lam t => by rw [subst, substVar_to_subst subst_lift_id t, subst_id t]
  | .app s t u => by rw [subst, subst_id t, subst_id u]
  | .prod t u => by rw [subst, subst_id t, subst_id u]
  | .fst t => congrArg TargetTerm.fst (subst_id t)
  | .snd t => congrArg TargetTerm.snd (subst_id t)
  | .prodrec rem s pz t u => by rw [subst, subst_id t, subst_id u]
  | .zero => rfl
  | .succ t => congrArg TargetTerm.succ (subst_id t)
  | .natrec rem str pz rz z s n => by rw [subst, subst_id z, subst_id s, subst_id n]
  | .star => rfl
  | .unitrec t u => by rw [subst, subst_id t, subst_id u]
  | .undef => rfl

theorem subst_lift_wkSubst {ρ : Wk} {σ : TSubst} (t : TargetTerm) :
    subst (wkSubst (.lift ρ) (liftSubst σ)) t = subst (liftSubst (wkSubst ρ σ)) t := by
  apply substVar_to_subst
  intro x
  cases x with
  | zero => rfl
  | succ x => exact (wk1_wk_eq_lift_wk1 ρ (σ x)).symm

theorem subst_lift_substWk {ρ : Wk} {σ : TSubst} (t : TargetTerm) :
    subst (substWk (liftSubst σ) (.lift ρ)) t = subst (liftSubst (substWk σ ρ)) t := by
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem wk_subst {ρ : Wk} {σ : TSubst} :
    ∀ t : TargetTerm, wk ρ (subst σ t) = subst (wkSubst ρ σ) t
  | .var _ => rfl
  | .lam t => by rw [subst, wk, subst, wk_subst t, subst_lift_wkSubst t]
  | .app s t u => by rw [subst, wk, subst, wk_subst t, wk_subst u]
  | .prod t u => by rw [subst, wk, subst, wk_subst t, wk_subst u]
  | .fst t => congrArg TargetTerm.fst (wk_subst t)
  | .snd t => congrArg TargetTerm.snd (wk_subst t)
  | .prodrec rem s pz t u => by rw [subst, wk, subst, wk_subst t, wk_subst u]
  | .zero => rfl
  | .succ t => congrArg TargetTerm.succ (wk_subst t)
  | .natrec rem str pz rz z s n => by
      rw [subst, wk, subst, wk_subst z, wk_subst s, wk_subst n]
  | .star => rfl
  | .unitrec t u => by rw [subst, wk, subst, wk_subst t, wk_subst u]
  | .undef => rfl

theorem subst_wk {ρ : Wk} {σ : TSubst} :
    ∀ t : TargetTerm, subst σ (wk ρ t) = subst (substWk σ ρ) t
  | .var _ => rfl
  | .lam t => by rw [wk, subst, subst, subst_wk t, subst_lift_substWk t]
  | .app s t u => by rw [wk, subst, subst, subst_wk t, subst_wk u]
  | .prod t u => by rw [wk, subst, subst, subst_wk t, subst_wk u]
  | .fst t => congrArg TargetTerm.fst (subst_wk t)
  | .snd t => congrArg TargetTerm.snd (subst_wk t)
  | .prodrec rem s pz t u => by rw [wk, subst, subst, subst_wk t, subst_wk u]
  | .zero => rfl
  | .succ t => congrArg TargetTerm.succ (subst_wk t)
  | .natrec rem str pz rz z s n => by
      rw [wk, subst, subst, subst_wk z, subst_wk s, subst_wk n]
  | .star => rfl
  | .unitrec t u => by rw [wk, subst, subst, subst_wk t, subst_wk u]
  | .undef => rfl

theorem substCompLift {σ σ' : TSubst} :
    ∀ x, compSubst (liftSubst σ) (liftSubst σ') x = liftSubst (compSubst σ σ') x
  | 0 => rfl
  | x + 1 => (subst_wk (σ' x)).trans (wk_subst (σ' x)).symm

theorem substCompEq {σ σ' : TSubst} :
    ∀ t : TargetTerm, subst σ (subst σ' t) = subst (compSubst σ σ') t
  | .var _ => rfl
  | .lam t => by
      rw [subst, subst, substCompEq t, substVar_to_subst substCompLift t]
      rfl
  | .app s t u => by rw [subst, subst, substCompEq t, substCompEq u]; rfl
  | .prod t u => by rw [subst, subst, substCompEq t, substCompEq u]; rfl
  | .fst t => congrArg TargetTerm.fst (substCompEq t)
  | .snd t => congrArg TargetTerm.snd (substCompEq t)
  | .prodrec rem s pz t u => by rw [subst, subst, substCompEq t, substCompEq u]; rfl
  | .zero => rfl
  | .succ t => congrArg TargetTerm.succ (substCompEq t)
  | .natrec rem str pz rz z s n => by
      rw [subst, subst, substCompEq z, substCompEq s, substCompEq n]; rfl
  | .star => rfl
  | .unitrec t u => by rw [subst, subst, substCompEq t, substCompEq u]; rfl
  | .undef => rfl

theorem substVarSingletonComp {u : TargetTerm} {σ : TSubst} :
    ∀ x, compSubst (sgSubst u) (liftSubst σ) x = consSubst σ u x
  | 0 => rfl
  | x + 1 => (subst_wk (σ x)).trans (subst_id (σ x))

theorem singleSubstComp (u : TargetTerm) (σ : TSubst) (t : TargetTerm) :
    subst0 (subst (liftSubst σ) t) u = subst (consSubst σ u) t :=
  (substCompEq t).trans (substVar_to_subst substVarSingletonComp t)

theorem singleSubstLift {σ : TSubst} (t u : TargetTerm) :
    subst σ (subst0 t u) = subst0 (subst (liftSubst σ) t) (subst σ u) := by
  unfold subst0
  rw [substCompEq t, substCompEq t]
  apply substVar_to_subst
  intro x
  cases x with
  | zero => rfl
  | succ x => exact (substVarSingletonComp (x + 1)).symm

theorem wk_beta {ρ : Wk} {a : TargetTerm} (t : TargetTerm) :
    wk ρ (subst0 t a) = subst0 (wk (.lift ρ) t) (wk ρ a) := by
  unfold subst0
  rw [wk_subst t, subst_wk t]
  apply substVar_to_subst
  intro x
  cases x <;> rfl

/-- Substitution replacing variable `x` with `.undef` and keeping all other variables. -/
def replaceUndef (x : Nat) : TSubst :=
  fun y ↦ if y = x then .undef else .var y

theorem liftSubst_replaceUndef (x : Nat) :
    ∀ y, liftSubst (replaceUndef x) y = replaceUndef (x + 1) y
  | 0 => rfl
  | y + 1 => by
      simp only [liftSubst, replaceUndef, Nat.add_right_cancel_iff]
      split <;> rfl

theorem not_hasX_subst_replaceUndef (t : TargetTerm) (x : Nat) :
    ¬ HasX x (subst (replaceUndef x) t) := by
  induction t generalizing x with
  | var y =>
      simp only [subst, replaceUndef]
      split
      · exact not_hasX_undef x
      · rename_i hne
        intro hx
        cases hx
        exact hne rfl
  | lam t ih =>
      simp only [subst]
      rw [substVar_to_subst (liftSubst_replaceUndef x) t]
      intro hx
      cases hx with
      | lam hx' => exact ih (x + 1) hx'
  | app s t u iht ihu =>
      intro hx
      cases hx with
      | app_left h => exact iht x h
      | app_right h => exact ihu x h
  | prod t u iht ihu =>
      intro hx
      cases hx with
      | prod_left h => exact iht x h
      | prod_right h => exact ihu x h
  | fst t ih =>
      intro hx
      cases hx with
      | fst h => exact ih x h
  | snd t ih =>
      intro hx
      cases hx with
      | snd h => exact ih x h
  | prodrec rem s pz t u iht ihu =>
      intro hx
      cases hx with
      | prodrec_left h => exact iht x h
      | prodrec_right h => exact ihu x h
  | zero => exact not_hasX_zero x
  | succ t ih =>
      intro hx
      cases hx with
      | succ h => exact ih x h
  | natrec rem str pz rz z s n ihz ihs ihn =>
      intro hx
      cases hx with
      | natrec_zero h => exact ihz x h
      | natrec_succ h => exact ihs x h
      | natrec_arg h => exact ihn x h
  | star => exact not_hasX_star x
  | unitrec t u iht ihu =>
      intro hx
      cases hx with
      | unitrec_left h => exact iht x h
      | unitrec_right h => exact ihu x h
  | undef => exact not_hasX_undef x

/-- Canonical target numeral `suck k` (`Graded.Erasure.Target.sucⁿ`). -/
def suck : Nat → TargetTerm
  | 0 => .zero
  | k + 1 => .succ (suck k)

@[simp]
theorem wk_suck (ρ : Wk) (k : Nat) : wk ρ (suck k) = suck k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [suck, wk, ih]

@[simp]
theorem subst_suck (σ : TSubst) (k : Nat) : subst σ (suck k) = suck k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [suck, subst, ih]

theorem suck_inj {k₁ k₂ : Nat} (h : suck k₁ = suck k₂) : k₁ = k₂ := by
  induction k₁ generalizing k₂ with
  | zero =>
      cases k₂ with
      | zero => rfl
      | succ k₂ => cases h
  | succ k₁ ih =>
      cases k₂ with
      | zero => cases h
      | succ k₂ =>
          injection h with h'
          exact congrArg Nat.succ (ih h')

/-- Target values (`Graded.Erasure.Target.Value`). -/
inductive Value : TargetTerm → Prop where
  | lam (t : TargetTerm) : Value (.lam t)
  | prod (t u : TargetTerm) : Value (.prod t u)
  | zero : Value .zero
  | succ (t : TargetTerm) : Value (.succ t)
  | star : Value .star
  | undef : Value .undef

/-- `Value⟨ s ⟩ t` (`Graded.Erasure.Target.Value⟨_⟩`): any term in `nonStrict` mode,
    or a `Value` in `strict` mode. -/
def ValueIfStrict : Strictness → TargetTerm → Prop
  | .nonStrict, _ => True
  | .strict, t => Value t

theorem valueIfStrict_undef (s : Strictness) : ValueIfStrict s .undef := by
  cases s with
  | nonStrict => trivial
  | strict => exact .undef

/-- Target numerals (`Graded.Erasure.Target.Numeral`). -/
inductive Numeral : TargetTerm → Prop where
  | zero : Numeral .zero
  | succ {t : TargetTerm} : Numeral t → Numeral (.succ t)

theorem numeral_suck (k : Nat) : Numeral (suck k) := by
  induction k with
  | zero => exact .zero
  | succ k ih => exact .succ ih

theorem numeral_is_value {t : TargetTerm} (h : Numeral t) : Value t := by
  cases h with
  | zero => exact .zero
  | succ _ => exact .succ _

/-- Single-step target reduction (`Graded.Erasure.Target._⊢_⇒_`). -/
inductive TargetStep : TargetTerm → TargetTerm → Prop where
  | app_subst {s : Strictness} {t t' u : TargetTerm} :
      TargetStep t t' →
      TargetStep (.app s t u) (.app s t' u)
  | app_subst_arg {t u u' : TargetTerm} :
      Value t →
      TargetStep u u' →
      TargetStep (.app .strict t u) (.app .strict t u')
  | beta {s : Strictness} {t u : TargetTerm} :
      ValueIfStrict s u →
      TargetStep (.app s (.lam t) u) (subst0 t u)
  | fst_subst {t t' : TargetTerm} :
      TargetStep t t' →
      TargetStep (.fst t) (.fst t')
  | snd_subst {t t' : TargetTerm} :
      TargetStep t t' →
      TargetStep (.snd t) (.snd t')
  | sigma_beta1 (t u : TargetTerm) :
      TargetStep (.fst (.prod t u)) t
  | sigma_beta2 (t u : TargetTerm) :
      TargetStep (.snd (.prod t u)) u
  | prodrec_subst {rem : Bool} {s : Strictness} {pz : Bool} {t t' u : TargetTerm} :
      TargetStep t t' →
      TargetStep (.prodrec rem s pz t u) (.prodrec rem s pz t' u)
  | prodrec_beta_keep (rem : Bool) (s : Strictness) (t t' u : TargetTerm) :
      TargetStep (.prodrec rem s false (.prod t t') u) (.app s (.app s u t) t')
  | prodrec_beta_erased (rem : Bool) (s : Strictness) (t' u : TargetTerm) :
      TargetStep (.prodrec rem s true t' u) (.app s (appZero rem s u) t')
  | natrec_subst {rem : Bool} {str : Strictness} {pz rz : Bool} {z s n n' : TargetTerm} :
      TargetStep n n' →
      TargetStep (.natrec rem str pz rz z s n) (.natrec rem str pz rz z s n')
  | natrec_zero (rem : Bool) (str : Strictness) (pz rz : Bool) (z s : TargetTerm) :
      TargetStep (.natrec rem str pz rz z s .zero) z
  | natrec_succ (rem : Bool) (str : Strictness) (pz rz : Bool) (z s v : TargetTerm) :
      TargetStep (.natrec rem str pz rz z s (.succ v))
        (appOrZero rem str rz (appOrZero rem str pz s v) (.natrec rem str pz rz z s v))
  | unitrec_subst {t t' u : TargetTerm} :
      TargetStep t t' →
      TargetStep (.unitrec t u) (.unitrec t' u)
  | unitrec_beta (u : TargetTerm) :
      TargetStep (.unitrec .star u) u

/-- Reflexive-transitive closure of `TargetStep` (`Graded.Erasure.Target._⊢_⇒*_`). -/
inductive TargetStar : TargetTerm → TargetTerm → Prop where
  | refl (t : TargetTerm) : TargetStar t t
  | step {t t' u : TargetTerm} :
      TargetStep t t' → TargetStar t' u → TargetStar t u

namespace TargetStar

theorem single {t u : TargetTerm} (h : TargetStep t u) : TargetStar t u :=
  .step h (.refl u)

theorem trans {t u v : TargetTerm} (h₁ : TargetStar t u) (h₂ : TargetStar u v) :
    TargetStar t v := by
  induction h₁ with
  | refl _ => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem app_subst {s : Strictness} {t t' : TargetTerm} (u : TargetTerm)
    (h : TargetStar t t') : TargetStar (.app s t u) (.app s t' u) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.app_subst hs) ih

theorem appZero_subst (remove : Bool) (str : Strictness) {t t' : TargetTerm}
    (h : TargetStar t t') : TargetStar (appZero remove str t) (appZero remove str t') := by
  unfold appZero
  split
  · exact h
  · exact app_subst .undef h

theorem appOrZero_subst (remove : Bool) (str : Strictness) (isZero : Bool)
    {t t' : TargetTerm} (u : TargetTerm) (h : TargetStar t t') :
    TargetStar (appOrZero remove str isZero t u) (appOrZero remove str isZero t' u) := by
  unfold appOrZero
  split
  · exact appZero_subst remove str h
  · exact app_subst u h

theorem app_subst_arg {t u u' : TargetTerm} (ht : Value t)
    (h : TargetStar u u') : TargetStar (.app .strict t u) (.app .strict t u') := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.app_subst_arg ht hs) ih

theorem fst_subst {t t' : TargetTerm} (h : TargetStar t t') :
    TargetStar (.fst t) (.fst t') := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.fst_subst hs) ih

theorem snd_subst {t t' : TargetTerm} (h : TargetStar t t') :
    TargetStar (.snd t) (.snd t') := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.snd_subst hs) ih

theorem prodrec_subst (rem : Bool) (s : Strictness) (pz : Bool)
    {t t' : TargetTerm} (u : TargetTerm) (h : TargetStar t t') :
    TargetStar (.prodrec rem s pz t u) (.prodrec rem s pz t' u) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.prodrec_subst hs) ih

theorem natrec_subst (rem : Bool) (str : Strictness) (pz rz : Bool) (z s : TargetTerm)
    {n n' : TargetTerm} (h : TargetStar n n') :
    TargetStar (.natrec rem str pz rz z s n) (.natrec rem str pz rz z s n') := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.natrec_subst hs) ih

theorem unitrec_subst {t t' : TargetTerm} (u : TargetTerm) (h : TargetStar t t') :
    TargetStar (.unitrec t u) (.unitrec t' u) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.unitrec_subst hs) ih

end TargetStar

/-- Values do not step in `TargetStep`. -/
theorem value_no_step {t u : TargetTerm} (hv : Value t) (hs : TargetStep t u) : False := by
  cases hv <;> cases hs

theorem value_star_eq {t u : TargetTerm} (hv : Value t) (hs : TargetStar t u) : t = u := by
  cases hs with
  | refl _ => rfl
  | step h _ => exact False.elim (value_no_step hv h)

/-- Numeral reduction (`Graded.Erasure.SucRed._⊢_⇒ˢ⟨_⟩*_`), which extends WHNF
    reduction with congruence under `succ`. -/
inductive TargetStarNum : TargetTerm → TargetTerm → Prop where
  | refl (t : TargetTerm) : TargetStarNum t t
  | whnf_step {t t' u : TargetTerm} :
      TargetStep t t' → TargetStarNum t' u → TargetStarNum t u
  | succ_cong {t t' : TargetTerm} :
      TargetStarNum t t' → TargetStarNum (.succ t) (.succ t')

namespace TargetStarNum

theorem of_targetStar {t u : TargetTerm} (h : TargetStar t u) : TargetStarNum t u := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .whnf_step hs ih

theorem trans {t u v : TargetTerm} (h₁ : TargetStarNum t u) (h₂ : TargetStarNum u v) :
    TargetStarNum t v := by
  induction h₁ generalizing v with
  | refl _ => exact h₂
  | whnf_step hs _ ih => exact .whnf_step hs (ih h₂)
  | succ_cong h ih =>
      cases h₂ with
      | refl _ => exact .succ_cong h
      | whnf_step hs _ => cases hs
      | succ_cong h' => exact .succ_cong (ih h')

end TargetStarNum

end TargetTerm

namespace GStar

variable {M : Type} {𝕄 : Modality M}

theorem trans {t u v : GTerm M}
    (h₁ : GStar 𝕄 t u) (h₂ : GStar 𝕄 u v) : GStar 𝕄 t v := by
  induction h₁ with
  | refl _ => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem app_subst {p : M} {t t' : GTerm M} (u : GTerm M)
    (h : GStar 𝕄 t t') : GStar 𝕄 (.app p t u) (.app p t' u) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.app_subst hs) ih

theorem fst_subst {p : M} {t t' : GTerm M}
    (h : GStar 𝕄 t t') : GStar 𝕄 (.fst p t) (.fst p t') := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.fst_subst hs) ih

theorem snd_subst {p : M} {t t' : GTerm M}
    (h : GStar 𝕄 t t') : GStar 𝕄 (.snd p t) (.snd p t') := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.snd_subst hs) ih

theorem unitrec_subst {p q : M} (A u : GTerm M) {t t' : GTerm M}
    (h : GStar 𝕄 t t') : GStar 𝕄 (.unitrec p q A t u) (.unitrec p q A t' u) := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.unitrec_subst hs) ih

theorem natrec_subst {p q r : M} (A z s : GTerm M) {n n' : GTerm M}
    (h : GStar 𝕄 n n') : GStar 𝕄 (.natrec p q r A z s n) (.natrec p q r A z s n') := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .step (.natrec_subst hs) ih

end GStar

/-! ### Full Numeral Reduction on Source `GTerm M` -/

/-- Full numeral reduction for source `GTerm M` (`Graded.Erasure.SucRed._⊢_⇒ˢ*_∷ℕ`). -/
inductive GStarNum {M : Type} (𝕄 : Modality M) : GTerm M → GTerm M → Prop where
  | refl (t : GTerm M) : GStarNum 𝕄 t t
  | whnf_step {t t' u : GTerm M} :
      GStep 𝕄 t t' → GStarNum 𝕄 t' u → GStarNum 𝕄 t u
  | succ_cong {t t' : GTerm M} :
      GStarNum 𝕄 t t' → GStarNum 𝕄 (.succ t) (.succ t')

namespace GStarNum

variable {M : Type} {𝕄 : Modality M}

theorem of_gstar {t u : GTerm M} (h : GStar 𝕄 t u) : GStarNum 𝕄 t u := by
  induction h with
  | refl _ => exact .refl _
  | step hs _ ih => exact .whnf_step hs ih

theorem trans {t u v : GTerm M} (h₁ : GStarNum 𝕄 t u) (h₂ : GStarNum 𝕄 u v) :
    GStarNum 𝕄 t v := by
  induction h₁ generalizing v with
  | refl _ => exact h₂
  | whnf_step hs _ ih => exact .whnf_step hs (ih h₂)
  | succ_cong h ih =>
      cases h₂ with
      | refl _ => exact .succ_cong h
      | whnf_step hs _ => cases hs
      | succ_cong h' => exact .succ_cong (ih h')

theorem suck_no_gstep (k : Nat) {u : GTerm M} (h : GStep 𝕄 (GTerm.suck k) u) :
    False := by
  cases k <;> cases h

theorem suck_starNum_eq (k : Nat) {u : GTerm M} (h : GStarNum 𝕄 (GTerm.suck k) u) :
    u = GTerm.suck k := by
  induction k generalizing u with
  | zero =>
      cases h with
      | refl _ => rfl
      | whnf_step hs _ => cases hs
  | succ k ih =>
      cases h with
      | refl _ => rfl
      | whnf_step hs _ => cases hs
      | succ_cong h' => exact congrArg GTerm.succ (ih h')

theorem gstep_deterministic {t u₁ u₂ : GTerm M}
    (h₁ : GStep 𝕄 t u₁) (h₂ : GStep 𝕄 t u₂) : u₁ = u₂ := by
  induction h₁ generalizing u₂ with
  | app_subst hs₁ ih =>
      cases h₂ with
      | app_subst hs₂ => rw [ih hs₂]
      | beta => cases hs₁
  | beta =>
      cases h₂ with
      | app_subst hs₂ => cases hs₂
      | beta => rfl
  | fst_subst hs₁ ih =>
      cases h₂ with
      | fst_subst hs₂ => rw [ih hs₂]
      | sigma_beta1 => cases hs₁
  | snd_subst hs₁ ih =>
      cases h₂ with
      | snd_subst hs₂ => rw [ih hs₂]
      | sigma_beta2 => cases hs₁
  | sigma_beta1 =>
      cases h₂ with
      | fst_subst hs₂ => cases hs₂
      | sigma_beta1 => rfl
  | sigma_beta2 =>
      cases h₂ with
      | snd_subst hs₂ => cases hs₂
      | sigma_beta2 => rfl
  | prodrec_subst hs₁ ih =>
      cases h₂ with
      | prodrec_subst hs₂ => rw [ih hs₂]
      | prodrec_beta => cases hs₁
  | prodrec_beta =>
      cases h₂ with
      | prodrec_subst hs₂ => cases hs₂
      | prodrec_beta => rfl
  | unitrec_subst hs₁ ih =>
      cases h₂ with
      | unitrec_subst hs₂ => rw [ih hs₂]
      | unitrec_beta => cases hs₁
  | unitrec_beta =>
      cases h₂ with
      | unitrec_subst hs₂ => cases hs₂
      | unitrec_beta => rfl
  | natrec_subst hs₁ ih =>
      cases h₂ with
      | natrec_subst hs₂ => rw [ih hs₂]
      | natrec_zero => cases hs₁
      | natrec_succ => cases hs₁
  | natrec_zero =>
      cases h₂ with
      | natrec_subst hs₂ => cases hs₂
      | natrec_zero => rfl
  | natrec_succ =>
      cases h₂ with
      | natrec_subst hs₂ => cases hs₂
      | natrec_succ => rfl

theorem suck_inj {k₁ k₂ : Nat} (h : GTerm.suck (M := M) k₁ = GTerm.suck k₂) :
    k₁ = k₂ := by
  induction k₁ generalizing k₂ with
  | zero =>
      cases k₂ with
      | zero => rfl
      | succ _ => cases h
  | succ k₁ ih =>
      cases k₂ with
      | zero => cases h
      | succ k₂ =>
          injection h with h'
          exact congrArg Nat.succ (ih h')

theorem suck_deterministic_aux {t u₁ u₂ : GTerm M}
    (h₁ : GStarNum 𝕄 t u₁) (h₂ : GStarNum 𝕄 t u₂) :
    ∀ {k₁ k₂ : Nat}, u₁ = GTerm.suck k₁ → u₂ = GTerm.suck k₂ → k₁ = k₂ := by
  induction h₁ generalizing u₂ with
  | refl t =>
      intro k₁ k₂ hu₁ hu₂
      subst hu₁
      have heq := suck_starNum_eq k₁ h₂
      rw [hu₂] at heq
      exact (suck_inj heq).symm
  | whnf_step hs₁ _ ih =>
      intro k₁ k₂ hu₁ hu₂
      cases h₂ with
      | refl _ =>
          subst hu₂
          exact False.elim (suck_no_gstep k₂ hs₁)
      | whnf_step hs₂ hrest₂ =>
          have heq := gstep_deterministic hs₁ hs₂
          subst heq
          exact ih hrest₂ hu₁ hu₂
      | succ_cong _ => cases hs₁
  | succ_cong hsub₁ ih =>
      intro k₁ k₂ hu₁ hu₂
      cases k₁ with
      | zero => cases hu₁
      | succ m₁ =>
          injection hu₁ with hu₁'
          cases h₂ with
          | refl _ =>
              cases k₂ with
              | zero => cases hu₂
              | succ m₂ =>
                  injection hu₂ with hu₂'
                  exact congrArg Nat.succ (ih (.refl _) hu₁' hu₂')
          | whnf_step hs₂ _ => cases hs₂
          | succ_cong hsub₂ =>
              cases k₂ with
              | zero => cases hu₂
              | succ m₂ =>
                  injection hu₂ with hu₂'
                  exact congrArg Nat.succ (ih hsub₂ hu₁' hu₂')

theorem suck_deterministic {t : GTerm M} {k₁ k₂ : Nat}
    (h₁ : GStarNum 𝕄 t (GTerm.suck k₁)) (h₂ : GStarNum 𝕄 t (GTerm.suck k₂)) :
    k₁ = k₂ :=
  suck_deterministic_aux h₁ h₂ rfl rfl

end GStarNum

/-! ## 2. Extraction Function (`erase`, M2 Section 6.1 / `Graded.Erasure.Extraction`) -/

section Extraction

variable {M : Type} (𝕄 : Modality M)

/-- Extraction of graded source terms `GTerm M` to untyped `TargetTerm`
    (`Graded.Erasure.Extraction.erase′`). -/
def erase (remove : Bool) (str : Strictness) : GTerm M → TargetTerm
  | .var x => .var x
  | .univ => .undef
  | .pi _ _ _ _ => .undef
  | .lam p t =>
      if p = 𝕄.zero then
        if remove then TargetTerm.subst0 (erase remove str t) .undef
        else .lam (erase remove str t)
      else
        .lam (erase remove str t)
  | .app p t u =>
      if p = 𝕄.zero then
        appZero remove str (erase remove str t)
      else
        .app str (erase remove str t) (erase remove str u)
  | .sigma _ _ _ _ _ => .undef
  | .prod _ p t u =>
      if p = 𝕄.zero then
        erase remove str u
      else
        .prod (erase remove str t) (erase remove str u)
  | .fst p t =>
      if p = 𝕄.zero then .undef else .fst (erase remove str t)
  | .snd p t =>
      if p = 𝕄.zero then erase remove str t else .snd (erase remove str t)
  | .prodrec r p _ _ t u =>
      if r = 𝕄.zero then
        appZero remove str (appZero remove str (erase remove str u))
      else
        .prodrec remove str (decide (p = 𝕄.zero)) (erase remove str t) (erase remove str u)
  | .nat => .undef
  | .zero => .zero
  | .succ t => .succ (erase remove str t)
  | .natrec p _ r _ z s n =>
      .natrec remove str (decide (p = 𝕄.zero)) (decide (r = 𝕄.zero))
        (erase remove str z) (erase remove str s) (erase remove str n)
  | .unit => .undef
  | .star => .star
  | .unitrec p _ _ t u =>
      if p = 𝕄.zero then
        erase remove str u
      else
        .unitrec (erase remove str t) (erase remove str u)

/-- Default extraction function (`Graded.Erasure.Extraction.erase`): removes `𝟘`-graded
    lambda/application arguments in `nonStrict` mode and keeps dummy `.undef` closures
    in `strict` mode. -/
def eraseDefault (str : Strictness) : GTerm M → TargetTerm :=
  erase 𝕄 (str == .nonStrict) str

/-- Extraction of a source substitution (`Graded.Erasure.Extraction.eraseSubst′`). -/
def eraseSubst (remove : Bool) (str : Strictness) (σ : GTerm.GSubst M) : TargetTerm.TSubst :=
  fun x ↦ erase 𝕄 remove str (σ x)

@[simp]
theorem erase_suck (remove : Bool) (str : Strictness) (k : Nat) :
    erase 𝕄 remove str (GTerm.suck k) = TargetTerm.suck k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [GTerm.suck, TargetTerm.suck, erase, ih]

theorem wk_appZero (ρ : Wk) (remove : Bool) (str : Strictness) (t : TargetTerm) :
    TargetTerm.wk ρ (appZero remove str t) = appZero remove str (TargetTerm.wk ρ t) := by
  unfold appZero
  split <;> rfl

theorem subst_appZero (σ : TargetTerm.TSubst) (remove : Bool) (str : Strictness) (t : TargetTerm) :
    TargetTerm.subst σ (appZero remove str t) = appZero remove str (TargetTerm.subst σ t) := by
  unfold appZero
  split <;> rfl

/-- Extraction commutes with weakening (`Graded.Erasure.Extraction.Properties.wk-erase-comm`). -/
theorem wk_erase_comm (remove : Bool) (str : Strictness) (ρ : Wk) (t : GTerm M) :
    TargetTerm.wk ρ (erase 𝕄 remove str t) = erase 𝕄 remove str (GTerm.wk ρ t) := by
  induction t generalizing ρ with
  | var x => rfl
  | univ => rfl
  | pi p q A B _ _ => rfl
  | lam p t ih =>
      simp only [erase, GTerm.wk]
      split
      · split
        · rw [TargetTerm.wk_beta, ih (.lift ρ)]
          rfl
        · exact congrArg TargetTerm.lam (ih (.lift ρ))
      · exact congrArg TargetTerm.lam (ih (.lift ρ))
  | app p t u iht ihu =>
      simp only [erase, GTerm.wk]
      split
      · rw [wk_appZero, iht ρ]
      · simp [TargetTerm.wk, iht ρ, ihu ρ]
  | sigma s p q A B _ _ => rfl
  | prod s p t u iht ihu =>
      simp only [erase, GTerm.wk]
      split
      · exact ihu ρ
      · simp [TargetTerm.wk, iht ρ, ihu ρ]
  | fst p t ih =>
      simp only [erase, GTerm.wk]
      split
      · rfl
      · exact congrArg TargetTerm.fst (ih ρ)
  | snd p t ih =>
      simp only [erase, GTerm.wk]
      split
      · exact ih ρ
      · exact congrArg TargetTerm.snd (ih ρ)
  | prodrec r p q A t u _ iht ihu =>
      simp only [erase, GTerm.wk]
      split
      · rw [wk_appZero, wk_appZero, ihu ρ]
      · simp [TargetTerm.wk, iht ρ, ihu ρ]
  | nat => rfl
  | zero => rfl
  | succ t ih => exact congrArg TargetTerm.succ (ih ρ)
  | natrec p q r A z s n _ ihz ihs ihn =>
      simp [erase, GTerm.wk, TargetTerm.wk, ihz ρ, ihs ρ, ihn ρ]
  | unit => rfl
  | star => rfl
  | unitrec p q A t u _ iht ihu =>
      simp only [erase, GTerm.wk]
      split
      · exact ihu ρ
      · simp [TargetTerm.wk, iht ρ, ihu ρ]

theorem liftSubst_erase_comm (remove : Bool) (str : Strictness) (σ : GTerm.GSubst M) :
    ∀ x, TargetTerm.liftSubst (eraseSubst 𝕄 remove str σ) x =
      eraseSubst 𝕄 remove str (GTerm.liftSubst σ) x
  | 0 => rfl
  | x + 1 => wk_erase_comm 𝕄 remove str (.step .id) (σ x)

/-- Extraction commutes with parallel substitution
    (`Graded.Erasure.Extraction.Properties.subst-erase-comm`). -/
theorem subst_erase_comm (remove : Bool) (str : Strictness) (σ : GTerm.GSubst M) (t : GTerm M) :
    TargetTerm.subst (eraseSubst 𝕄 remove str σ) (erase 𝕄 remove str t) =
      erase 𝕄 remove str (GTerm.subst σ t) := by
  induction t generalizing σ with
  | var x => rfl
  | univ => rfl
  | pi p q A B _ _ => rfl
  | lam p t ih =>
      simp only [erase, GTerm.subst]
      split
      · split
        · rw [TargetTerm.singleSubstLift]
          have h1 : TargetTerm.subst (TargetTerm.liftSubst (eraseSubst 𝕄 remove str σ))
              (erase 𝕄 remove str t) =
              erase 𝕄 remove str (GTerm.subst (GTerm.liftSubst σ) t) := by
            rw [TargetTerm.substVar_to_subst (liftSubst_erase_comm 𝕄 remove str σ), ih]
          rw [h1]
          rfl
        · simp only [TargetTerm.subst]
          rw [TargetTerm.substVar_to_subst (liftSubst_erase_comm 𝕄 remove str σ), ih]
      · simp only [TargetTerm.subst]
        rw [TargetTerm.substVar_to_subst (liftSubst_erase_comm 𝕄 remove str σ), ih]
  | app p t u iht ihu =>
      simp only [erase, GTerm.subst]
      split
      · rw [subst_appZero, iht σ]
      · simp [TargetTerm.subst, iht σ, ihu σ]
  | sigma s p q A B _ _ => rfl
  | prod s p t u iht ihu =>
      simp only [erase, GTerm.subst]
      split
      · exact ihu σ
      · simp [TargetTerm.subst, iht σ, ihu σ]
  | fst p t ih =>
      simp only [erase, GTerm.subst]
      split
      · rfl
      · exact congrArg TargetTerm.fst (ih σ)
  | snd p t ih =>
      simp only [erase, GTerm.subst]
      split
      · exact ih σ
      · exact congrArg TargetTerm.snd (ih σ)
  | prodrec r p q A t u _ iht ihu =>
      simp only [erase, GTerm.subst]
      split
      · rw [subst_appZero, subst_appZero, ihu σ]
      · simp [TargetTerm.subst, iht σ, ihu σ]
  | nat => rfl
  | zero => rfl
  | succ t ih => exact congrArg TargetTerm.succ (ih σ)
  | natrec p q r A z s n _ ihz ihs ihn =>
      simp [erase, GTerm.subst, TargetTerm.subst, ihz σ, ihs σ, ihn σ]
  | unit => rfl
  | star => rfl
  | unitrec p q A t u _ iht ihu =>
      simp only [erase, GTerm.subst]
      split
      · exact ihu σ
      · simp [TargetTerm.subst, iht σ, ihu σ]

theorem eraseSubst_sgSubst (remove : Bool) (str : Strictness) (u : GTerm M) :
    ∀ x, eraseSubst 𝕄 remove str (GTerm.sgSubst u) x =
      TargetTerm.sgSubst (erase 𝕄 remove str u) x
  | 0 => rfl
  | _ + 1 => rfl

/-- Extraction commutes with single-variable substitution `subst0`. -/
theorem subst0_erase_comm (remove : Bool) (str : Strictness) (t u : GTerm M) :
    TargetTerm.subst0 (erase 𝕄 remove str t) (erase 𝕄 remove str u) =
      erase 𝕄 remove str (GTerm.subst0 t u) := by
  unfold TargetTerm.subst0 GTerm.subst0
  rw [← TargetTerm.substVar_to_subst (eraseSubst_sgSubst 𝕄 remove str u) (erase 𝕄 remove str t)]
  exact subst_erase_comm 𝕄 remove str (GTerm.sgSubst u) t

end Extraction

/-! ## 3. Erasure of Unused Variables (M2 Theorem 6.4) -/

/-- A substitution `σ` agrees with the identity substitution on all variables
    with non-zero usage in `γ` (`OK` in `Graded/Erasure/Extraction/Properties/Usage.agda`). -/
def SubstSameOnNonZero {M : Type} (𝕄 : Modality M) (γ : Conₘ M) (σ : GTerm.GSubst M) : Prop :=
  ∀ x : Nat, γ x ≠ 𝕄.zero → σ x = .var x

namespace Usage

variable {M : Type} {𝕄 : Modality M}

theorem substSame_of_erased {γ : Conₘ M} {σ : GTerm.GSubst M}
    (h : ∀ x : Nat, σ x ≠ .var x → γ x = 𝕄.zero) :
    SubstSameOnNonZero 𝕄 γ σ := by
  intro x hgx
  -- Being syntactically `.var x` is decidable without `DecidableEq M`, so the contrapositive
  -- is constructive (a `by_cases` on `σ x = .var x` would need `Classical.choice` here).
  have key : ∀ t : GTerm M, (t ≠ .var x → False) → t = .var x := by
    intro t ht
    cases t with
    | var y =>
      by_cases hy : y = x
      · rw [hy]
      · exact (ht (fun e => hy (by injection e))).elim
    | _ => exact (ht (fun e => by cases e)).elim
  exact key (σ x) (fun hne => hgx (h x hne))

theorem substSame_lift {γ : Conₘ M} {q : M} {σ : GTerm.GSubst M}
    (hσ : SubstSameOnNonZero 𝕄 γ σ) :
    SubstSameOnNonZero 𝕄 (Conₘ.cons γ q) (GTerm.liftSubst σ) := by
  intro x hx
  cases x with
  | zero => rfl
  | succ x =>
      simp only [GTerm.liftSubst, hσ x hx, GTerm.wk1, GTerm.wk, wkVar]

theorem substSame_le (hw : 𝕄.HasWellBehavedZero) {γ δ : Conₘ M} {σ : GTerm.GSubst M}
    (hle : Conₘ.le 𝕄 δ γ) (hσ : SubstSameOnNonZero 𝕄 δ σ) :
    SubstSameOnNonZero 𝕄 γ σ := by
  intro x hgx
  apply hσ x
  intro hdx
  have hle_x := hle x
  rw [hdx] at hle_x
  exact hgx (hw.zero_le_eq_zero hle_x)

theorem substSame_add_left (hw : 𝕄.HasWellBehavedZero) {γ δ : Conₘ M} {σ : GTerm.GSubst M}
    (hσ : SubstSameOnNonZero 𝕄 (Conₘ.add 𝕄 γ δ) σ) :
    SubstSameOnNonZero 𝕄 γ σ := by
  intro x hgx
  apply hσ x
  intro hadd
  exact hgx (hw.add_positive_left hadd)

theorem substSame_add_right (hw : 𝕄.HasWellBehavedZero) {γ δ : Conₘ M} {σ : GTerm.GSubst M}
    (hσ : SubstSameOnNonZero 𝕄 (Conₘ.add 𝕄 γ δ) σ) :
    SubstSameOnNonZero 𝕄 δ σ := by
  intro x hdx
  apply hσ x
  intro hadd
  exact hdx (hw.add_positive_right hadd)

theorem substSame_scale (hw : 𝕄.HasWellBehavedZero) {p : M} {γ : Conₘ M} {σ : GTerm.GSubst M}
    (hp : p ≠ 𝕄.zero) (hσ : SubstSameOnNonZero 𝕄 (Conₘ.scale 𝕄 p γ) σ) :
    SubstSameOnNonZero 𝕄 γ σ := by
  intro x hgx
  apply hσ x
  intro hmul
  rcases hw.zero_product hmul with rfl | h0
  · exact hp rfl
  · exact hgx h0

theorem substSame_meet_left (hw : 𝕄.HasWellBehavedZero) {γ δ : Conₘ M} {σ : GTerm.GSubst M}
    (hσ : SubstSameOnNonZero 𝕄 (Conₘ.meet 𝕄 γ δ) σ) :
    SubstSameOnNonZero 𝕄 γ σ :=
  substSame_le hw (fun x ↦ 𝕄.meet_le_left (γ x) (δ x)) hσ

theorem substSame_meet_right (hw : 𝕄.HasWellBehavedZero) {γ δ : Conₘ M} {σ : GTerm.GSubst M}
    (hσ : SubstSameOnNonZero 𝕄 (Conₘ.meet 𝕄 γ δ) σ) :
    SubstSameOnNonZero 𝕄 δ σ :=
  substSame_le hw (fun x ↦ 𝕄.meet_le_right (γ x) (δ x)) hσ

/-- `Graded.Erasure.Extraction.Properties.Usage.erase-[]`:
    Under `HasWellBehavedZero`, substituting arbitrary terms for `𝟘`-graded variables
    does not change the extracted target term. -/
theorem erase_subst_same (hw : 𝕄.HasWellBehavedZero) (remove : Bool) (str : Strictness)
    {γ : Conₘ M} {m : Mode} {t : GTerm M}
    (ht : Usage 𝕄 γ m t) (hm : m = .oneMode)
    {σ : GTerm.GSubst M} (hσ : SubstSameOnNonZero 𝕄 γ σ) :
    erase 𝕄 remove str (GTerm.subst σ t) = erase 𝕄 remove str t := by
  induction ht generalizing σ with
  | sub _ hle ih =>
      exact ih hm (substSame_le hw hle hσ)
  | var =>
      rename_i m' x
      subst hm
      have hx1 : Conₘ.single 𝕄 x (Mode.toGrade 𝕄 .oneMode) x ≠ 𝕄.zero := by
        simp only [Conₘ.single, ↓reduceIte, Mode.toGrade]
        exact hw.nonTrivial
      simp only [GTerm.subst, hσ x hx1]
  | univ | nat | unit | star | zero | pi _ _ _ _ | sigma _ _ _ _ => rfl
  | succ _ ih =>
      exact congrArg TargetTerm.succ (ih hm hσ)
  | lam _ ih =>
      rename_i γ' m' p body _
      subst hm
      have ih_body := ih rfl (substSame_lift (q := 𝕄.mul (Mode.toGrade 𝕄 .oneMode) p) hσ)
      simp only [GTerm.subst, erase]
      split
      · split
        · rw [ih_body]
        · exact congrArg TargetTerm.lam ih_body
      · exact congrArg TargetTerm.lam ih_body
  | app _ _ iht ihu =>
      rename_i γf δu m' p f u _ _
      subst hm
      have hf := iht rfl (substSame_add_left hw hσ)
      simp only [GTerm.subst, erase]
      split
      · rw [hf]
      · rename_i hp
        have hm_p : Mode.scale 𝕄 .oneMode p = .oneMode := Mode.scale_oneMode_ne_zero 𝕄 hp
        have hu := ihu hm_p (substSame_scale hw hp (substSame_add_right hw hσ))
        rw [hf, hu]
  | @prodStrong γt δu m' p t1 t2 _ _ iht ihu =>
      subst hm
      have hu := ihu rfl (substSame_meet_right hw hσ)
      simp only [GTerm.subst, erase]
      split
      · exact hu
      · rename_i hp
        have hm_p : Mode.scale 𝕄 .oneMode p = .oneMode := Mode.scale_oneMode_ne_zero 𝕄 hp
        have ht1 := iht hm_p (substSame_scale hw hp (substSame_meet_left hw hσ))
        rw [ht1, hu]
  | @prodWeak γt δu m' p t1 t2 _ _ iht ihu =>
      subst hm
      have hu := ihu rfl (substSame_add_right hw hσ)
      simp only [GTerm.subst, erase]
      split
      · exact hu
      · rename_i hp
        have hm_p : Mode.scale 𝕄 .oneMode p = .oneMode := Mode.scale_oneMode_ne_zero 𝕄 hp
        have ht1 := iht hm_p (substSame_scale hw hp (substSame_add_left hw hσ))
        rw [ht1, hu]
  | fst _ _ ih =>
      simp only [GTerm.subst, erase]
      split
      · rfl
      · exact congrArg TargetTerm.fst (ih hm hσ)
  | snd _ ih =>
      simp only [GTerm.subst, erase]
      split
      · exact ih hm hσ
      · exact congrArg TargetTerm.snd (ih hm hσ)
  | @prodrec γt δu ηA m' r p q A t1 u1 _ _ _ iht ihu _ =>
      subst hm
      have hu := ihu rfl (substSame_add_right hw hσ)
      simp only [GTerm.subst, erase]
      split
      · rw [hu]
      · rename_i hr
        have hm_r : Mode.scale 𝕄 .oneMode r = .oneMode := Mode.scale_oneMode_ne_zero 𝕄 hr
        have ht1 := iht hm_r (substSame_scale hw hr (substSame_add_left hw hσ))
        rw [ht1, hu]
  | @unitrec γt δu ηA m' p q A t1 u1 _ _ _ iht ihu _ =>
      subst hm
      have hu := ihu rfl (substSame_add_right hw hσ)
      simp only [GTerm.subst, erase]
      split
      · exact hu
      · rename_i hp
        have hm_p : Mode.scale 𝕄 .oneMode p = .oneMode := Mode.scale_oneMode_ne_zero 𝕄 hp
        have ht1 := iht hm_p (substSame_scale hw hp (substSame_add_left hw hσ))
        rw [ht1, hu]
  | @natrec_fix γz δs ηn θA χ m' x p q r A z s n _ _ _ _ hx1 _ hχ1 hχ2 ihz ihs ihn _ =>
      subst hm
      have hσχ := substSame_add_right hw hσ
      have hz := ihz rfl (substSame_le hw hχ1 hσχ)
      have hs := ihs rfl (substSame_add_left hw (substSame_le hw hχ2 hσχ))
      have hx_ne : x ≠ 𝕄.zero := by
        intro hx0
        have hx1' := hx1
        rw [hx0] at hx1'
        exact hw.nonTrivial (hw.zero_le_eq_zero hx1')
      have hn := ihn rfl (substSame_scale hw hx_ne (substSame_add_left hw hσ))
      simp only [GTerm.subst, erase, hz, hs, hn]

/-- `Graded.Erasure.Extraction.Properties.Usage.erase-[]` in the exact Agda form:
    if `∀ x, σ x ≠ var x → γ x = 𝟘` and `γ ▸[𝟙ᵐ] t`, then
    `erase (t[σ]) = erase t`. -/
theorem erase_subst_erased (hw : 𝕄.HasWellBehavedZero) (remove : Bool) (str : Strictness)
    {γ : Conₘ M} {t : GTerm M} {σ : GTerm.GSubst M}
    (hok : ∀ x : Nat, σ x ≠ .var x → γ x = 𝕄.zero)
    (ht : Usage 𝕄 γ .oneMode t) :
    erase 𝕄 remove str (GTerm.subst σ t) = erase 𝕄 remove str t :=
  erase_subst_same hw remove str ht rfl (substSame_of_erased hok)

theorem inv_var {γ : Conₘ M} {m : Mode} {x : Nat}
    (h : Usage 𝕄 γ m (.var x)) :
    Conₘ.le 𝕄 γ (Conₘ.single 𝕄 x (Mode.toGrade 𝕄 m)) := by
  generalize ht : (GTerm.var x : GTerm M) = t at h
  induction h with
  | sub _ hle ih => exact Conₘ.le_trans 𝕄 hle (ih ht)
  | var =>
      injection ht with hx
      subst hx
      exact Conₘ.le_refl 𝕄 _
  | _ => nomatch ht

/-- Substituting any term `u` for an erased variable `0` (`γ ∙ 𝟘 ▸[𝟙ᵐ] t`) produces
    the same extracted term as substituting `.undef`. -/
theorem erase_subst0_erased (hw : 𝕄.HasWellBehavedZero) (remove : Bool) (str : Strictness)
    {γ : Conₘ M} {t : GTerm M} (u : GTerm M)
    (ht : Usage 𝕄 (Conₘ.cons γ 𝕄.zero) .oneMode t) :
    erase 𝕄 remove str (GTerm.subst0 t u) =
      TargetTerm.subst0 (erase 𝕄 remove str t) .undef := by
  let σ_kill : GTerm.GSubst M := fun y ↦ if y = 0 then .univ else .var y
  have hsame : SubstSameOnNonZero 𝕄 (Conₘ.cons γ 𝕄.zero) σ_kill := by
    intro y hgy
    simp only [σ_kill]
    split
    · rename_i hy0
      subst hy0
      exact False.elim (hgy rfl)
    · rfl
  have heq1 : erase 𝕄 remove str (GTerm.subst σ_kill t) = erase 𝕄 remove str t :=
    erase_subst_same hw remove str ht rfl hsame
  have h_erase_kill : ∀ y, eraseSubst 𝕄 remove str σ_kill y = TargetTerm.replaceUndef 0 y := by
    intro y
    simp only [eraseSubst, σ_kill, TargetTerm.replaceUndef]
    split <;> rfl
  have heq2 : TargetTerm.subst (TargetTerm.replaceUndef 0) (erase 𝕄 remove str t) =
      erase 𝕄 remove str t := by
    rw [← TargetTerm.substVar_to_subst h_erase_kill (erase 𝕄 remove str t)]
    exact (subst_erase_comm 𝕄 remove str σ_kill t).trans heq1
  rw [← subst0_erase_comm 𝕄 remove str t u]
  unfold TargetTerm.subst0
  conv => lhs; rw [← heq2]
  rw [TargetTerm.substCompEq]
  apply TargetTerm.substVar_to_subst
  intro y
  cases y <;> rfl

/-- **M2 Theorem 6.4 (`erased-hasX`, `Graded.Erasure.Extraction.Properties.Usage`)**:
    Under `HasWellBehavedZero`, if `γ ▸[𝟙ᵐ] t` and `γ x = 𝟘`, then variable `x`
    does not occur syntactically (`¬ HasX x`) in the extracted target term
    `erase 𝕄 remove str t`. -/
theorem erased_not_hasX (hw : 𝕄.HasWellBehavedZero) (remove : Bool) (str : Strictness)
    {γ : Conₘ M} {t : GTerm M} {x : Nat}
    (hx : γ x = 𝕄.zero) (ht : Usage 𝕄 γ .oneMode t) :
    ¬ TargetTerm.HasX x (erase 𝕄 remove str t) := by
  let σ_kill : GTerm.GSubst M := fun y ↦ if y = x then .univ else .var y
  have hsame : SubstSameOnNonZero 𝕄 γ σ_kill := by
    intro y hgy
    simp only [σ_kill]
    split
    · rename_i hyx
      subst hyx
      exact False.elim (hgy hx)
    · rfl
  have heq1 : erase 𝕄 remove str (GTerm.subst σ_kill t) = erase 𝕄 remove str t :=
    erase_subst_same hw remove str ht rfl hsame
  have h_erase_kill : ∀ y, eraseSubst 𝕄 remove str σ_kill y = TargetTerm.replaceUndef x y := by
    intro y
    simp only [eraseSubst, σ_kill, TargetTerm.replaceUndef]
    split <;> rfl
  have heq2 : TargetTerm.subst (TargetTerm.replaceUndef x) (erase 𝕄 remove str t) =
      erase 𝕄 remove str (GTerm.subst σ_kill t) := by
    rw [← TargetTerm.substVar_to_subst h_erase_kill (erase 𝕄 remove str t)]
    exact subst_erase_comm 𝕄 remove str σ_kill t
  rw [← heq1, ← heq2]
  exact TargetTerm.not_hasX_subst_replaceUndef (erase 𝕄 remove str t) x

/-- Corollary of M2 Theorem 6.4 for the default non-strict extraction `eraseDefault 𝕄 .nonStrict`. -/
theorem erased_not_hasX_default (hw : 𝕄.HasWellBehavedZero)
    {γ : Conₘ M} {t : GTerm M} {x : Nat}
    (hx : γ x = 𝕄.zero) (ht : Usage 𝕄 γ .oneMode t) :
    ¬ TargetTerm.HasX x (eraseDefault 𝕄 .nonStrict t) :=
  erased_not_hasX hw true .nonStrict hx ht

end Usage

/-! ## 4. Operational Simulation and the Erasure Logical Relation (M2 Section 6.2) -/

/-! ### 4.1 Syntactic Restriction Against Erased Matches and Direct Operational Simulation -/

/-- `NoErasedMatches 𝕄 t` holds when `t` does not eliminate `Unit` or weak `Σ`-products
    at grade `𝟘`. As shown in M2 Section 6.3, open neutral terms inside `unitrec 𝟘` or
    `prodrec 𝟘` can erase to values even when the source term is stuck. -/
def NoErasedMatches {M : Type} (𝕄 : Modality M) : GTerm M → Prop
  | .var _ | .univ | .nat | .unit | .zero | .star => True
  | .pi _ _ A B | .sigma _ _ _ A B => NoErasedMatches 𝕄 A ∧ NoErasedMatches 𝕄 B
  | .lam _ t | .fst _ t | .snd _ t | .succ t => NoErasedMatches 𝕄 t
  | .app _ t u | .prod _ _ t u => NoErasedMatches 𝕄 t ∧ NoErasedMatches 𝕄 u
  | .prodrec r _ _ _ t u => r ≠ 𝕄.zero ∧ NoErasedMatches 𝕄 t ∧ NoErasedMatches 𝕄 u
  | .unitrec p _ _ t u => p ≠ 𝕄.zero ∧ NoErasedMatches 𝕄 t ∧ NoErasedMatches 𝕄 u
  | .natrec _ _ _ _ z s n =>
      NoErasedMatches 𝕄 z ∧ NoErasedMatches 𝕄 s ∧ NoErasedMatches 𝕄 n

/-- Single-step operational simulation of `GStep 𝕄 t t'` by `TargetStar` in `nonStrict`
    mode under `HasWellBehavedZero` and `NoErasedMatches`. -/
theorem erase_gstep_sim {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    (remove : Bool) {γ : Conₘ M} {t t' : GTerm M}
    (hs : GStep 𝕄 t t') (hu : Usage 𝕄 γ .oneMode t) (hnem : NoErasedMatches 𝕄 t) :
    TargetTerm.TargetStar (erase 𝕄 remove .nonStrict t) (erase 𝕄 remove .nonStrict t') := by
  induction hs generalizing γ with
  | @app_subst p f f' a hstep ih =>
      rcases Usage.inv_app hu with ⟨γf, δa, hf, _, _⟩
      rcases hnem with ⟨hnem_f, _⟩
      have ih_f := ih hf hnem_f
      simp only [erase]
      split
      · exact TargetTerm.TargetStar.appZero_subst remove .nonStrict ih_f
      · exact TargetTerm.TargetStar.app_subst _ ih_f
  | @beta p body arg =>
      rcases Usage.inv_app hu with ⟨γf, δa, hlam, _, _⟩
      have hbody := Usage.inv_lam hlam
      simp only [Mode.toGrade, 𝕄.one_mul] at hbody
      simp only [erase]
      by_cases hp : p = 𝕄.zero
      · subst hp
        simp only [↓reduceIte]
        have her := Usage.erase_subst0_erased hw remove .nonStrict arg hbody
        rw [her]
        cases remove with
        | true => exact .refl _
        | false =>
            exact TargetTerm.TargetStar.single
              (TargetTerm.TargetStep.beta (TargetTerm.valueIfStrict_undef .nonStrict))
      · simp only [hp, ↓reduceIte]
        rw [← subst0_erase_comm 𝕄 remove .nonStrict body arg]
        exact TargetTerm.TargetStar.single (TargetTerm.TargetStep.beta trivial)
  | @fst_subst p a a' hstep ih =>
      rcases Usage.inv_fst hu with ⟨ha, hle⟩
      simp only [Mode.toGrade, 𝕄.one_mul] at hle
      have hp : p ≠ 𝕄.zero := by
        intro hp0
        rw [hp0] at hle
        exact hw.zero_not_le_one hle
      simp only [erase, hp, ↓reduceIte]
      exact TargetTerm.TargetStar.fst_subst (ih ha hnem)
  | @snd_subst p a a' hstep ih =>
      have ha := Usage.inv_snd hu
      simp only [erase]
      split
      · exact ih ha hnem
      · exact TargetTerm.TargetStar.snd_subst (ih ha hnem)
  | @sigma_beta1 p a b =>
      rcases Usage.inv_fst hu with ⟨_, hle⟩
      simp only [Mode.toGrade, 𝕄.one_mul] at hle
      have hp : p ≠ 𝕄.zero := by
        intro hp0
        rw [hp0] at hle
        exact hw.zero_not_le_one hle
      simp only [erase, hp, ↓reduceIte]
      exact TargetTerm.TargetStar.single (TargetTerm.TargetStep.sigma_beta1 _ _)
  | @sigma_beta2 p a b =>
      simp only [erase]
      by_cases hp : p = 𝕄.zero
      · simp only [hp, ↓reduceIte]
        exact .refl _
      · simp only [hp, ↓reduceIte]
        exact TargetTerm.TargetStar.single (TargetTerm.TargetStep.sigma_beta2 _ _)
  | @prodrec_subst r p q A a a' b hstep ih =>
      rcases Usage.inv_prodrec hu with ⟨γt, δu, _, ha, _, _, _⟩
      rcases hnem with ⟨hr, hnem_a, _⟩
      have hm_r : Mode.scale 𝕄 .oneMode r = .oneMode := Mode.scale_oneMode_ne_zero 𝕄 hr
      rw [hm_r] at ha
      simp only [erase, hr, ↓reduceIte]
      exact TargetTerm.TargetStar.prodrec_subst remove .nonStrict (decide (p = 𝕄.zero)) _
        (ih ha hnem_a)
  | @prodrec_beta r p q A t1 t2 b =>
      rcases hnem with ⟨hr, _, _⟩
      simp only [erase, hr, ↓reduceIte]
      by_cases hp : p = 𝕄.zero
      · subst hp
        have hr0 : 𝕄.mul r 𝕄.zero = 𝕄.zero := 𝕄.mul_zero r
        simp only [↓reduceIte, decide_true, hr0]
        exact TargetTerm.TargetStar.single
          (TargetTerm.TargetStep.prodrec_beta_erased remove .nonStrict _ _)
      · have hrp : 𝕄.mul r p ≠ 𝕄.zero := by
          intro hmul
          rcases hw.zero_product hmul with h1 | h2
          · exact hr h1
          · exact hp h2
        simp only [hp, hrp, ↓reduceIte, decide_false]
        exact TargetTerm.TargetStar.single
          (TargetTerm.TargetStep.prodrec_beta_keep remove .nonStrict _ _ _)
  | @unitrec_subst p q A a a' b hstep ih =>
      rcases Usage.inv_unitrec hu with ⟨γt, δu, _, ha, _, _, _⟩
      rcases hnem with ⟨hp, hnem_a, _⟩
      have hm_p : Mode.scale 𝕄 .oneMode p = .oneMode := Mode.scale_oneMode_ne_zero 𝕄 hp
      rw [hm_p] at ha
      simp only [erase, hp, ↓reduceIte]
      exact TargetTerm.TargetStar.unitrec_subst _ (ih ha hnem_a)
  | @unitrec_beta p q A b =>
      simp only [erase]
      by_cases hp : p = 𝕄.zero
      · simp only [hp, ↓reduceIte]
        exact .refl _
      · simp only [hp, ↓reduceIte]
        exact TargetTerm.TargetStar.single (TargetTerm.TargetStep.unitrec_beta _)
  | @natrec_subst p q r A z s n n' hstep ih =>
      rcases Usage.inv_natrec hu with ⟨_, _, ηn, _, _, _, _, _, hn, _, _, _, _, _, _⟩
      rcases hnem with ⟨_, _, hnem_n⟩
      simp only [erase]
      exact TargetTerm.TargetStar.natrec_subst remove .nonStrict
        (decide (p = 𝕄.zero)) (decide (r = 𝕄.zero)) _ _ (ih hn hnem_n)
  | @natrec_zero p q r A z s =>
      simp only [erase]
      exact TargetTerm.TargetStar.single
        (TargetTerm.TargetStep.natrec_zero remove .nonStrict _ _ _ _)
  | @natrec_succ p q r A z s n =>
      have hstep := TargetTerm.TargetStep.natrec_succ remove .nonStrict
        (decide (p = 𝕄.zero)) (decide (r = 𝕄.zero))
        (erase 𝕄 remove .nonStrict z) (erase 𝕄 remove .nonStrict s) (erase 𝕄 remove .nonStrict n)
      have heq : appOrZero remove .nonStrict (decide (r = 𝕄.zero))
          (appOrZero remove .nonStrict (decide (p = 𝕄.zero))
            (erase 𝕄 remove .nonStrict s) (erase 𝕄 remove .nonStrict n))
          (.natrec remove .nonStrict (decide (p = 𝕄.zero)) (decide (r = 𝕄.zero))
            (erase 𝕄 remove .nonStrict z) (erase 𝕄 remove .nonStrict s)
            (erase 𝕄 remove .nonStrict n)) =
          erase 𝕄 remove .nonStrict (.app r (.app p s n) (.natrec p q r A z s n)) := by
        simp only [erase, appOrZero]
        by_cases hr : r = 𝕄.zero <;> by_cases hp : p = 𝕄.zero <;> simp [hr, hp]
      rw [heq] at hstep
      exact TargetTerm.TargetStar.single hstep

/-! ### 4.2 The Logical Relation for Erasure (`Graded.Erasure.LogicalRelation`) -/

/-- Erasure logical relation for natural numbers (`_®_∷ℕ` in
    `Graded/Erasure/LogicalRelation.agda`). -/
inductive ErasedRelNat {M : Type} (𝕄 : Modality M) : GTerm M → TargetTerm → Prop where
  | zeroᵣ {t : GTerm M} {v : TargetTerm} :
      GStar 𝕄 t .zero →
      TargetTerm.TargetStar v .zero →
      ErasedRelNat 𝕄 t v
  | sucᵣ {t t' : GTerm M} {v v' : TargetTerm} :
      GStar 𝕄 t (.succ t') →
      TargetTerm.TargetStar v (.succ v') →
      ErasedRelNat 𝕄 t' v' →
      ErasedRelNat 𝕄 t v

theorem erasedRelNat_backwards_closed {M : Type} {𝕄 : Modality M}
    {t t' : GTerm M} {v v' : TargetTerm}
    (ht : GStar 𝕄 t t') (hv : TargetTerm.TargetStar v v')
    (hrel : ErasedRelNat 𝕄 t' v') :
    ErasedRelNat 𝕄 t v := by
  cases hrel with
  | zeroᵣ ht0 hv0 =>
      exact .zeroᵣ (GStar.trans ht ht0) (TargetTerm.TargetStar.trans hv hv0)
  | sucᵣ hts hvs hsub =>
      exact .sucᵣ (GStar.trans ht hts) (TargetTerm.TargetStar.trans hv hvs) hsub

/-- Every pair `(t, v)` in `ErasedRelNat 𝕄 t v` reduces in full numeral reduction
    (`GStarNum` and `TargetStarNum`) to the exact same canonical numeral `suck k`
    (`soundness-ℕ″` in `Graded/Erasure/Consequences/Soundness.agda`). -/
theorem soundness_nat_of_erasedRelNat {M : Type} {𝕄 : Modality M}
    {t : GTerm M} {v : TargetTerm} (h : ErasedRelNat 𝕄 t v) :
    ∃ k : Nat, GStarNum 𝕄 t (GTerm.suck k) ∧
      TargetTerm.TargetStarNum v (TargetTerm.suck k) := by
  induction h with
  | zeroᵣ ht0 hv0 =>
      exact ⟨0, GStarNum.of_gstar ht0, TargetTerm.TargetStarNum.of_targetStar hv0⟩
  | sucᵣ hts hvs _ ih =>
      rcases ih with ⟨k, htk, hvk⟩
      refine ⟨k + 1, ?_, ?_⟩
      · exact GStarNum.trans (GStarNum.of_gstar hts) (.succ_cong htk)
      · exact TargetTerm.TargetStarNum.trans
          (TargetTerm.TargetStarNum.of_targetStar hvs) (.succ_cong hvk)

/-- Inductive semantic type witnesses (`ts » Δ ⊨ A` in `Graded/Erasure/LogicalRelation.agda`)
    supporting structural recursion for the erasure logical relation `ErasedRel`. -/
inductive SemType {M : Type} (𝕄 : Modality M) : GTerm M → Type where
  | univ {A : GTerm M} : GStar 𝕄 A .univ → SemType 𝕄 A
  | nat {A : GTerm M} : GStar 𝕄 A .nat → SemType 𝕄 A
  | unit {A : GTerm M} : GStar 𝕄 A .unit → SemType 𝕄 A
  | pi {A : GTerm M} (p q : M) (F G : GTerm M) :
      GStar 𝕄 A (.pi p q F G) →
      SemType 𝕄 F →
      SemType 𝕄 G →
      SemType 𝕄 A
  | sigma {A : GTerm M} (s : Strength) (p q : M) (F G : GTerm M) :
      GStar 𝕄 A (.sigma s p q F G) →
      SemType 𝕄 F →
      SemType 𝕄 G →
      SemType 𝕄 A

/-- Type-indexed logical relation for erasure (`_®_∷_/_` in
    `Graded/Erasure/LogicalRelation.agda`), defined by structural recursion on the
    semantic type witness `SemType 𝕄 A`. -/
def ErasedRel {M : Type} (𝕄 : Modality M) (remove : Bool) (str : Strictness) :
    {A : GTerm M} → SemType 𝕄 A → GTerm M → TargetTerm → Prop
  | _, .univ _, _, v =>
      str = .strict → TargetTerm.TargetStar v .undef
  | _, .nat _, t, v =>
      ErasedRelNat 𝕄 t v
  | _, .unit _, t, v =>
      GStar 𝕄 t .star ∧ TargetTerm.TargetStar v .star
  | _, .pi p _ _ _ _ hF hG, t, v =>
      ∀ a : GTerm M,
        if p = 𝕄.zero then
          ErasedRel 𝕄 remove str hG (.app p t a) (appZero remove str v)
        else
          ∀ w : TargetTerm, ErasedRel 𝕄 remove str hF a w →
            ErasedRel 𝕄 remove str hG (.app p t a) (.app str v w)
  | _, .sigma s p _ _ _ _ hF hG, t, v =>
      ∃ t₁ t₂ : GTerm M, GStar 𝕄 t (.prod s p t₁ t₂) ∧
        ∃ v₂ : TargetTerm, ErasedRel 𝕄 remove str hG t₂ v₂ ∧
          if p = 𝕄.zero then
            TargetTerm.TargetStar v v₂
          else
            ∃ v₁ : TargetTerm, TargetTerm.TargetStar v (.prod v₁ v₂) ∧
              ErasedRel 𝕄 remove str hF t₁ v₁

/-- Grade-indexed erasure logical relation (`t ® v ∷ A ◂ p` in
    `Graded/Erasure/LogicalRelation/Hidden.agda`). -/
def ErasedRelGraded {M : Type} (𝕄 : Modality M) (remove : Bool) (str : Strictness)
    (p : M) {A : GTerm M} (hA : SemType 𝕄 A) (t : GTerm M) (v : TargetTerm) : Prop :=
  p ≠ 𝕄.zero → ErasedRel 𝕄 remove str hA t v

theorem erasedRel_to_graded {M : Type} {𝕄 : Modality M} {remove : Bool} {str : Strictness}
    {p : M} {A : GTerm M} {hA : SemType 𝕄 A} {t : GTerm M} {v : TargetTerm}
    (h : ErasedRel 𝕄 remove str hA t v) :
    ErasedRelGraded 𝕄 remove str p hA t v :=
  fun _ ↦ h

theorem erasedRelGraded_zero {M : Type} {𝕄 : Modality M} {remove : Bool} {str : Strictness}
    {p : M} {A : GTerm M} {hA : SemType 𝕄 A} {t : GTerm M} {v : TargetTerm}
    (hp : p = 𝕄.zero) :
    ErasedRelGraded 𝕄 remove str p hA t v :=
  fun hne ↦ False.elim (hne hp)

theorem erasedRelGraded_nonZero {M : Type} {𝕄 : Modality M} {remove : Bool} {str : Strictness}
    {p : M} {A : GTerm M} {hA : SemType 𝕄 A} {t : GTerm M} {v : TargetTerm}
    (hp : p ≠ 𝕄.zero) (h : ErasedRelGraded 𝕄 remove str p hA t v) :
    ErasedRel 𝕄 remove str hA t v :=
  h hp

/-- Grade subsumption (`subsumption-®∷◂` in `Graded/Erasure/LogicalRelation/Hidden.agda`). -/
theorem subsumption_erasedRelGraded {M : Type} {𝕄 : Modality M} {remove : Bool} {str : Strictness}
    {p q : M} {A : GTerm M} {hA : SemType 𝕄 A} {t : GTerm M} {v : TargetTerm}
    (himp : p = 𝕄.zero → q = 𝕄.zero)
    (h : ErasedRelGraded 𝕄 remove str p hA t v) :
    ErasedRelGraded 𝕄 remove str q hA t v := by
  intro hq
  apply h
  intro hp
  exact hq (himp hp)

/-- Backwards closure of `ErasedRel` under source `GStar` and target `TargetStar`
    (`redSubstTerm*` / `®∷-⇐*` in `Graded/Erasure/LogicalRelation/Reduction.agda`). -/
theorem erasedRel_backwards_closed {M : Type} {𝕄 : Modality M}
    {remove : Bool} {str : Strictness}
    {A : GTerm M} (hA : SemType 𝕄 A) {t t' : GTerm M} {v v' : TargetTerm}
    (ht : GStar 𝕄 t t') (hv : TargetTerm.TargetStar v v')
    (hrel : ErasedRel 𝕄 remove str hA t' v') :
    ErasedRel 𝕄 remove str hA t v := by
  induction hA generalizing t t' v v' with
  | univ _ =>
      intro hs
      exact TargetTerm.TargetStar.trans hv (hrel hs)
  | nat _ =>
      exact erasedRelNat_backwards_closed ht hv hrel
  | unit _ =>
      exact ⟨GStar.trans ht hrel.1, TargetTerm.TargetStar.trans hv hrel.2⟩
  | pi p q F G _ _ _ _ ihG =>
      intro a
      have hsub := hrel a
      by_cases hp : p = 𝕄.zero
      · rw [if_pos hp] at hsub ⊢
        exact ihG (GStar.app_subst a ht) (TargetTerm.TargetStar.appZero_subst remove str hv) hsub
      · rw [if_neg hp] at hsub ⊢
        intro w hw
        exact ihG (GStar.app_subst a ht) (TargetTerm.TargetStar.app_subst w hv) (hsub w hw)
  | sigma s p q F G _ _ _ _ _ =>
      rcases hrel with ⟨t₁, t₂, ht12, v₂, hv2, hrest⟩
      refine ⟨t₁, t₂, GStar.trans ht ht12, v₂, hv2, ?_⟩
      by_cases hp : p = 𝕄.zero
      · simp only [hp, ↓reduceIte] at hrest ⊢
        exact TargetTerm.TargetStar.trans hv hrest
      · simp only [hp, ↓reduceIte] at hrest ⊢
        rcases hrest with ⟨v₁, hv12, hrel1⟩
        exact ⟨v₁, TargetTerm.TargetStar.trans hv hv12, hrel1⟩

theorem erasedRelGraded_backwards_closed {M : Type} {𝕄 : Modality M}
    {remove : Bool} {str : Strictness} {p : M}
    {A : GTerm M} (hA : SemType 𝕄 A) {t t' : GTerm M} {v v' : TargetTerm}
    (ht : GStar 𝕄 t t') (hv : TargetTerm.TargetStar v v')
    (hrel : ErasedRelGraded 𝕄 remove str p hA t' v') :
    ErasedRelGraded 𝕄 remove str p hA t v :=
  fun hp ↦ erasedRel_backwards_closed hA ht hv (hrel hp)

/-- Validity of `natrec` in the erasure logical relation (`natrecʳ′` in
    `Graded/Erasure/LogicalRelation/Fundamental/Nat.agda`), proved by induction
    on `ErasedRelNat 𝕄 n v_n`. -/
theorem erasedRel_natrec {M : Type} {𝕄 : Modality M}
    {remove : Bool} {str : Strictness}
    {A : GTerm M} (hA : SemType 𝕄 A)
    (p q r : M) (Motive z s n : GTerm M) (v_z v_s v_n : TargetTerm)
    (hz : ErasedRel 𝕄 remove str hA z v_z)
    (hs : ∀ (m : GTerm M) (v_m : TargetTerm),
      ErasedRelNat 𝕄 m v_m →
      ∀ (acc : GTerm M) (v_acc : TargetTerm),
        ErasedRel 𝕄 remove str hA acc v_acc →
        ErasedRel 𝕄 remove str hA
          (.app r (.app p s m) acc)
          (appOrZero remove str (decide (r = 𝕄.zero))
            (appOrZero remove str (decide (p = 𝕄.zero)) v_s v_m) v_acc))
    (hn : ErasedRelNat 𝕄 n v_n) :
    ErasedRel 𝕄 remove str hA
      (.natrec p q r Motive z s n)
      (.natrec remove str (decide (p = 𝕄.zero)) (decide (r = 𝕄.zero)) v_z v_s v_n) := by
  induction hn with
  | @zeroᵣ n₀ vn₀ hn0 hvn0 =>
      have h_src : GStar 𝕄 (.natrec p q r Motive z s n₀) z :=
        GStar.trans (GStar.natrec_subst Motive z s hn0) (.step .natrec_zero (.refl z))
      have h_tgt : TargetTerm.TargetStar
          (.natrec remove str (decide (p = 𝕄.zero)) (decide (r = 𝕄.zero)) v_z v_s vn₀) v_z :=
        TargetTerm.TargetStar.trans
          (TargetTerm.TargetStar.natrec_subst remove str
            (decide (p = 𝕄.zero)) (decide (r = 𝕄.zero)) v_z v_s hvn0)
          (TargetTerm.TargetStar.single
            (TargetTerm.TargetStep.natrec_zero remove str _ _ v_z v_s))
      exact erasedRel_backwards_closed hA h_src h_tgt hz
  | @sucᵣ n₀ m vn₀ vm hns hvns hm ih =>
      have h_step := hs m vm hm (.natrec p q r Motive z s m)
        (.natrec remove str (decide (p = 𝕄.zero)) (decide (r = 𝕄.zero)) v_z v_s vm) ih
      have h_src : GStar 𝕄 (.natrec p q r Motive z s n₀)
          (.app r (.app p s m) (.natrec p q r Motive z s m)) :=
        GStar.trans (GStar.natrec_subst Motive z s hns) (.step .natrec_succ (.refl _))
      have h_tgt : TargetTerm.TargetStar
          (.natrec remove str (decide (p = 𝕄.zero)) (decide (r = 𝕄.zero)) v_z v_s vn₀)
          (appOrZero remove str (decide (r = 𝕄.zero))
            (appOrZero remove str (decide (p = 𝕄.zero)) v_s vm)
            (.natrec remove str (decide (p = 𝕄.zero)) (decide (r = 𝕄.zero)) v_z v_s vm)) :=
        TargetTerm.TargetStar.trans
          (TargetTerm.TargetStar.natrec_subst remove str
            (decide (p = 𝕄.zero)) (decide (r = 𝕄.zero)) v_z v_s hvns)
          (TargetTerm.TargetStar.single
            (TargetTerm.TargetStep.natrec_succ remove str _ _ v_z v_s vm))
      exact erasedRel_backwards_closed hA h_src h_tgt h_step

/-! ### 4.3 `GTerm` Substitution Lemmas, Validity, and M2 Theorems 6.8 & 6.9 -/

namespace GTerm

variable {M : Type}

def wkSubst (ρ : Wk) (σ : GSubst M) : GSubst M := fun n ↦ wk ρ (σ n)

def substWk (σ : GSubst M) (ρ : Wk) : GSubst M := fun n ↦ σ (wkVar ρ n)

def compSubst (σ τ : GSubst M) : GSubst M := fun n ↦ subst σ (τ n)

theorem wkVar_to_wk {ρ ρ' : Wk} (h : ∀ x, wkVar ρ x = wkVar ρ' x) :
    ∀ t : GTerm M, wk ρ t = wk ρ' t
  | .univ => rfl
  | .pi p q A B => by simp [wk, wkVar_to_wk h A, wkVar_to_wk (wkVar_lift h) B]
  | .sigma s p q A B => by simp [wk, wkVar_to_wk h A, wkVar_to_wk (wkVar_lift h) B]
  | .nat => rfl
  | .unit => rfl
  | .var x => congrArg GTerm.var (h x)
  | .lam p t => congrArg (GTerm.lam p) (wkVar_to_wk (wkVar_lift h) t)
  | .app p t u => by simp [wk, wkVar_to_wk h t, wkVar_to_wk h u]
  | .prod s p t u => by simp [wk, wkVar_to_wk h t, wkVar_to_wk h u]
  | .fst p t => congrArg (GTerm.fst p) (wkVar_to_wk h t)
  | .snd p t => congrArg (GTerm.snd p) (wkVar_to_wk h t)
  | .prodrec r p q A t u => by
      simp [wk, wkVar_to_wk (wkVar_lift h) A, wkVar_to_wk h t, wkVar_to_wk h u]
  | .zero => rfl
  | .succ t => congrArg GTerm.succ (wkVar_to_wk h t)
  | .natrec p q r A z s n => by
      simp [wk, wkVar_to_wk (wkVar_lift h) A,
        wkVar_to_wk h z, wkVar_to_wk h s, wkVar_to_wk h n]
  | .star => rfl
  | .unitrec p q A t u => by
      simp [wk, wkVar_to_wk (wkVar_lift h) A, wkVar_to_wk h t, wkVar_to_wk h u]

@[simp]
theorem wk_id : ∀ t : GTerm M, wk .id t = t
  | .univ => rfl
  | .pi p q A B => by rw [wk, wk_id A, wkVar_to_wk wkVar_lift_id B, wk_id B]
  | .sigma s p q A B => by rw [wk, wk_id A, wkVar_to_wk wkVar_lift_id B, wk_id B]
  | .nat => rfl
  | .unit => rfl
  | .var _ => rfl
  | .lam p t => by rw [wk, wkVar_to_wk wkVar_lift_id t, wk_id t]
  | .app p t u => by rw [wk, wk_id t, wk_id u]
  | .prod s p t u => by rw [wk, wk_id t, wk_id u]
  | .fst p t => congrArg (GTerm.fst p) (wk_id t)
  | .snd p t => congrArg (GTerm.snd p) (wk_id t)
  | .prodrec r p q A t u => by
      rw [wk, wkVar_to_wk wkVar_lift_id A, wk_id A, wk_id t, wk_id u]
  | .zero => rfl
  | .succ t => congrArg GTerm.succ (wk_id t)
  | .natrec p q r A z s n => by
      rw [wk, wkVar_to_wk wkVar_lift_id A, wk_id A, wk_id z, wk_id s, wk_id n]
  | .star => rfl
  | .unitrec p q A t u => by
      rw [wk, wkVar_to_wk wkVar_lift_id A, wk_id A, wk_id t, wk_id u]

theorem wk_comp : ∀ (ρ ρ' : Wk) (t : GTerm M),
    wk ρ (wk ρ' t) = wk (compWk ρ ρ') t
  | _, _, .univ => rfl
  | ρ, ρ', .pi p q A B => by
      simp [wk, wk_comp ρ ρ' A, wk_comp (.lift ρ) (.lift ρ') B, compWk]
  | ρ, ρ', .sigma s p q A B => by
      simp [wk, wk_comp ρ ρ' A, wk_comp (.lift ρ) (.lift ρ') B, compWk]
  | _, _, .nat => rfl
  | _, _, .unit => rfl
  | ρ, ρ', .var x => congrArg GTerm.var (wkVar_comp ρ ρ' x)
  | ρ, ρ', .lam p t => by simp [wk, wk_comp (.lift ρ) (.lift ρ') t, compWk]
  | ρ, ρ', .app p t u => by simp [wk, wk_comp ρ ρ' t, wk_comp ρ ρ' u]
  | ρ, ρ', .prod s p t u => by simp [wk, wk_comp ρ ρ' t, wk_comp ρ ρ' u]
  | ρ, ρ', .fst p t => congrArg (GTerm.fst p) (wk_comp ρ ρ' t)
  | ρ, ρ', .snd p t => congrArg (GTerm.snd p) (wk_comp ρ ρ' t)
  | ρ, ρ', .prodrec r p q A t u => by
      simp [wk, wk_comp (.lift ρ) (.lift ρ') A, wk_comp ρ ρ' t, wk_comp ρ ρ' u, compWk]
  | _, _, .zero => rfl
  | ρ, ρ', .succ t => congrArg GTerm.succ (wk_comp ρ ρ' t)
  | ρ, ρ', .natrec p q r A z s n => by
      simp [wk, wk_comp (.lift ρ) (.lift ρ') A,
        wk_comp ρ ρ' z, wk_comp ρ ρ' s, wk_comp ρ ρ' n, compWk]
  | _, _, .star => rfl
  | ρ, ρ', .unitrec p q A t u => by
      simp [wk, wk_comp (.lift ρ) (.lift ρ') A, wk_comp ρ ρ' t, wk_comp ρ ρ' u, compWk]

theorem wk1_wk_eq_lift_wk1 (ρ : Wk) (t : GTerm M) :
    wk1 (wk ρ t) = wk (.lift ρ) (wk1 t) := by
  unfold wk1
  rw [wk_comp (.step .id) ρ t, wk_comp (.lift ρ) (.step .id) t, lift_step_comp ρ]

theorem substVar_lift {σ σ' : GSubst M} (h : ∀ x, σ x = σ' x) :
    ∀ x, liftSubst σ x = liftSubst σ' x
  | 0 => rfl
  | x + 1 => congrArg wk1 (h x)

theorem substVar_to_subst {σ σ' : GSubst M} (h : ∀ x, σ x = σ' x) :
    ∀ t : GTerm M, subst σ t = subst σ' t
  | .univ => rfl
  | .pi p q A B => by
      simp [subst, substVar_to_subst h A, substVar_to_subst (substVar_lift h) B]
  | .sigma s p q A B => by
      simp [subst, substVar_to_subst h A, substVar_to_subst (substVar_lift h) B]
  | .nat => rfl
  | .unit => rfl
  | .var x => h x
  | .lam p t => congrArg (GTerm.lam p) (substVar_to_subst (substVar_lift h) t)
  | .app p t u => by simp [subst, substVar_to_subst h t, substVar_to_subst h u]
  | .prod s p t u => by simp [subst, substVar_to_subst h t, substVar_to_subst h u]
  | .fst p t => congrArg (GTerm.fst p) (substVar_to_subst h t)
  | .snd p t => congrArg (GTerm.snd p) (substVar_to_subst h t)
  | .prodrec r p q A t u => by
      simp [subst, substVar_to_subst (substVar_lift h) A,
        substVar_to_subst h t, substVar_to_subst h u]
  | .zero => rfl
  | .succ t => congrArg GTerm.succ (substVar_to_subst h t)
  | .natrec p q r A z s n => by
      simp [subst, substVar_to_subst (substVar_lift h) A,
        substVar_to_subst h z, substVar_to_subst h s, substVar_to_subst h n]
  | .star => rfl
  | .unitrec p q A t u => by
      simp [subst, substVar_to_subst (substVar_lift h) A,
        substVar_to_subst h t, substVar_to_subst h u]

theorem subst_lift_id : ∀ x, liftSubst (idSubst (M := M)) x = idSubst x
  | 0 => rfl
  | _ + 1 => rfl

@[simp]
theorem subst_id : ∀ t : GTerm M, subst idSubst t = t
  | .univ => rfl
  | .pi p q A B => by rw [subst, subst_id A, substVar_to_subst subst_lift_id B, subst_id B]
  | .sigma s p q A B => by rw [subst, subst_id A, substVar_to_subst subst_lift_id B, subst_id B]
  | .nat => rfl
  | .unit => rfl
  | .var _ => rfl
  | .lam p t => by rw [subst, substVar_to_subst subst_lift_id t, subst_id t]
  | .app p t u => by rw [subst, subst_id t, subst_id u]
  | .prod s p t u => by rw [subst, subst_id t, subst_id u]
  | .fst p t => congrArg (GTerm.fst p) (subst_id t)
  | .snd p t => congrArg (GTerm.snd p) (subst_id t)
  | .prodrec r p q A t u => by
      rw [subst, substVar_to_subst subst_lift_id A, subst_id A, subst_id t, subst_id u]
  | .zero => rfl
  | .succ t => congrArg GTerm.succ (subst_id t)
  | .natrec p q r A z s n => by
      rw [subst, substVar_to_subst subst_lift_id A, subst_id A, subst_id z, subst_id s, subst_id n]
  | .star => rfl
  | .unitrec p q A t u => by
      rw [subst, substVar_to_subst subst_lift_id A, subst_id A, subst_id t, subst_id u]

theorem subst_lift_wkSubst {ρ : Wk} {σ : GSubst M} (t : GTerm M) :
    subst (wkSubst (.lift ρ) (liftSubst σ)) t = subst (liftSubst (wkSubst ρ σ)) t := by
  apply substVar_to_subst
  intro x
  cases x with
  | zero => rfl
  | succ x => exact (wk1_wk_eq_lift_wk1 ρ (σ x)).symm

theorem subst_lift_substWk {ρ : Wk} {σ : GSubst M} (t : GTerm M) :
    subst (substWk (liftSubst σ) (.lift ρ)) t = subst (liftSubst (substWk σ ρ)) t := by
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem wk_subst {ρ : Wk} {σ : GSubst M} :
    ∀ t : GTerm M, wk ρ (subst σ t) = subst (wkSubst ρ σ) t
  | .univ => rfl
  | .pi p q A B => by rw [subst, wk, subst, wk_subst A, wk_subst B, subst_lift_wkSubst B]
  | .sigma s p q A B => by rw [subst, wk, subst, wk_subst A, wk_subst B, subst_lift_wkSubst B]
  | .nat => rfl
  | .unit => rfl
  | .var _ => rfl
  | .lam p t => by rw [subst, wk, subst, wk_subst t, subst_lift_wkSubst t]
  | .app p t u => by rw [subst, wk, subst, wk_subst t, wk_subst u]
  | .prod s p t u => by rw [subst, wk, subst, wk_subst t, wk_subst u]
  | .fst p t => congrArg (GTerm.fst p) (wk_subst t)
  | .snd p t => congrArg (GTerm.snd p) (wk_subst t)
  | .prodrec r p q A t u => by
      rw [subst, wk, subst, wk_subst A, subst_lift_wkSubst A, wk_subst t, wk_subst u]
  | .zero => rfl
  | .succ t => congrArg GTerm.succ (wk_subst t)
  | .natrec p q r A z s n => by
      rw [subst, wk, subst, wk_subst A, subst_lift_wkSubst A,
        wk_subst z, wk_subst s, wk_subst n]
  | .star => rfl
  | .unitrec p q A t u => by
      rw [subst, wk, subst, wk_subst A, subst_lift_wkSubst A, wk_subst t, wk_subst u]

theorem subst_wk {ρ : Wk} {σ : GSubst M} :
    ∀ t : GTerm M, subst σ (wk ρ t) = subst (substWk σ ρ) t
  | .univ => rfl
  | .pi p q A B => by rw [wk, subst, subst, subst_wk A, subst_wk B, subst_lift_substWk B]
  | .sigma s p q A B => by rw [wk, subst, subst, subst_wk A, subst_wk B, subst_lift_substWk B]
  | .nat => rfl
  | .unit => rfl
  | .var _ => rfl
  | .lam p t => by rw [wk, subst, subst, subst_wk t, subst_lift_substWk t]
  | .app p t u => by rw [wk, subst, subst, subst_wk t, subst_wk u]
  | .prod s p t u => by rw [wk, subst, subst, subst_wk t, subst_wk u]
  | .fst p t => congrArg (GTerm.fst p) (subst_wk t)
  | .snd p t => congrArg (GTerm.snd p) (subst_wk t)
  | .prodrec r p q A t u => by
      rw [wk, subst, subst, subst_wk A, subst_lift_substWk A, subst_wk t, subst_wk u]
  | .zero => rfl
  | .succ t => congrArg GTerm.succ (subst_wk t)
  | .natrec p q r A z s n => by
      rw [wk, subst, subst, subst_wk A, subst_lift_substWk A,
        subst_wk z, subst_wk s, subst_wk n]
  | .star => rfl
  | .unitrec p q A t u => by
      rw [wk, subst, subst, subst_wk A, subst_lift_substWk A, subst_wk t, subst_wk u]

theorem substCompLift {σ σ' : GSubst M} :
    ∀ x, compSubst (liftSubst σ) (liftSubst σ') x = liftSubst (compSubst σ σ') x
  | 0 => rfl
  | x + 1 => (subst_wk (σ' x)).trans (wk_subst (σ' x)).symm

theorem substCompEq {σ σ' : GSubst M} :
    ∀ t : GTerm M, subst σ (subst σ' t) = subst (compSubst σ σ') t
  | .univ => rfl
  | .pi p q A B => by
      rw [subst, subst, substCompEq A, substCompEq B, substVar_to_subst substCompLift B]; rfl
  | .sigma s p q A B => by
      rw [subst, subst, substCompEq A, substCompEq B, substVar_to_subst substCompLift B]; rfl
  | .nat => rfl
  | .unit => rfl
  | .var _ => rfl
  | .lam p t => by
      rw [subst, subst, substCompEq t, substVar_to_subst substCompLift t]; rfl
  | .app p t u => by rw [subst, subst, substCompEq t, substCompEq u]; rfl
  | .prod s p t u => by rw [subst, subst, substCompEq t, substCompEq u]; rfl
  | .fst p t => congrArg (GTerm.fst p) (substCompEq t)
  | .snd p t => congrArg (GTerm.snd p) (substCompEq t)
  | .prodrec r p q A t u => by
      rw [subst, subst, substCompEq A, substVar_to_subst substCompLift A,
        substCompEq t, substCompEq u]; rfl
  | .zero => rfl
  | .succ t => congrArg GTerm.succ (substCompEq t)
  | .natrec p q r A z s n => by
      rw [subst, subst, substCompEq A, substVar_to_subst substCompLift A,
        substCompEq z, substCompEq s, substCompEq n]; rfl
  | .star => rfl
  | .unitrec p q A t u => by
      rw [subst, subst, substCompEq A, substVar_to_subst substCompLift A,
        substCompEq t, substCompEq u]; rfl

theorem substVarSingletonComp {u : GTerm M} {σ : GSubst M} :
    ∀ x, compSubst (sgSubst u) (liftSubst σ) x = consSubst σ u x
  | 0 => rfl
  | x + 1 => (subst_wk (σ x)).trans (subst_id (σ x))

theorem singleSubstComp (u : GTerm M) (σ : GSubst M) (t : GTerm M) :
    subst0 (subst (liftSubst σ) t) u = subst (consSubst σ u) t :=
  (substCompEq t).trans (substVar_to_subst substVarSingletonComp t)

end GTerm

/-- Semantic typing context: a list of `(type, SemType witness)` entries. -/
abbrev SemCon {M : Type} (𝕄 : Modality M) := List (Σ A : GTerm M, SemType 𝕄 A)

/-- Context lookup for `SemCon 𝕄`. -/
inductive SemLookup {M : Type} {𝕄 : Modality M} :
    Nat → SemCon 𝕄 → (A : GTerm M) → SemType 𝕄 A → Type where
  | here {A : GTerm M} {hA : SemType 𝕄 A} {Γ : SemCon 𝕄} :
      SemLookup 0 (⟨A, hA⟩ :: Γ) A hA
  | there {x : Nat} {A B : GTerm M} {hA : SemType 𝕄 A} {hB : SemType 𝕄 B} {Γ : SemCon 𝕄} :
      SemLookup x Γ A hA →
      SemLookup (x + 1) (⟨B, hB⟩ :: Γ) A hA

/-- Related source and target substitutions (`σ ® σ′ ∷[ m ] Γ ◂ γ` in
    `Graded/Erasure/LogicalRelation/Substitutions.agda`). -/
def SubstRel {M : Type} (𝕄 : Modality M) (remove : Bool) (str : Strictness)
    (Γ : SemCon 𝕄) (γ : Conₘ M) (m : Mode)
    (σ : GTerm.GSubst M) (σ' : TargetTerm.TSubst) : Prop :=
  ∀ {x : Nat} {A : GTerm M} {hA : SemType 𝕄 A},
    Nonempty (SemLookup x Γ A hA) →
    ErasedRelGraded 𝕄 remove str (𝕄.mul (Mode.toGrade 𝕄 m) (γ x)) hA (σ x) (σ' x)

/-- Semantic validity of an open graded term (`γ ▸ Γ ⊩ʳ t ∷[ m ] A` in
    `Graded/Erasure/LogicalRelation/Hidden.agda`). -/
def ValidErased {M : Type} (𝕄 : Modality M) (remove : Bool) (str : Strictness)
    (Γ : SemCon 𝕄) (γ : Conₘ M) (m : Mode)
    (t A : GTerm M) (hA : SemType 𝕄 A) : Prop :=
  ∀ (σ : GTerm.GSubst M) (σ' : TargetTerm.TSubst),
    SubstRel 𝕄 remove str Γ γ m σ σ' →
    ErasedRelGraded 𝕄 remove str (Mode.toGrade 𝕄 m) hA
      (GTerm.subst σ t) (TargetTerm.subst σ' (erase 𝕄 remove str t))

/-- Every pair of substitutions `(σ, σ')` is related under the zero usage context `𝟘ᶜ`
    (`®∷[]◂𝟘ᶜ` in `Graded/Erasure/LogicalRelation/Hidden.agda`). -/
theorem substRel_zero {M : Type} (𝕄 : Modality M) (remove : Bool) (str : Strictness)
    (Γ : SemCon 𝕄) (m : Mode) (σ : GTerm.GSubst M) (σ' : TargetTerm.TSubst) :
    SubstRel 𝕄 remove str Γ (Conₘ.zero 𝕄) m σ σ' := by
  intro x A hA _
  simp only [Conₘ.zero, 𝕄.mul_zero]
  exact erasedRelGraded_zero rfl

theorem substRel_cons {M : Type} {𝕄 : Modality M} {remove : Bool} {str : Strictness}
    {Γ : SemCon 𝕄} {γ : Conₘ M} {m : Mode} {p : M}
    {A : GTerm M} {hA : SemType 𝕄 A}
    {σ : GTerm.GSubst M} {σ' : TargetTerm.TSubst} {a : GTerm M} {v : TargetTerm}
    (ha : ErasedRelGraded 𝕄 remove str (𝕄.mul (Mode.toGrade 𝕄 m) p) hA a v)
    (hσ : SubstRel 𝕄 remove str Γ γ m σ σ') :
    SubstRel 𝕄 remove str (⟨A, hA⟩ :: Γ) (Conₘ.cons γ p) m
      (GTerm.consSubst σ a) (TargetTerm.consSubst σ' v) := by
  intro x B hB ⟨hl⟩
  cases hl with
  | here => exact ha
  | there hl' => exact hσ ⟨hl'⟩

/-- Subsumption for `SubstRel` (`subsumption-®∷[∣]◂`). -/
theorem subsumption_substRel {M : Type} {𝕄 : Modality M}
    {remove : Bool} {str : Strictness} {Γ : SemCon 𝕄} {γ δ : Conₘ M} {m : Mode}
    {σ : GTerm.GSubst M} {σ' : TargetTerm.TSubst}
    (himp : ∀ x, γ x = 𝕄.zero → δ x = 𝕄.zero)
    (hσ : SubstRel 𝕄 remove str Γ γ m σ σ') :
    SubstRel 𝕄 remove str Γ δ m σ σ' := by
  intro x A hA hl
  apply subsumption_erasedRelGraded _ (hσ hl)
  cases m with
  | zeroMode =>
      intro _
      simp [Mode.toGrade, 𝕄.zero_mul]
  | oneMode =>
      simp only [Mode.toGrade, 𝕄.one_mul]
      exact himp x

/-- Subsumption for `ValidErased` (`subsumption-▸⊩ʳ∷[]`). -/
theorem subsumption_validErased {M : Type} {𝕄 : Modality M}
    {remove : Bool} {str : Strictness} {Γ : SemCon 𝕄} {γ δ : Conₘ M} {m : Mode}
    {t A : GTerm M} {hA : SemType 𝕄 A}
    (himp : ∀ x, δ x = 𝕄.zero → γ x = 𝕄.zero)
    (hv : ValidErased 𝕄 remove str Γ γ m t A hA) :
    ValidErased 𝕄 remove str Γ δ m t A hA :=
  fun σ σ' hσ ↦ hv σ σ' (subsumption_substRel himp hσ)

/-- Inequality-based subsumption for `ValidErased` (`subsumption-▸⊩ʳ∷[]-≤`). -/
theorem subsumption_validErased_le {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    {remove : Bool} {str : Strictness} {Γ : SemCon 𝕄} {γ δ : Conₘ M} {m : Mode}
    {t A : GTerm M} {hA : SemType 𝕄 A}
    (hle : Conₘ.le 𝕄 δ γ)
    (hv : ValidErased 𝕄 remove str Γ γ m t A hA) :
    ValidErased 𝕄 remove str Γ δ m t A hA := by
  apply subsumption_validErased _ hv
  intro x hdx
  have hle_x := hle x
  rw [hdx] at hle_x
  exact hw.zero_le_eq_zero hle_x

theorem validErased_zeroMode {M : Type} {𝕄 : Modality M}
    {remove : Bool} {str : Strictness} {Γ : SemCon 𝕄} {γ : Conₘ M}
    {t A : GTerm M} {hA : SemType 𝕄 A} :
    ValidErased 𝕄 remove str Γ γ .zeroMode t A hA :=
  fun _ _ _ ↦ erasedRelGraded_zero rfl

/-- Fundamental lemma for variables (`fundamentalVar` in
    `Graded/Erasure/LogicalRelation/Fundamental.agda`). -/
theorem valid_var {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    {remove : Bool} {str : Strictness} {Γ : SemCon 𝕄} {γ : Conₘ M} {m : Mode}
    {x : Nat} {A : GTerm M} {hA : SemType 𝕄 A}
    (hl : SemLookup x Γ A hA) (hux : Usage 𝕄 γ m (.var x)) :
    ValidErased 𝕄 remove str Γ γ m (.var x) A hA := by
  intro σ σ' hσ
  have hrel := hσ ⟨hl⟩
  have hle := Usage.inv_var hux
  apply subsumption_erasedRelGraded _ hrel
  cases m with
  | zeroMode => intro _; rfl
  | oneMode =>
      simp only [Mode.toGrade, 𝕄.one_mul]
      intro hgx
      have hle_x := hle x
      simp only [Conₘ.single, ↓reduceIte, Mode.toGrade] at hle_x
      rw [hgx] at hle_x
      exact False.elim (hw.zero_not_le_one hle_x)

/-- Validity of `zero` (`zeroʳ` in `Graded/Erasure/LogicalRelation/Fundamental/Nat.agda`). -/
theorem valid_zero {M : Type} {𝕄 : Modality M}
    {remove : Bool} {str : Strictness} {Γ : SemCon 𝕄} {γ : Conₘ M} {m : Mode} :
    ValidErased 𝕄 remove str Γ γ m .zero .nat (.nat (.refl .nat)) := by
  intro σ σ' _
  exact erasedRel_to_graded (.zeroᵣ (.refl .zero) (.refl .zero))

/-- Validity of `succ` (`sucʳ` in `Graded/Erasure/LogicalRelation/Fundamental/Nat.agda`). -/
theorem valid_succ {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    {remove : Bool} {str : Strictness} {Γ : SemCon 𝕄} {γ : Conₘ M} {m : Mode}
    {t : GTerm M}
    (ht : ValidErased 𝕄 remove str Γ γ m t .nat (.nat (.refl .nat))) :
    ValidErased 𝕄 remove str Γ γ m (.succ t) .nat (.nat (.refl .nat)) := by
  cases m with
  | zeroMode => exact validErased_zeroMode
  | oneMode =>
      intro σ σ' hσ
      have ih := erasedRelGraded_nonZero hw.nonTrivial (ht σ σ' hσ)
      exact erasedRel_to_graded (.sucᵣ (.refl _) (.refl _) ih)

/-- Validity of `star` (`starʳ` in `Graded/Erasure/LogicalRelation/Fundamental/Unit.agda`). -/
theorem valid_star {M : Type} {𝕄 : Modality M}
    {remove : Bool} {str : Strictness} {Γ : SemCon 𝕄} {γ : Conₘ M} {m : Mode} :
    ValidErased 𝕄 remove str Γ γ m .star .unit (.unit (.refl .unit)) := by
  intro σ σ' _
  exact erasedRel_to_graded ⟨.refl .star, .refl .star⟩

/-- Validity of `unitrec` (`unitrecʳ` in `Graded/Erasure/LogicalRelation/Fundamental/Unit.agda`). -/
theorem valid_unitrec {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    {remove : Bool} {str : Strictness} {Γ : SemCon 𝕄} {γ δ : Conₘ M} {m : Mode}
    {p q : M} {Motive t u C : GTerm M} {hC : SemType 𝕄 C}
    (hp_ne : p ≠ 𝕄.zero)
    (ht : ValidErased 𝕄 remove str Γ γ (Mode.scale 𝕄 m p) t .unit (.unit (.refl .unit)))
    (hu : ValidErased 𝕄 remove str Γ δ m u C hC) :
    ValidErased 𝕄 remove str Γ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 p γ) δ) m
      (.unitrec p q Motive t u) C hC := by
  cases m with
  | zeroMode => exact validErased_zeroMode
  | oneMode =>
      intro σ σ' hσ
      have hσ_u : SubstRel 𝕄 remove str Γ δ .oneMode σ σ' :=
        subsumption_substRel (fun x h0 ↦ hw.add_positive_right h0) hσ
      have hσ_t : SubstRel 𝕄 remove str Γ γ .oneMode σ σ' :=
        subsumption_substRel (fun x h0 ↦ by
          rcases hw.zero_product (hw.add_positive_left h0) with h1 | h2
          · exact False.elim (hp_ne h1)
          · exact h2) hσ
      have hm_p : Mode.scale 𝕄 .oneMode p = .oneMode := Mode.scale_oneMode_ne_zero 𝕄 hp_ne
      rw [hm_p] at ht
      rcases erasedRelGraded_nonZero hw.nonTrivial (ht σ σ' hσ_t) with ⟨ht_src, ht_tgt⟩
      have ih_u := erasedRelGraded_nonZero hw.nonTrivial (hu σ σ' hσ_u)
      apply erasedRel_to_graded
      simp only [GTerm.subst, erase, hp_ne, ↓reduceIte, TargetTerm.subst]
      have h_src : GStar 𝕄 (.unitrec p q (GTerm.subst (GTerm.liftSubst σ) Motive)
          (GTerm.subst σ t) (GTerm.subst σ u)) (GTerm.subst σ u) :=
        GStar.trans
          (GStar.unitrec_subst (GTerm.subst (GTerm.liftSubst σ) Motive) (GTerm.subst σ u) ht_src)
          (.step .unitrec_beta (.refl _))
      have h_tgt : TargetTerm.TargetStar
          (.unitrec (TargetTerm.subst σ' (erase 𝕄 remove str t))
            (TargetTerm.subst σ' (erase 𝕄 remove str u)))
          (TargetTerm.subst σ' (erase 𝕄 remove str u)) :=
        TargetTerm.TargetStar.trans
          (TargetTerm.TargetStar.unitrec_subst _ ht_tgt)
          (TargetTerm.TargetStar.single (TargetTerm.TargetStep.unitrec_beta _))
      exact erasedRel_backwards_closed hC h_src h_tgt ih_u

/-- Validity of `lam` (`lamʳ` in `Graded/Erasure/LogicalRelation/Fundamental/Pi-Sigma.agda`). -/
theorem valid_lam {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    {remove : Bool} {Γ : SemCon 𝕄} {γ : Conₘ M} {m : Mode}
    {p q : M} {F G t : GTerm M} {hF : SemType 𝕄 F} {hG : SemType 𝕄 G}
    (ht : ValidErased 𝕄 remove .nonStrict (⟨F, hF⟩ :: Γ)
      (Conₘ.cons γ (𝕄.mul (Mode.toGrade 𝕄 m) p)) m t G hG) :
    ValidErased 𝕄 remove .nonStrict Γ γ m (.lam p t) (.pi p q F G)
      (.pi p q F G (.refl _) hF hG) := by
  cases m with
  | zeroMode => exact validErased_zeroMode
  | oneMode =>
      intro σ σ' hσ
      apply erasedRel_to_graded
      intro a
      by_cases hp : p = 𝕄.zero
      · subst hp
        simp only [↓reduceIte]
        have ha0 : ErasedRelGraded 𝕄 remove .nonStrict
            (𝕄.mul (Mode.toGrade 𝕄 .oneMode) (𝕄.mul (Mode.toGrade 𝕄 .oneMode) 𝕄.zero))
            hF a .undef := by
          simp only [Mode.toGrade, 𝕄.mul_zero]
          exact erasedRelGraded_zero rfl
        have ih_t := erasedRelGraded_nonZero hw.nonTrivial (ht _ _ (substRel_cons ha0 hσ))
        rw [← GTerm.singleSubstComp a σ t,
            ← TargetTerm.singleSubstComp .undef σ' (erase 𝕄 remove .nonStrict t)] at ih_t
        have h_src : GStar 𝕄 (.app 𝕄.zero (GTerm.subst σ (.lam 𝕄.zero t)) a)
            (GTerm.subst0 (GTerm.subst (GTerm.liftSubst σ) t) a) :=
          .step .beta (.refl _)
        have h_tgt : TargetTerm.TargetStar
            (appZero remove .nonStrict (TargetTerm.subst σ' (erase 𝕄 remove .nonStrict (.lam 𝕄.zero t))))
            (TargetTerm.subst0 (TargetTerm.subst (TargetTerm.liftSubst σ') (erase 𝕄 remove .nonStrict t)) .undef) := by
          simp only [erase, ↓reduceIte]
          cases remove with
          | true =>
              simp only [appZero, ↓reduceIte, TargetTerm.singleSubstLift]
              exact .refl _
          | false =>
              simp only [appZero]
              exact TargetTerm.TargetStar.single (TargetTerm.TargetStep.beta trivial)
        exact erasedRel_backwards_closed hG h_src h_tgt ih_t
      · simp only [hp, ↓reduceIte]
        intro w hw_rel
        have ha : ErasedRelGraded 𝕄 remove .nonStrict
            (𝕄.mul (Mode.toGrade 𝕄 .oneMode) (𝕄.mul (Mode.toGrade 𝕄 .oneMode) p))
            hF a w :=
          erasedRel_to_graded hw_rel
        have ih_t := erasedRelGraded_nonZero hw.nonTrivial (ht _ _ (substRel_cons ha hσ))
        rw [← GTerm.singleSubstComp a σ t,
            ← TargetTerm.singleSubstComp w σ' (erase 𝕄 remove .nonStrict t)] at ih_t
        have h_src : GStar 𝕄 (.app p (GTerm.subst σ (.lam p t)) a)
            (GTerm.subst0 (GTerm.subst (GTerm.liftSubst σ) t) a) :=
          .step .beta (.refl _)
        have h_tgt : TargetTerm.TargetStar
            (.app .nonStrict (TargetTerm.subst σ' (erase 𝕄 remove .nonStrict (.lam p t))) w)
            (TargetTerm.subst0 (TargetTerm.subst (TargetTerm.liftSubst σ') (erase 𝕄 remove .nonStrict t)) w) := by
          simp only [erase, hp, ↓reduceIte, TargetTerm.subst]
          exact TargetTerm.TargetStar.single (TargetTerm.TargetStep.beta trivial)
        exact erasedRel_backwards_closed hG h_src h_tgt ih_t

/-- Validity of `app` (`∘ʳ` in `Graded/Erasure/LogicalRelation/Fundamental/Pi-Sigma.agda`). -/
theorem valid_app {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    {remove : Bool} {str : Strictness} {Γ : SemCon 𝕄} {γ δ : Conₘ M} {m : Mode}
    {p q : M} {F G t u : GTerm M} {hF : SemType 𝕄 F} {hG : SemType 𝕄 G}
    (ht : ValidErased 𝕄 remove str Γ γ m t (.pi p q F G) (.pi p q F G (.refl _) hF hG))
    (hu : ValidErased 𝕄 remove str Γ δ (Mode.scale 𝕄 m p) u F hF) :
    ValidErased 𝕄 remove str Γ (Conₘ.add 𝕄 γ (Conₘ.scale 𝕄 p δ)) m (.app p t u) G hG := by
  cases m with
  | zeroMode => exact validErased_zeroMode
  | oneMode =>
      intro σ σ' hσ
      have hσ_t : SubstRel 𝕄 remove str Γ γ .oneMode σ σ' :=
        subsumption_substRel (fun x h0 ↦ hw.add_positive_left h0) hσ
      have ih_t := erasedRelGraded_nonZero hw.nonTrivial (ht σ σ' hσ_t)
      have h_app := ih_t (GTerm.subst σ u)
      apply erasedRel_to_graded
      by_cases hp : p = 𝕄.zero
      · subst hp
        simp only [↓reduceIte, GTerm.subst, erase, subst_appZero] at h_app ⊢
        exact h_app
      · simp only [hp, ↓reduceIte, GTerm.subst, erase, TargetTerm.subst] at h_app ⊢
        have hσ_u : SubstRel 𝕄 remove str Γ δ .oneMode σ σ' :=
          subsumption_substRel (fun x h0 ↦ by
            rcases hw.zero_product (hw.add_positive_right h0) with h1 | h2
            · exact False.elim (hp h1)
            · exact h2) hσ
        have hm_p : Mode.scale 𝕄 .oneMode p = .oneMode := Mode.scale_oneMode_ne_zero 𝕄 hp
        rw [hm_p] at hu
        have ih_u := erasedRelGraded_nonZero hw.nonTrivial (hu σ σ' hσ_u)
        exact h_app _ ih_u

/-- Validity of strong pair `prod .strong` (`prodˢʳ` in
    `Graded/Erasure/LogicalRelation/Fundamental/Pi-Sigma.agda`). -/
theorem valid_prodStrong {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    {remove : Bool} {str : Strictness} {Γ : SemCon 𝕄} {γ δ : Conₘ M} {m : Mode}
    {p q : M} {F G t u : GTerm M} {hF : SemType 𝕄 F} {hG : SemType 𝕄 G}
    (ht : ValidErased 𝕄 remove str Γ γ (Mode.scale 𝕄 m p) t F hF)
    (hu : ValidErased 𝕄 remove str Γ δ m u G hG) :
    ValidErased 𝕄 remove str Γ (Conₘ.meet 𝕄 (Conₘ.scale 𝕄 p γ) δ) m
      (.prod .strong p t u) (.sigma .strong p q F G)
      (.sigma .strong p q F G (.refl _) hF hG) := by
  cases m with
  | zeroMode => exact validErased_zeroMode
  | oneMode =>
      intro σ σ' hσ
      have hσ_u : SubstRel 𝕄 remove str Γ δ .oneMode σ σ' :=
        subsumption_substRel (fun x h0 ↦ hw.meet_positive_right h0) hσ
      have ih_u := erasedRelGraded_nonZero hw.nonTrivial (hu σ σ' hσ_u)
      apply erasedRel_to_graded
      refine ⟨GTerm.subst σ t, GTerm.subst σ u, .refl _,
        TargetTerm.subst σ' (erase 𝕄 remove str u), ih_u, ?_⟩
      by_cases hp : p = 𝕄.zero
      · simp only [hp, ↓reduceIte, erase]
        exact .refl _
      · simp only [hp, ↓reduceIte, erase, TargetTerm.subst]
        have hσ_t : SubstRel 𝕄 remove str Γ γ .oneMode σ σ' :=
          subsumption_substRel (fun x h0 ↦ by
            rcases hw.zero_product (hw.meet_positive_left h0) with h1 | h2
            · exact False.elim (hp h1)
            · exact h2) hσ
        have hm_p : Mode.scale 𝕄 .oneMode p = .oneMode := Mode.scale_oneMode_ne_zero 𝕄 hp
        rw [hm_p] at ht
        have ih_t := erasedRelGraded_nonZero hw.nonTrivial (ht σ σ' hσ_t)
        exact ⟨TargetTerm.subst σ' (erase 𝕄 remove str t), .refl _, ih_t⟩

/-- Validity of weak pair `prod .weak` (`prodʷʳ` in
    `Graded/Erasure/LogicalRelation/Fundamental/Pi-Sigma.agda`). -/
theorem valid_prodWeak {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    {remove : Bool} {str : Strictness} {Γ : SemCon 𝕄} {γ δ : Conₘ M} {m : Mode}
    {p q : M} {F G t u : GTerm M} {hF : SemType 𝕄 F} {hG : SemType 𝕄 G}
    (ht : ValidErased 𝕄 remove str Γ γ (Mode.scale 𝕄 m p) t F hF)
    (hu : ValidErased 𝕄 remove str Γ δ m u G hG) :
    ValidErased 𝕄 remove str Γ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 p γ) δ) m
      (.prod .weak p t u) (.sigma .weak p q F G)
      (.sigma .weak p q F G (.refl _) hF hG) := by
  cases m with
  | zeroMode => exact validErased_zeroMode
  | oneMode =>
      intro σ σ' hσ
      have hσ_u : SubstRel 𝕄 remove str Γ δ .oneMode σ σ' :=
        subsumption_substRel (fun x h0 ↦ hw.add_positive_right h0) hσ
      have ih_u := erasedRelGraded_nonZero hw.nonTrivial (hu σ σ' hσ_u)
      apply erasedRel_to_graded
      refine ⟨GTerm.subst σ t, GTerm.subst σ u, .refl _,
        TargetTerm.subst σ' (erase 𝕄 remove str u), ih_u, ?_⟩
      by_cases hp : p = 𝕄.zero
      · simp only [hp, ↓reduceIte, erase]
        exact .refl _
      · simp only [hp, ↓reduceIte, erase, TargetTerm.subst]
        have hσ_t : SubstRel 𝕄 remove str Γ γ .oneMode σ σ' :=
          subsumption_substRel (fun x h0 ↦ by
            rcases hw.zero_product (hw.add_positive_left h0) with h1 | h2
            · exact False.elim (hp h1)
            · exact h2) hσ
        have hm_p : Mode.scale 𝕄 .oneMode p = .oneMode := Mode.scale_oneMode_ne_zero 𝕄 hp
        rw [hm_p] at ht
        have ih_t := erasedRelGraded_nonZero hw.nonTrivial (ht σ σ' hσ_t)
        exact ⟨TargetTerm.subst σ' (erase 𝕄 remove str t), .refl _, ih_t⟩

/-- Validity of `fst` (`fstʳ` in `Graded/Erasure/LogicalRelation/Fundamental/Pi-Sigma.agda`). -/
theorem valid_fst {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    {remove : Bool} {str : Strictness} {Γ : SemCon 𝕄} {γ : Conₘ M} {m : Mode}
    {p q : M} {F G t : GTerm M} {hF : SemType 𝕄 F} {hG : SemType 𝕄 G}
    (hle : 𝕄.le (𝕄.mul (Mode.toGrade 𝕄 m) p) (Mode.toGrade 𝕄 m))
    (ht : ValidErased 𝕄 remove str Γ γ m t (.sigma .strong p q F G)
      (.sigma .strong p q F G (.refl _) hF hG)) :
    ValidErased 𝕄 remove str Γ γ m (.fst p t) F hF := by
  cases m with
  | zeroMode => exact validErased_zeroMode
  | oneMode =>
      intro σ σ' hσ
      simp only [Mode.toGrade, 𝕄.one_mul] at hle
      have hp : p ≠ 𝕄.zero := by
        intro hp0
        rw [hp0] at hle
        exact hw.zero_not_le_one hle
      have ih_t := erasedRelGraded_nonZero hw.nonTrivial (ht σ σ' hσ)
      rcases ih_t with ⟨t₁, t₂, ht12, v₂, _, hrest⟩
      simp only [hp, ↓reduceIte] at hrest
      rcases hrest with ⟨v₁, hv12, hrel1⟩
      apply erasedRel_to_graded
      simp only [GTerm.subst, erase, hp, ↓reduceIte, TargetTerm.subst]
      have h_src : GStar 𝕄 (.fst p (GTerm.subst σ t)) t₁ :=
        GStar.trans (GStar.fst_subst ht12) (.step .sigma_beta1 (.refl t₁))
      have h_tgt : TargetTerm.TargetStar
          (.fst (TargetTerm.subst σ' (erase 𝕄 remove str t))) v₁ :=
        TargetTerm.TargetStar.trans
          (TargetTerm.TargetStar.fst_subst hv12)
          (TargetTerm.TargetStar.single (TargetTerm.TargetStep.sigma_beta1 v₁ v₂))
      exact erasedRel_backwards_closed hF h_src h_tgt hrel1

/-- Validity of `snd` (`sndʳ` in `Graded/Erasure/LogicalRelation/Fundamental/Pi-Sigma.agda`). -/
theorem valid_snd {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    {remove : Bool} {str : Strictness} {Γ : SemCon 𝕄} {γ : Conₘ M} {m : Mode}
    {p q : M} {F G t : GTerm M} {hF : SemType 𝕄 F} {hG : SemType 𝕄 G}
    (ht : ValidErased 𝕄 remove str Γ γ m t (.sigma .strong p q F G)
      (.sigma .strong p q F G (.refl _) hF hG)) :
    ValidErased 𝕄 remove str Γ γ m (.snd p t) G hG := by
  cases m with
  | zeroMode => exact validErased_zeroMode
  | oneMode =>
      intro σ σ' hσ
      have ih_t := erasedRelGraded_nonZero hw.nonTrivial (ht σ σ' hσ)
      rcases ih_t with ⟨t₁, t₂, ht12, v₂, hrel2, hrest⟩
      apply erasedRel_to_graded
      have h_src : GStar 𝕄 (.snd p (GTerm.subst σ t)) t₂ :=
        GStar.trans (GStar.snd_subst ht12) (.step .sigma_beta2 (.refl t₂))
      by_cases hp : p = 𝕄.zero
      · rw [if_pos hp] at hrest
        simp only [GTerm.subst, erase, if_pos hp]
        exact erasedRel_backwards_closed hG h_src hrest hrel2
      · rw [if_neg hp] at hrest
        simp only [GTerm.subst, erase, if_neg hp, TargetTerm.subst]
        rcases hrest with ⟨v₁, hv12, _⟩
        have h_tgt : TargetTerm.TargetStar
            (.snd (TargetTerm.subst σ' (erase 𝕄 remove str t))) v₂ :=
          TargetTerm.TargetStar.trans
            (TargetTerm.TargetStar.snd_subst hv12)
            (TargetTerm.TargetStar.single (TargetTerm.TargetStep.sigma_beta2 v₁ v₂))
        exact erasedRel_backwards_closed hG h_src h_tgt hrel2

/-- Validity of `natrec` (`natrecʳ` in `Graded/Erasure/LogicalRelation/Fundamental/Nat.agda`),
    applicable to all three `natrec` usage rules (`natrec_ineq`, `natrec_fix`, `natrec_glb`). -/
theorem valid_natrec {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    {remove : Bool} {str : Strictness} {Γ : SemCon 𝕄} {γz δs ηn χ : Conₘ M} {m : Mode}
    {p q r q₁ q₂ : M} {Motive z s n A : GTerm M} {hA : SemType 𝕄 A}
    (hz : ValidErased 𝕄 remove str Γ γz m z A hA)
    (hs : ValidErased 𝕄 remove str Γ δs m s (.pi p q₁ .nat (.pi r q₂ A A))
      (.pi p q₁ .nat (.pi r q₂ A A) (.refl _) (.nat (.refl .nat)) (.pi r q₂ A A (.refl _) hA hA)))
    (hn : ValidErased 𝕄 remove str Γ ηn m n .nat (.nat (.refl .nat)))
    (hzero : ∀ x, χ x = 𝕄.zero → γz x = 𝕄.zero ∧ δs x = 𝕄.zero ∧ ηn x = 𝕄.zero) :
    ValidErased 𝕄 remove str Γ χ m (.natrec p q r Motive z s n) A hA := by
  cases m with
  | zeroMode => exact validErased_zeroMode
  | oneMode =>
      intro σ σ' hσ
      have hσ_z : SubstRel 𝕄 remove str Γ γz .oneMode σ σ' :=
        subsumption_substRel (fun x h0 ↦ (hzero x h0).1) hσ
      have hσ_s : SubstRel 𝕄 remove str Γ δs .oneMode σ σ' :=
        subsumption_substRel (fun x h0 ↦ (hzero x h0).2.1) hσ
      have hσ_n : SubstRel 𝕄 remove str Γ ηn .oneMode σ σ' :=
        subsumption_substRel (fun x h0 ↦ (hzero x h0).2.2) hσ
      have ih_z := erasedRelGraded_nonZero hw.nonTrivial (hz σ σ' hσ_z)
      have ih_s := erasedRelGraded_nonZero hw.nonTrivial (hs σ σ' hσ_s)
      have ih_n := erasedRelGraded_nonZero hw.nonTrivial (hn σ σ' hσ_n)
      apply erasedRel_to_graded
      simp only [GTerm.subst, erase, TargetTerm.subst]
      apply erasedRel_natrec hA p q r (GTerm.subst (GTerm.liftSubst σ) Motive)
        (GTerm.subst σ z) (GTerm.subst σ s) (GTerm.subst σ n)
        (TargetTerm.subst σ' (erase 𝕄 remove str z))
        (TargetTerm.subst σ' (erase 𝕄 remove str s))
        (TargetTerm.subst σ' (erase 𝕄 remove str n))
        ih_z _ ih_n
      intro m_val vm hm acc vacc hacc
      have hs1 := ih_s m_val
      have h_step1 : ErasedRel 𝕄 remove str (.pi r q₂ A A (.refl _) hA hA)
          (.app p (GTerm.subst σ s) m_val)
          (appOrZero remove str (decide (p = 𝕄.zero))
            (TargetTerm.subst σ' (erase 𝕄 remove str s)) vm) := by
        by_cases hp : p = 𝕄.zero
        · simp only [hp, ↓reduceIte, decide_true, appOrZero] at hs1 ⊢
          exact hs1
        · simp only [hp, ↓reduceIte, decide_false, appOrZero] at hs1 ⊢
          exact hs1 vm hm
      have hs2 := h_step1 acc
      by_cases hr : r = 𝕄.zero
      · simp only [hr, ↓reduceIte, decide_true, appOrZero] at hs2 ⊢
        exact hs2
      · simp only [hr, ↓reduceIte, decide_false, appOrZero] at hs2 ⊢
        exact hs2 vacc hacc

/-- Graded typing derivation indexed by `SemCon 𝕄` and `SemType 𝕄` for the
    Fundamental Theorem of the Erasure Logical Relation (`GHasSemType`). -/
inductive GHasSemType {M : Type} (𝕄 : Modality M) :
    SemCon 𝕄 → (t A : GTerm M) → SemType 𝕄 A → Type where
  | var {Γ : SemCon 𝕄} {x : Nat} {A : GTerm M} {hA : SemType 𝕄 A} :
      SemLookup x Γ A hA →
      GHasSemType 𝕄 Γ (.var x) A hA
  | zero {Γ : SemCon 𝕄} :
      GHasSemType 𝕄 Γ .zero .nat (.nat (.refl .nat))
  | succ {Γ : SemCon 𝕄} {t : GTerm M} :
      GHasSemType 𝕄 Γ t .nat (.nat (.refl .nat)) →
      GHasSemType 𝕄 Γ (.succ t) .nat (.nat (.refl .nat))
  | star {Γ : SemCon 𝕄} :
      GHasSemType 𝕄 Γ .star .unit (.unit (.refl .unit))
  | unitrec {Γ : SemCon 𝕄} {p q : M} {Motive t u C : GTerm M} {hC : SemType 𝕄 C} :
      p ≠ 𝕄.zero →
      GHasSemType 𝕄 Γ t .unit (.unit (.refl .unit)) →
      GHasSemType 𝕄 Γ u C hC →
      GHasSemType 𝕄 Γ (.unitrec p q Motive t u) C hC
  | lam {Γ : SemCon 𝕄} {p q : M} {F G t : GTerm M} {hF : SemType 𝕄 F} {hG : SemType 𝕄 G} :
      GHasSemType 𝕄 (⟨F, hF⟩ :: Γ) t G hG →
      GHasSemType 𝕄 Γ (.lam p t) (.pi p q F G) (.pi p q F G (.refl _) hF hG)
  | app {Γ : SemCon 𝕄} {p q : M} {F G t u : GTerm M} {hF : SemType 𝕄 F} {hG : SemType 𝕄 G} :
      GHasSemType 𝕄 Γ t (.pi p q F G) (.pi p q F G (.refl _) hF hG) →
      GHasSemType 𝕄 Γ u F hF →
      GHasSemType 𝕄 Γ (.app p t u) G hG
  | prodStrong {Γ : SemCon 𝕄} {p q : M} {F G t u : GTerm M}
      {hF : SemType 𝕄 F} {hG : SemType 𝕄 G} :
      GHasSemType 𝕄 Γ t F hF →
      GHasSemType 𝕄 Γ u G hG →
      GHasSemType 𝕄 Γ (.prod .strong p t u) (.sigma .strong p q F G)
        (.sigma .strong p q F G (.refl _) hF hG)
  | prodWeak {Γ : SemCon 𝕄} {p q : M} {F G t u : GTerm M}
      {hF : SemType 𝕄 F} {hG : SemType 𝕄 G} :
      GHasSemType 𝕄 Γ t F hF →
      GHasSemType 𝕄 Γ u G hG →
      GHasSemType 𝕄 Γ (.prod .weak p t u) (.sigma .weak p q F G)
        (.sigma .weak p q F G (.refl _) hF hG)
  | fst {Γ : SemCon 𝕄} {p q : M} {F G t : GTerm M}
      {hF : SemType 𝕄 F} {hG : SemType 𝕄 G} :
      GHasSemType 𝕄 Γ t (.sigma .strong p q F G) (.sigma .strong p q F G (.refl _) hF hG) →
      GHasSemType 𝕄 Γ (.fst p t) F hF
  | snd {Γ : SemCon 𝕄} {p q : M} {F G t : GTerm M}
      {hF : SemType 𝕄 F} {hG : SemType 𝕄 G} :
      GHasSemType 𝕄 Γ t (.sigma .strong p q F G) (.sigma .strong p q F G (.refl _) hF hG) →
      GHasSemType 𝕄 Γ (.snd p t) G hG
  | natrec {Γ : SemCon 𝕄} {p q r q₁ q₂ : M} {Motive z s n A : GTerm M} {hA : SemType 𝕄 A} :
      GHasSemType 𝕄 Γ z A hA →
      GHasSemType 𝕄 Γ s (.pi p q₁ .nat (.pi r q₂ A A))
        (.pi p q₁ .nat (.pi r q₂ A A) (.refl _) (.nat (.refl .nat))
          (.pi r q₂ A A (.refl _) hA hA)) →
      GHasSemType 𝕄 Γ n .nat (.nat (.refl .nat)) →
      GHasSemType 𝕄 Γ (.natrec p q r Motive z s n) A hA

/-- **M2 Theorem 6.8 (Fundamental Lemma of the Erasure Logical Relation, `fundamental` in
    `Graded/Erasure/LogicalRelation/Fundamental.agda`)**:
    Under `HasWellBehavedZero`, every well-typed (`GHasSemType 𝕄 Γ t A hA`) and
    well-resourced (`Usage 𝕄 γ m t`) graded term is semantically valid (`ValidErased`). -/
theorem fundamental {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    (remove : Bool) {Γ : SemCon 𝕄} {γ : Conₘ M} {m : Mode}
    {t A : GTerm M} {hA : SemType 𝕄 A}
    (ht : GHasSemType 𝕄 Γ t A hA) (hu : Usage 𝕄 γ m t) :
    ValidErased 𝕄 remove .nonStrict Γ γ m t A hA := by
  induction ht generalizing γ m with
  | var hl =>
      exact valid_var hw hl hu
  | zero =>
      exact valid_zero
  | succ _ ih =>
      exact valid_succ hw (ih (Usage.inv_succ hu))
  | star =>
      exact valid_star
  | unitrec hp_ne _ _ iht ihu =>
      rcases Usage.inv_unitrec hu with ⟨γt, δu, _, hut, huu, _, hle⟩
      exact subsumption_validErased_le hw hle
        (valid_unitrec hw hp_ne (iht hut) (ihu huu))
  | lam _ ih =>
      exact valid_lam hw (ih (Usage.inv_lam hu))
  | app _ _ iht ihu =>
      rcases Usage.inv_app hu with ⟨γf, δa, hf, ha, hle⟩
      exact subsumption_validErased_le hw hle (valid_app hw (iht hf) (ihu ha))
  | prodStrong _ _ iht ihu =>
      rcases Usage.inv_prodStrong hu with ⟨γ1, γ2, h1, h2, hle⟩
      exact subsumption_validErased_le hw hle (valid_prodStrong hw (iht h1) (ihu h2))
  | prodWeak _ _ iht ihu =>
      rcases Usage.inv_prodWeak hu with ⟨γ1, γ2, h1, h2, hle⟩
      exact subsumption_validErased_le hw hle (valid_prodWeak hw (iht h1) (ihu h2))
  | fst _ ih =>
      rcases Usage.inv_fst hu with ⟨hut, hcond⟩
      exact valid_fst hw hcond (ih hut)
  | snd _ ih =>
      have hut := Usage.inv_snd hu
      exact valid_snd hw (ih hut)
  | natrec _ _ _ ihz ihs ihn =>
      rcases Usage.inv_natrec hu with
        ⟨γz, δs, ηn, _, χ, x, huz, hus, hun, _, hx1, _, hχ1, hχ2, hle_γ⟩
      apply subsumption_validErased_le hw hle_γ
      refine valid_natrec hw (ihz huz) (ihs hus) (ihn hun) ?_
      intro y hy
      have h_add := hw.add_positive hy
      have hχy : χ y = 𝕄.zero := h_add.2
      have h1 := hχ1 y; rw [hχy] at h1
      have hgz : γz y = 𝕄.zero := hw.zero_le_eq_zero h1
      have h2 := hχ2 y; rw [hχy] at h2
      have hds : δs y = 𝕄.zero := hw.add_positive_left (hw.zero_le_eq_zero h2)
      have hx_ne : x ≠ 𝕄.zero := by
        intro hx0
        rw [hx0] at hx1
        exact hw.zero_not_le_one hx1
      have hηn : ηn y = 𝕄.zero := by
        rcases hw.zero_product h_add.1 with h0 | h0
        · exact False.elim (hx_ne h0)
        · exact h0
      exact ⟨hgz, hds, hηn⟩

/-- **M2 Theorem 6.8 (`fundamentalErased`, `Graded/Erasure/LogicalRelation/Fundamental.agda`)**:
    In a fully erased usage context `𝟘ᶜ`, every well-typed, well-resourced term `t`
    is related to its extraction `erase 𝕄 remove .nonStrict t` at grade `⌜ m ⌝`. -/
theorem fundamentalErased {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    (remove : Bool) {Γ : SemCon 𝕄} {m : Mode}
    {t A : GTerm M} {hA : SemType 𝕄 A}
    (ht : GHasSemType 𝕄 Γ t A hA) (hu : Usage 𝕄 (Conₘ.zero 𝕄) m t) :
    ErasedRelGraded 𝕄 remove .nonStrict (Mode.toGrade 𝕄 m) hA
      t (erase 𝕄 remove .nonStrict t) := by
  have hval := fundamental hw remove ht hu GTerm.idSubst TargetTerm.idSubst
    (substRel_zero 𝕄 remove .nonStrict Γ m GTerm.idSubst TargetTerm.idSubst)
  simpa only [GTerm.subst_id, TargetTerm.subst_id] using hval

/-- **M2 Theorem 6.8 (`fundamentalErased-𝟙ᵐ`)**:
    In a fully erased usage context `𝟘ᶜ` at mode `𝟙ᵐ`, `t` is directly related to
    `erase 𝕄 remove .nonStrict t` in `ErasedRel`. -/
theorem fundamentalErased_oneMode {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    (remove : Bool) {Γ : SemCon 𝕄}
    {t A : GTerm M} {hA : SemType 𝕄 A}
    (ht : GHasSemType 𝕄 Γ t A hA) (hu : Usage 𝕄 (Conₘ.zero 𝕄) .oneMode t) :
    ErasedRel 𝕄 remove .nonStrict hA t (erase 𝕄 remove .nonStrict t) :=
  erasedRelGraded_nonZero hw.nonTrivial (fundamentalErased hw remove ht hu)

/-- **M2 Theorem 6.9 (Soundness of Extraction for Natural Numbers, `soundness-ℕ` in
    `Graded/Erasure/Consequences/Soundness.agda`)**:
    Under `HasWellBehavedZero`, if `t` has type `ℕ` (`GHasSemType 𝕄 Γ t .nat (.nat (.refl .nat))`)
    and is resourced by the zero usage context `𝟘ᶜ ▸[𝟙ᵐ] t`, then there exists a natural
    number `k : Nat` such that:
    1. `t` reduces in source numeral reduction (`GStarNum`) to `GTerm.suck k`, and
    2. `erase 𝕄 remove .nonStrict t` reduces in target numeral reduction (`TargetStarNum`)
       to `TargetTerm.suck k`. -/
theorem soundness_nat {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    (remove : Bool) {Γ : SemCon 𝕄} {t : GTerm M}
    (ht : GHasSemType 𝕄 Γ t .nat (.nat (.refl .nat)))
    (hu : Usage 𝕄 (Conₘ.zero 𝕄) .oneMode t) :
    ∃ k : Nat, GStarNum 𝕄 t (GTerm.suck k) ∧
      TargetTerm.TargetStarNum (erase 𝕄 remove .nonStrict t) (TargetTerm.suck k) :=
  soundness_nat_of_erasedRelNat (fundamentalErased_oneMode hw remove ht hu)

/-- **Deterministic Corollary of M2 Theorem 6.9 (`soundness_nat_canonical`)**:
    If a well-typed, `𝟘ᶜ`-resourced term `t` of type `ℕ` reduces to `GTerm.suck k`,
    then its extracted target term `erase 𝕄 remove .nonStrict t` reduces to
    `TargetTerm.suck k` for the exact same numeral `k`. -/
theorem soundness_nat_canonical {M : Type} {𝕄 : Modality M} (hw : 𝕄.HasWellBehavedZero)
    (remove : Bool) {Γ : SemCon 𝕄} {t : GTerm M} {k : Nat}
    (ht : GHasSemType 𝕄 Γ t .nat (.nat (.refl .nat)))
    (hu : Usage 𝕄 (Conₘ.zero 𝕄) .oneMode t)
    (hred : GStarNum 𝕄 t (GTerm.suck k)) :
    TargetTerm.TargetStarNum (erase 𝕄 remove .nonStrict t) (TargetTerm.suck k) := by
  rcases soundness_nat hw remove ht hu with ⟨k', hsrc, htgt⟩
  have heq := GStarNum.suck_deterministic hred hsrc
  subst heq
  exact htgt

/-! ## 5. Formalized Counterexamples for Scope Conditions (M2 Section 6.3) -/

/-- **Counterexample 1 (`erased_match_open_counterexample`, M2 Section 6.3)**:
    In an open context, if erased matches (`unitrec 𝟘`) are permitted, the stuck neutral
    source term `t = unitrec 𝟘 𝟙 ℕ (var 0) zero` cannot step in `GStep 𝕄`, so it never
    reduces to `GTerm.zero`. However, its extraction `erase 𝕄 remove str t` is `.zero`,
    which reduces in `0` steps to `TargetTerm.zero`!
    This formally witnesses why M2 Theorem 6.9 requires either `NoErasedMatches` (`p ≠ 𝟘`)
    or a closed/erasable context (`𝟘ᶜ ▸[𝟙ᵐ] t`, which forbids `var 0` at a non-zero grade). -/
theorem erased_match_open_counterexample {M : Type} (𝕄 : Modality M)
    (remove : Bool) (str : Strictness) :
    let t : GTerm M := .unitrec 𝕄.zero 𝕄.one .nat (.var 0) .zero
    (∀ u : GTerm M, ¬ GStep 𝕄 t u) ∧
    ¬ GStarNum 𝕄 t (GTerm.suck 0) ∧
    erase 𝕄 remove str t = TargetTerm.suck 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hs
    cases hs with
    | unitrec_subst hvar => cases hvar
  · intro hstar
    cases hstar with
    | whnf_step hs _ =>
        cases hs with
        | unitrec_subst hvar => cases hvar
  · simp [erase, TargetTerm.suck]

/-- **Counterexample 2 (`trivial_modality_breaks_erasure`, M2 Section 6.1)**:
    Without `HasWellBehavedZero` (specifically when `𝟙 = 𝟘` in the trivial 1-element
    modality), `var 0` is well-resourced by `𝟘ᶜ` at `𝟙ᵐ` (`𝟘ᶜ ▸[𝟙ᵐ] var 0`), yet variable `0`
    still occurs free (`HasX 0`) in `erase`! This formally witnesses why `HasWellBehavedZero`
    is necessary for M2 Theorem 6.4 (`erased_not_hasX`). -/
def TrivialModality : Modality Unit where
  zero := ()
  one := ()
  omega := ()
  add _ _ := ()
  mul _ _ := ()
  meet _ _ := ()
  decEqZero _ := isTrue rfl
  add_assoc _ _ _ := rfl
  add_comm _ _ := rfl
  zero_add _ := rfl
  add_zero _ := rfl
  mul_assoc _ _ _ := rfl
  mul_one _ := rfl
  one_mul _ := rfl
  mul_zero _ := rfl
  zero_mul _ := rfl
  left_distrib _ _ _ := rfl
  right_distrib _ _ _ := rfl
  meet_assoc _ _ _ := rfl
  meet_comm _ _ := rfl
  meet_idem _ := rfl
  mul_left_distrib_meet _ _ _ := rfl
  mul_right_distrib_meet _ _ _ := rfl
  add_left_distrib_meet _ _ _ := rfl
  add_right_distrib_meet _ _ _ := rfl
  omega_le_one := rfl
  omega_mul_add_le _ _ := rfl

theorem trivial_modality_breaks_erasure (remove : Bool) (str : Strictness) :
    Usage TrivialModality (Conₘ.zero TrivialModality) .oneMode (.var 0) ∧
    (Conₘ.zero TrivialModality) 0 = TrivialModality.zero ∧
    TargetTerm.HasX 0 (erase TrivialModality remove str (.var 0)) := by
  refine ⟨?_, rfl, .var 0⟩
  have h : Conₘ.zero TrivialModality =
      Conₘ.single TrivialModality 0 (Mode.toGrade TrivialModality .oneMode) := by
    funext x; rfl
  rw [h]
  exact .var

end FeasibleUnivalence


