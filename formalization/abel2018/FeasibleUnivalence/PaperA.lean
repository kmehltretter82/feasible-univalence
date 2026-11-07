/-
Copyright (c) 2026 Feasible Univalence Project.
Released under the MIT license; see the source artifact LICENSE.

Paper A (Gates G2 & G3): Resource Correctness Survives Erasure
==============================================================

This module formalizes the operational and quantitative bridge for **Paper A**
(*Resource Correctness Survives Erasure*, `docs/formalization-roadmap.md` & `docs/proof-ideas.md`,
Gates G2 and G3), addressing the open problem of extending M3's source-machine resource
theorem (`HeapMachine.lean`) across M2's erasing extraction (`Erasure.lean`) to an
untyped, ungraded target closure machine (`TargetState`).

Key contents:
1. **Extracted Target Closure Machine (`TargetEntry`, `TargetCont`, `TargetHeap`, `TargetState`)**:
   - Executes extracted `TargetTerm` closures (`erase 𝕄 false .nonStrict`) with `Wk`
     pointer environments.
   - Contains **no types** (`A`) and **no grades** (`p, q, r : M`) in terms, continuations,
     or heap cells at runtime.
   - Determinism (`targetHeapNumStep_det`) and canonical numeral irreducibility
     (`target_suck_empty_no_step`).
2. **Erasing Compiler & Environment Simulation (`compileState`, `ErasedHeapRel`, `ErasedStateRel`)**:
   - Compiles graded source states `State M` to `TargetState` using `erase 𝕄 false .nonStrict`.
   - Erased function arguments (`p = 𝕄.zero` in `.app p t u`) are erased at compile time
     to `.undef` (`appZero false .nonStrict (erase t) = .app .nonStrict (erase t) .undef`),
     allocating `⟨.undef, ρ⟩` on the target heap without keeping or evaluating `u`.
3. **Erasure Non-Access & Lockstep Simulation (`erased_slot_never_accessed`,
   `erased_heap_lockstep_sim`, `erased_heap_star_sim`, `erased_binding_never_accessed`)**:
   - Proves that under `𝕄.HasWellBehavedZero`, any heap cell with grade `𝕄.zero` is never
     accessed by `HeapLookup` when stack multiplicity is non-zero.
   - Establishes 1-to-1 lockstep simulation between tracked source execution (`HeapNumStep` /
     `HeapNumStar`) and extracted target closure-machine execution (`TargetHeapNumStep` /
     `TargetHeapNumStar`).
4. **Affine Resource Budget Invariant & Linear Resource Conservation Law**:
   - Explicit trace accounting (`StepUsed`, `TraceUsed`, `InitialHeapLive`, `InitialHeapAvail`)
     proving the affine invariant
     $$\operatorname{used}(\tau)(x) + \operatorname{live}(s')(x) \le \operatorname{available}(s)(x)$$
     on `NatPlusInfinity` and `AffineModality`, and the linear conservation law
     $$\operatorname{used}(\tau)(x) + \operatorname{retained}(s')(x) = \operatorname{available}(s)(x)$$
     accounting for resources stored in returned closures.
5. **Main Theorem of Paper A (`paper_A_resource_correctness_after_erasure`)**.
6. **Gate G2/G3 Benchmark (`fold_capturing_closure_example`) & Failure-Test Counterexamples**
   (`cbv_erased_eval_counterexample`, `affine_duplication_counterexample`,
   `linear_discard_counterexample`).
-/
import FeasibleUnivalence.Modality
import FeasibleUnivalence.Usage
import FeasibleUnivalence.Erasure
import FeasibleUnivalence.HeapMachine

namespace FeasibleUnivalence

open Abel2018

/-! ## 1. Extracted Target Closure Machine (`TargetEntry`, `TargetCont`, `TargetHeap`, `TargetState`) -/

/-- A closure in the extracted target machine: an untyped, ungraded `TargetTerm`
    paired with an environment weakening `env : Wk`. -/
structure TargetEntry where
  term : TargetTerm
  env : Wk
  deriving DecidableEq, Repr

namespace TargetEntry

def wk (ρ : Wk) (e : TargetEntry) : TargetEntry :=
  ⟨e.term, compWk ρ e.env⟩

def wk1 (e : TargetEntry) : TargetEntry :=
  ⟨e.term, .step e.env⟩

@[simp] theorem wk_step_id (e : TargetEntry) : wk (.step .id) e = wk1 e := by
  cases e; rfl

end TargetEntry

/-- Target continuation frames: all type motives `A` and modality grades `p, q, r : M`
    have been erased; only boolean erasure flags (`pz`, `rz`) for `prodrec`/`natrec`
    and `TargetTerm` branches remain. -/
inductive TargetCont where
  | appₑ : TargetTerm → Wk → TargetCont
  | fstₑ : TargetCont
  | sndₑ : TargetCont
  | prodrecₑ : Bool → TargetTerm → Wk → TargetCont
  | unitrecₑ : TargetTerm → Wk → TargetCont
  | natrecₑ : Bool → Bool → TargetTerm → TargetTerm → Wk → TargetCont
  | sucₑ : TargetCont
  deriving DecidableEq, Repr

namespace TargetCont

def wk (ρ : Wk) : TargetCont → TargetCont
  | .appₑ u ρ' => .appₑ u (compWk ρ ρ')
  | .fstₑ => .fstₑ
  | .sndₑ => .sndₑ
  | .prodrecₑ pz u ρ' => .prodrecₑ pz u (compWk ρ ρ')
  | .unitrecₑ u ρ' => .unitrecₑ u (compWk ρ ρ')
  | .natrecₑ pz rz z s ρ' => .natrecₑ pz rz z s (compWk ρ ρ')
  | .sucₑ => .sucₑ

def wk1 : TargetCont → TargetCont := wk (.step .id)
def wk2 : TargetCont → TargetCont := wk (.step (.step .id))

end TargetCont

/-- Target evaluation stacks. -/
abbrev TargetStack := List TargetCont

namespace TargetStack

def wk (ρ : Wk) : TargetStack → TargetStack
  | [] => []
  | c :: S => TargetCont.wk ρ c :: wk ρ S

def wk1 : TargetStack → TargetStack := wk (.step .id)
def wk2 : TargetStack → TargetStack := wk (.step (.step .id))

def sucs : Nat → TargetStack
  | 0 => []
  | k + 1 => .sucₑ :: sucs k

@[simp] theorem wk_sucs (ρ : Wk) : ∀ k : Nat, wk ρ (sucs k) = sucs k
  | 0 => rfl
  | k + 1 => congrArg (List.cons TargetCont.sucₑ) (wk_sucs ρ k)

end TargetStack

/-- Runtime heap of the extracted target machine: stores `TargetEntry` closures
    (or `.dummy` placeholders) with **no grades** at runtime. -/
inductive TargetHeap where
  | nil : TargetHeap
  | cons : TargetHeap → TargetEntry → TargetHeap
  | dummy : TargetHeap → TargetHeap
  deriving DecidableEq, Repr

namespace TargetHeap

def size : TargetHeap → Nat
  | .nil => 0
  | .cons H _ => H.size + 1
  | .dummy H => H.size + 1

def dummies : Nat → TargetHeap
  | 0 => .nil
  | k + 1 => .dummy (dummies k)

end TargetHeap

/-- Untyped, ungraded pointer lookup in `TargetHeap`.
    Note that `.dummy` cells cannot be looked up at index `0`, and no grades are checked
    or mutated at runtime. -/
inductive TargetLookup : TargetHeap → Nat → TargetEntry → Prop where
  | here {H : TargetHeap} {e : TargetEntry} :
      TargetLookup (.cons H e) 0 (TargetEntry.wk1 e)
  | there {H : TargetHeap} {x : Nat} {e e' : TargetEntry} :
      TargetLookup H x e →
      TargetLookup (.cons H e') (x + 1) (TargetEntry.wk1 e)
  | thereDummy {H : TargetHeap} {x : Nat} {e : TargetEntry} :
      TargetLookup H x e →
      TargetLookup (.dummy H) (x + 1) (TargetEntry.wk1 e)

namespace TargetLookup

theorem det {H : TargetHeap} {x : Nat} {e₁ e₂ : TargetEntry}
    (h₁ : TargetLookup H x e₁) (h₂ : TargetLookup H x e₂) : e₁ = e₂ := by
  induction h₁ generalizing e₂ with
  | here =>
    cases h₂ with
    | here => rfl
  | there h₁ ih =>
    cases h₂ with
    | there h₂ => rw [ih h₂]
  | thereDummy h₁ ih =>
    cases h₂ with
    | thereDummy h₂ => rw [ih h₂]

end TargetLookup

/-- Configuration of the extracted target closure machine. -/
structure TargetState where
  heap : TargetHeap
  head : TargetTerm
  env : Wk
  stack : TargetStack
  deriving DecidableEq, Repr

/-- Initial target machine state for evaluating an extracted `TargetTerm` in a dummy
    context of size `k`. -/
def initialTargetState (k : Nat) (t : TargetTerm) : TargetState :=
  ⟨TargetHeap.dummies k, t, .id, []⟩

/-- Elimination frame pushes on the extracted target closure machine (`⇒ₑ` on `TargetState`). -/
inductive TargetElimStep : TargetState → TargetState → Prop where
  | appₕ {H : TargetHeap} {s : Strictness} {t u : TargetTerm} {ρ : Wk} {S : TargetStack} :
      TargetElimStep ⟨H, .app s t u, ρ, S⟩ ⟨H, t, ρ, .appₑ u ρ :: S⟩
  | fstₕ {H : TargetHeap} {t : TargetTerm} {ρ : Wk} {S : TargetStack} :
      TargetElimStep ⟨H, .fst t, ρ, S⟩ ⟨H, t, ρ, .fstₑ :: S⟩
  | sndₕ {H : TargetHeap} {t : TargetTerm} {ρ : Wk} {S : TargetStack} :
      TargetElimStep ⟨H, .snd t, ρ, S⟩ ⟨H, t, ρ, .sndₑ :: S⟩
  | prodrecₕ {H : TargetHeap} {rem : Bool} {s : Strictness} {pz : Bool}
      {t u : TargetTerm} {ρ : Wk} {S : TargetStack} :
      TargetElimStep ⟨H, .prodrec rem s pz t u, ρ, S⟩ ⟨H, t, ρ, .prodrecₑ pz u ρ :: S⟩
  | unitrecₕ {H : TargetHeap} {t u : TargetTerm} {ρ : Wk} {S : TargetStack} :
      TargetElimStep ⟨H, .unitrec t u, ρ, S⟩ ⟨H, t, ρ, .unitrecₑ u ρ :: S⟩
  | natrecₕ {H : TargetHeap} {rem : Bool} {str : Strictness} {pz rz : Bool}
      {z s n : TargetTerm} {ρ : Wk} {S : TargetStack} :
      TargetElimStep ⟨H, .natrec rem str pz rz z s n, ρ, S⟩
        ⟨H, n, ρ, .natrecₑ pz rz z s ρ :: S⟩

/-- Variable lookup or elimination frame push on `TargetState`. -/
inductive TargetTrackElimStep : TargetState → TargetState → Prop where
  | var {H : TargetHeap} {x : Nat} {t : TargetTerm} {ρ ρ' : Wk} {S : TargetStack} :
      TargetLookup H (wkVar ρ x) ⟨t, ρ'⟩ →
      TargetTrackElimStep ⟨H, .var x, ρ, S⟩ ⟨H, t, ρ', S⟩
  | elim {s₁ s₂ : TargetState} :
      TargetElimStep s₁ s₂ →
      TargetTrackElimStep s₁ s₂

/-- Value β-reductions on the extracted target closure machine (`⇒ᵥ` on `TargetState`). -/
inductive TargetValStep : TargetState → TargetState → Prop where
  | lamₕ {H : TargetHeap} {t u : TargetTerm} {ρ ρ' : Wk} {S : TargetStack} :
      TargetValStep ⟨H, .lam t, ρ, .appₑ u ρ' :: S⟩
        ⟨.cons H ⟨u, ρ'⟩, t, .lift ρ, TargetStack.wk1 S⟩
  | prodStrongₕ₁ {H : TargetHeap} {t₁ t₂ : TargetTerm} {ρ : Wk} {S : TargetStack} :
      TargetValStep ⟨H, .prod t₁ t₂, ρ, .fstₑ :: S⟩
        ⟨H, t₁, ρ, S⟩
  | prodStrongₕ₂ {H : TargetHeap} {t₁ t₂ : TargetTerm} {ρ : Wk} {S : TargetStack} :
      TargetValStep ⟨H, .prod t₁ t₂, ρ, .sndₑ :: S⟩
        ⟨H, t₂, ρ, S⟩
  | prodWeakₕ {H : TargetHeap} {t₁ t₂ u : TargetTerm} {ρ ρ' : Wk} {S : TargetStack} :
      TargetValStep ⟨H, .prod t₁ t₂, ρ, .prodrecₑ false u ρ' :: S⟩
        ⟨.cons (.cons H ⟨t₁, ρ⟩) ⟨t₂, .step ρ⟩,
          .app .nonStrict (.app .nonStrict (TargetTerm.wk (.step (.step .id)) u) (.var 1)) (.var 0),
          .lift (.lift ρ'), TargetStack.wk2 S⟩
  | zeroₕ {H : TargetHeap} {pz rz : Bool} {z s : TargetTerm} {ρ ρ' : Wk} {S : TargetStack} :
      TargetValStep ⟨H, .zero, ρ, .natrecₑ pz rz z s ρ' :: S⟩
        ⟨H, z, ρ', S⟩
  | sucₕ {H : TargetHeap} {pz rz : Bool} {t z s : TargetTerm} {ρ ρ' : Wk} {S : TargetStack} :
      TargetValStep ⟨H, .succ t, ρ, .natrecₑ pz rz z s ρ' :: S⟩
        ⟨.cons (.cons H ⟨t, ρ⟩)
          ⟨.natrec false .nonStrict pz rz (TargetTerm.wk1 z) (TargetTerm.wk1 s) (.var 0), .lift ρ'⟩,
          appOrZero false .nonStrict rz
            (appOrZero false .nonStrict pz (TargetTerm.wk (.step (.step .id)) s) (.var 1))
            (.var 0),
          .lift (.lift ρ'), TargetStack.wk2 S⟩
  | starWeakₕ {H : TargetHeap} {u : TargetTerm} {ρ ρ' : Wk} {S : TargetStack} :
      TargetValStep ⟨H, .star, ρ, .unitrecₑ u ρ' :: S⟩
        ⟨H, u, ρ', S⟩

/-- Numeral evaluation steps (`⇒ₙ`) on `TargetState`. -/
inductive TargetNumStep : TargetState → TargetState → Prop where
  | sucₕ {H : TargetHeap} {t : TargetTerm} {ρ : Wk} {ℓ : Nat} :
      ¬ TargetTerm.Numeral t →
      TargetNumStep ⟨H, .succ t, ρ, TargetStack.sucs ℓ⟩
        ⟨H, t, ρ, .sucₑ :: TargetStack.sucs ℓ⟩
  | numₕ {H : TargetHeap} {t : TargetTerm} {ρ : Wk} {S : TargetStack} :
      TargetTerm.Numeral t →
      TargetNumStep ⟨H, t, ρ, .sucₑ :: S⟩
        ⟨H, .succ t, ρ, S⟩

/-- Single WHNF step on `TargetState`. -/
inductive TargetHeapStep : TargetState → TargetState → Prop where
  | elimStep {s₁ s₂ : TargetState} : TargetTrackElimStep s₁ s₂ → TargetHeapStep s₁ s₂
  | valStep {s₁ s₂ : TargetState} : TargetValStep s₁ s₂ → TargetHeapStep s₁ s₂

/-- Single full-numeral step on `TargetState`. -/
inductive TargetHeapNumStep : TargetState → TargetState → Prop where
  | elimStep {s₁ s₂ : TargetState} : TargetTrackElimStep s₁ s₂ → TargetHeapNumStep s₁ s₂
  | valStep {s₁ s₂ : TargetState} : TargetValStep s₁ s₂ → TargetHeapNumStep s₁ s₂
  | numStep {s₁ s₂ : TargetState} : TargetNumStep s₁ s₂ → TargetHeapNumStep s₁ s₂

/-- Reflexive-transitive closure of `TargetHeapStep`. -/
inductive TargetHeapStar : TargetState → TargetState → Prop where
  | refl (s : TargetState) : TargetHeapStar s s
  | step {s₁ s₂ s₃ : TargetState} :
      TargetHeapStep s₁ s₂ → TargetHeapStar s₂ s₃ → TargetHeapStar s₁ s₃

/-- Reflexive-transitive closure of `TargetHeapNumStep`. -/
inductive TargetHeapNumStar : TargetState → TargetState → Prop where
  | refl (s : TargetState) : TargetHeapNumStar s s
  | step {s₁ s₂ s₃ : TargetState} :
      TargetHeapNumStep s₁ s₂ → TargetHeapNumStar s₂ s₃ → TargetHeapNumStar s₁ s₃

namespace TargetHeapNumStar

theorem single {s₁ s₂ : TargetState} (h : TargetHeapNumStep s₁ s₂) :
    TargetHeapNumStar s₁ s₂ :=
  .step h (.refl s₂)

theorem trans {s₁ s₂ s₃ : TargetState}
    (h₁ : TargetHeapNumStar s₁ s₂) (h₂ : TargetHeapNumStar s₂ s₃) :
    TargetHeapNumStar s₁ s₃ := by
  induction h₁ with
  | refl _ => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

end TargetHeapNumStar

theorem TargetNumStep.not_valStep {s s₁ s₂ : TargetState}
    (hv : TargetValStep s s₁) (hn : TargetNumStep s s₂) : False := by
  generalize hs : s = s₀ at hv
  cases hv <;> {
    cases hn with
    | @sucₕ _ _ _ ℓ _ =>
      cases ℓ <;> simp [TargetStack.sucs] at hs
    | numₕ _ =>
      simp at hs
  }

theorem TargetNumStep.not_trackElimStep {s s₁ s₂ : TargetState}
    (he : TargetTrackElimStep s s₁) (hn : TargetNumStep s s₂) : False := by
  have hnotnum : ¬ TargetTerm.Numeral s.head := by
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

theorem TargetNumStep.det {s s₁ s₂ : TargetState}
    (h₁ : TargetNumStep s s₁) (h₂ : TargetNumStep s s₂) : s₁ = s₂ := by
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

/-- **Determinism of the Extracted Target Closure Machine (`targetHeapNumStep_det`)**:
    at most one transition applies to any `TargetState`. -/
theorem targetHeapNumStep_det {s s₁ s₂ : TargetState}
    (h₁ : TargetHeapNumStep s s₁) (h₂ : TargetHeapNumStep s s₂) : s₁ = s₂ := by
  cases h₁ with
  | elimStep he₁ =>
    cases h₂ with
    | elimStep he₂ =>
      cases he₁ with
      | var hl₁ =>
        cases he₂ with
        | var hl₂ =>
          have h_eq := hl₁.det hl₂
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
      exact False.elim (TargetNumStep.not_trackElimStep he₁ hn₂)
  | valStep hv₁ =>
    cases h₂ with
    | elimStep he₂ =>
      cases he₂ with
      | var _ => cases hv₁
      | elim hel₂ => cases hel₂ <;> cases hv₁
    | valStep hv₂ =>
      cases hv₁ <;> cases hv₂ <;> rfl
    | numStep hn₂ =>
      exact False.elim (TargetNumStep.not_valStep hv₁ hn₂)
  | numStep hn₁ =>
    cases h₂ with
    | elimStep he₂ =>
      exact False.elim (TargetNumStep.not_trackElimStep he₂ hn₁)
    | valStep hv₂ =>
      exact False.elim (TargetNumStep.not_valStep hv₂ hn₁)
    | numStep hn₂ =>
      exact TargetNumStep.det hn₁ hn₂

/-- Canonical target numeral states with an empty stack are irreducible. -/
theorem target_suck_empty_no_step {H : TargetHeap} {k : Nat} {ρ : Wk} {s' : TargetState}
    (h : TargetHeapNumStep ⟨H, TargetTerm.suck k, ρ, []⟩ s') : False := by
  generalize hs : (⟨H, TargetTerm.suck k, ρ, []⟩ : TargetState) = s₀ at h
  cases h with
  | elimStep he =>
    cases he with
    | var _ =>
      injection hs with _ ht _ _
      cases k <;> cases ht
    | elim hel =>
      cases hel <;> (injection hs with _ ht _ _; cases k <;> cases ht)
  | valStep hv =>
    cases hv <;> (injection hs with _ _ _ hS; cases hS)
  | numStep hn =>
    cases hn with
    | @sucₕ _ t _ ℓ hnotnum =>
      injection hs with _ ht _ _
      cases k with
      | zero => cases ht
      | succ k =>
        injection ht with ht'
        subst ht'
        exact hnotnum (TargetTerm.numeral_suck k)
    | numₕ _ =>
      injection hs with _ _ _ hS
      cases hS

/-- `.undef` with an empty stack is irreducible (stuck) on `TargetState`: if an erased
    binding were ever looked up and reached the head, the machine would get stuck. -/
theorem target_undef_empty_no_step {H : TargetHeap} {ρ : Wk} {s' : TargetState}
    (h : TargetHeapNumStep ⟨H, .undef, ρ, []⟩ s') : False := by
  generalize hs : (⟨H, .undef, ρ, []⟩ : TargetState) = s₀ at h
  cases h with
  | elimStep he =>
    cases he with
    | var _ => injection hs with _ ht _ _; cases ht
    | elim hel => cases hel <;> (injection hs with _ ht _ _; cases ht)
  | valStep hv =>
    cases hv <;> (injection hs with _ ht _ _; cases ht)
  | numStep hn =>
    cases hn with
    | sucₕ _ => injection hs with _ ht _ _; cases ht
    | numₕ _ => injection hs with _ _ _ hS; cases hS

/-! ## 2. Erasing Compiler to `TargetState` and Simulation Relation (`ErasedHeapRel`, `ErasedStateRel`) -/

section CompilerAndSimulation

variable {M : Type} (𝕄 : Modality M)

/-- Compile a source closure `Entry M` to a `TargetEntry` using M2's non-strict erasure
    `erase 𝕄 false .nonStrict` (which keeps closure binder indices aligned and erases
    `0`-graded arguments to `.undef`). -/
def compileEntry (e : Entry M) : TargetEntry :=
  ⟨erase 𝕄 false .nonStrict e.term, e.env⟩

@[simp] theorem compileEntry_wk (ρ : Wk) (e : Entry M) :
    compileEntry 𝕄 (Entry.wk ρ e) = TargetEntry.wk ρ (compileEntry 𝕄 e) := rfl

@[simp] theorem compileEntry_wk1 (e : Entry M) :
    compileEntry 𝕄 (Entry.wk1 e) = TargetEntry.wk1 (compileEntry 𝕄 e) := rfl

/-- Compile a source continuation frame `Cont M` to an ungraded, untyped `TargetCont`. -/
def compileCont : Cont M → TargetCont
  | .appₑ p u ρ =>
      .appₑ (if p = 𝕄.zero then .undef else erase 𝕄 false .nonStrict u) ρ
  | .fstₑ _ => .fstₑ
  | .sndₑ _ => .sndₑ
  | .prodrecₑ _ p _ _ u ρ =>
      .prodrecₑ (decide (p = 𝕄.zero)) (erase 𝕄 false .nonStrict u) ρ
  | .unitrecₑ _ _ _ u ρ =>
      .unitrecₑ (erase 𝕄 false .nonStrict u) ρ
  | .natrecₑ p _ r _ z s ρ =>
      .natrecₑ (decide (p = 𝕄.zero)) (decide (r = 𝕄.zero))
        (erase 𝕄 false .nonStrict z) (erase 𝕄 false .nonStrict s) ρ
  | .sucₑ => .sucₑ

@[simp] theorem compileCont_wk (ρ : Wk) (c : Cont M) :
    compileCont 𝕄 (Cont.wk ρ c) = TargetCont.wk ρ (compileCont 𝕄 c) := by
  cases c <;> rfl

/-- Compile a source stack `Stack M` to `TargetStack`. -/
def compileStack : Stack M → TargetStack
  | [] => []
  | c :: S => compileCont 𝕄 c :: compileStack S

@[simp] theorem compileStack_wk (ρ : Wk) :
    ∀ S : Stack M, compileStack 𝕄 (Stack.wk ρ S) = TargetStack.wk ρ (compileStack 𝕄 S)
  | [] => rfl
  | c :: S => by simp [Stack.wk, compileStack, TargetStack.wk, compileStack_wk ρ S]

@[simp] theorem compileStack_wk1 (S : Stack M) :
    compileStack 𝕄 (Stack.wk1 S) = TargetStack.wk1 (compileStack 𝕄 S) :=
  compileStack_wk 𝕄 (.step .id) S

@[simp] theorem compileStack_wk2 (S : Stack M) :
    compileStack 𝕄 (Stack.wk2 S) = TargetStack.wk2 (compileStack 𝕄 S) :=
  compileStack_wk 𝕄 (.step (.step .id)) S

@[simp] theorem compileStack_sucs :
    ∀ ℓ : Nat, compileStack 𝕄 (Stack.sucs (M := M) ℓ) = TargetStack.sucs ℓ
  | 0 => rfl
  | ℓ + 1 => congrArg (List.cons TargetCont.sucₑ) (compileStack_sucs ℓ)

/-- Compile a source heap `Heap M` to `TargetHeap`:
    erased (`0`-graded) bindings are erased to `⟨.undef, e.env⟩` on the target heap,
    removing the source expression completely! -/
def compileHeap : Heap M → TargetHeap
  | .nil => .nil
  | .cons H p e =>
      .cons (compileHeap H)
        (if p = 𝕄.zero then ⟨.undef, e.env⟩ else compileEntry 𝕄 e)
  | .dummy H => .dummy (compileHeap H)

@[simp] theorem compileHeap_erasedHeap :
    ∀ k : Nat, compileHeap 𝕄 (erasedHeap (M := M) k) = TargetHeap.dummies k
  | 0 => rfl
  | k + 1 => congrArg TargetHeap.dummy (compileHeap_erasedHeap k)

/-- Compile a full source configuration `State M` to `TargetState`. -/
def compileState (s : State M) : TargetState :=
  ⟨compileHeap 𝕄 s.heap, erase 𝕄 false .nonStrict s.head, s.env, compileStack 𝕄 s.stack⟩

@[simp] theorem compileState_initial (k : Nat) (t : GTerm M) :
    compileState 𝕄 (initialState k t) =
      initialTargetState k (erase 𝕄 false .nonStrict t) := by
  simp [compileState, initialState, initialTargetState, compileHeap_erasedHeap, compileStack]

/-- Syntactic compatibility predicate for closure-machine erasure (`ErasureCompatible`):
    extends M3's `NoErasedMatches 𝕄` (requiring non-erased scrutinees in `prodrec` and
    `unitrec`) with non-erased component grades in runtime pairs (`prod`, `fst`, `snd`,
    `prodrec`), while permitting **arbitrary erased (`𝕄.zero`) or non-erased grades**
    in functions (`lam`, `app`) and recursion (`natrec`). -/
def ErasureCompatible : GTerm M → Prop
  | .var _ | .univ | .nat | .unit | .zero | .star => True
  | .pi _ _ A B | .sigma _ _ _ A B =>
      ErasureCompatible A ∧ ErasureCompatible B
  | .lam _ t => ErasureCompatible t
  | .app _ t u => ErasureCompatible t ∧ ErasureCompatible u
  | .prod _ p t u => p ≠ 𝕄.zero ∧ ErasureCompatible t ∧ ErasureCompatible u
  | .fst p t | .snd p t => p ≠ 𝕄.zero ∧ ErasureCompatible t
  | .prodrec r p _ _ t u =>
      r ≠ 𝕄.zero ∧ p ≠ 𝕄.zero ∧ ErasureCompatible t ∧ ErasureCompatible u
  | .unitrec p _ _ t u =>
      p ≠ 𝕄.zero ∧ ErasureCompatible t ∧ ErasureCompatible u
  | .succ t => ErasureCompatible t
  | .natrec _ _ _ _ z s n =>
      ErasureCompatible z ∧ ErasureCompatible s ∧ ErasureCompatible n

theorem ErasureCompatible.wk {𝕄 : Modality M} (ρ : Wk) {t : GTerm M}
    (h : ErasureCompatible 𝕄 t) : ErasureCompatible 𝕄 (GTerm.wk ρ t) := by
  induction t generalizing ρ with
  | var _ | univ | nat | unit | zero | star => trivial
  | pi _ _ _ _ ihA ihB | sigma _ _ _ _ _ ihA ihB => exact ⟨ihA ρ h.1, ihB (.lift ρ) h.2⟩
  | lam _ _ ih => exact ih (.lift ρ) h
  | app _ _ _ iht ihu => exact ⟨iht ρ h.1, ihu ρ h.2⟩
  | prod _ _ _ _ iht ihu => exact ⟨h.1, iht ρ h.2.1, ihu ρ h.2.2⟩
  | fst _ _ ih | snd _ _ ih => exact ⟨h.1, ih ρ h.2⟩
  | prodrec _ _ _ _ _ _ _ iht ihu => exact ⟨h.1, h.2.1, iht ρ h.2.2.1, ihu ρ h.2.2.2⟩
  | unitrec _ _ _ _ _ _ iht ihu => exact ⟨h.1, iht ρ h.2.1, ihu ρ h.2.2⟩
  | succ _ ih => exact ih ρ h
  | natrec _ _ _ _ _ _ _ _ ihz ihs ihn => exact ⟨ihz ρ h.1, ihs ρ h.2.1, ihn ρ h.2.2⟩

theorem ErasureCompatible.suck (k : Nat) : ErasureCompatible 𝕄 (GTerm.suck k) := by
  induction k with
  | zero => trivial
  | succ k ih => exact ih

/-- `ErasureCompatible` on continuation frames. -/
def ContErasureCompatible : Cont M → Prop
  | .appₑ p u _ => p ≠ 𝕄.zero → ErasureCompatible 𝕄 u
  | .fstₑ _ | .sndₑ _ | .sucₑ => True
  | .prodrecₑ r p _ _ u _ =>
      r ≠ 𝕄.zero ∧ p ≠ 𝕄.zero ∧ ErasureCompatible 𝕄 u
  | .unitrecₑ p _ _ u _ =>
      p ≠ 𝕄.zero ∧ ErasureCompatible 𝕄 u
  | .natrecₑ _ _ _ _ z s _ =>
      ErasureCompatible 𝕄 z ∧ ErasureCompatible 𝕄 s

/-- `ErasureCompatible` on evaluation stacks. -/
def StackErasureCompatible : Stack M → Prop
  | [] => True
  | c :: S => ContErasureCompatible 𝕄 c ∧ StackErasureCompatible S

theorem StackErasureCompatible.wk {𝕄 : Modality M} (ρ : Wk) {S : Stack M}
    (hS : StackErasureCompatible 𝕄 S) : StackErasureCompatible 𝕄 (Stack.wk ρ S) := by
  induction S with
  | nil => trivial
  | cons c S ih =>
    rcases hS with ⟨hc, hS'⟩
    refine ⟨?_, ih hS'⟩
    cases c <;> simp [Cont.wk, ContErasureCompatible] at hc ⊢ <;> exact hc

/-- Under `HasWellBehavedZero` and `nr₂ p r ≠ 𝕄.zero`, every `StackErasureCompatible`
    stack has non-zero multiplicity `Stack.mult 𝕄 nr₂ S ≠ 𝕄.zero`. -/
theorem StackErasureCompatible.mult_ne_zero {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero)
    (hnr_nz : ∀ p r, nr₂ p r ≠ 𝕄.zero)
    {S : Stack M} (hS : StackErasureCompatible 𝕄 S) :
    Stack.mult 𝕄 nr₂ S ≠ 𝕄.zero := by
  induction S with
  | nil => exact hw.nonTrivial
  | cons c S ih =>
    rcases hS with ⟨hc, hS'⟩
    have hS_nz := ih hS'
    have hc_nz : Cont.mult 𝕄 nr₂ c ≠ 𝕄.zero := by
      cases c with
      | appₑ _ _ _ | fstₑ _ | sndₑ _ | sucₑ => exact hw.nonTrivial
      | prodrecₑ r _ _ _ _ _ => exact hc.1
      | unitrecₑ p _ _ _ _ => exact hc.1
      | natrecₑ p _ r _ _ _ _ => exact hnr_nz p r
    intro hmul
    rcases hw.zero_product hmul with h0 | h0
    · exact hS_nz h0
    · exact hc_nz h0

/-- In any modality with `HasWellBehavedZero`, any `NatrecMultFn` satisfies
    `nr₂ p r ≠ 𝕄.zero` because `nr₂ p r ≤ 𝕄.one` and `𝕄.zero ≤ 𝕄.one` would force `𝕄.one = 𝕄.zero`. -/
theorem NatrecMultFn.ne_zero {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂) (p r : M) :
    nr₂ p r ≠ 𝕄.zero := by
  intro h0
  have hle := hnr.le_one p r
  rw [h0] at hle
  exact hw.nonTrivial (hw.zero_le_eq_zero hle)

/-- **Environment / Heap Simulation Relation (`ErasedHeapRel 𝕄 H TH`)**:
    relates a graded source heap `H : Heap M` to an ungraded target heap `TH : TargetHeap`:
    - Every cell with `p ≠ 𝕄.zero` in `H` must be compiled to `compileEntry 𝕄 e` in `TH`
      and satisfy `ErasureCompatible 𝕄 e.term`.
    - Every erased cell with `p = 𝕄.zero` in `H` may correspond to **any** `TargetEntry`
      `te` in `TH` (in particular `⟨.undef, e.env⟩` produced by `compileHeap`), because
      erased cells can never be accessed! -/
inductive ErasedHeapRel : Heap M → TargetHeap → Prop where
  | nil : ErasedHeapRel .nil .nil
  | cons_live {H : Heap M} {TH : TargetHeap} {p : M} {e : Entry M} :
      p ≠ 𝕄.zero →
      ErasureCompatible 𝕄 e.term →
      ErasedHeapRel H TH →
      ErasedHeapRel (.cons H p e) (.cons TH (compileEntry 𝕄 e))
  | cons_erased {H : Heap M} {TH : TargetHeap} {p : M} {e : Entry M} {te : TargetEntry} :
      (p ≠ 𝕄.zero → te = compileEntry 𝕄 e ∧ ErasureCompatible 𝕄 e.term) →
      ErasedHeapRel H TH →
      ErasedHeapRel (.cons H p e) (.cons TH te)
  | dummy {H : Heap M} {TH : TargetHeap} :
      ErasedHeapRel H TH →
      ErasedHeapRel (.dummy H) (.dummy TH)

namespace ErasedHeapRel

variable {𝕄 : Modality M}

theorem of_erasedHeap :
    ∀ k : Nat, ErasedHeapRel 𝕄 (erasedHeap (M := M) k) (TargetHeap.dummies k)
  | 0 => .nil
  | k + 1 => .dummy (of_erasedHeap k)

/-- Pushing a pair `(p, e)` onto `H` and `(if p = 0 then .undef else erase e, e.env)`
    onto `TH` preserves `ErasedHeapRel`. -/
theorem cons_compiled {H : Heap M} {TH : TargetHeap} (p : M) (e : Entry M)
    (hec : p ≠ 𝕄.zero → ErasureCompatible 𝕄 e.term)
    (hrel : ErasedHeapRel 𝕄 H TH) :
    ErasedHeapRel 𝕄 (.cons H p e)
      (.cons TH (if p = 𝕄.zero then ⟨.undef, e.env⟩ else compileEntry 𝕄 e)) := by
  apply ErasedHeapRel.cons_erased _ hrel
  intro hp
  simp [hp, hec hp]

end ErasedHeapRel

/-- **Full State Simulation Relation (`ErasedStateRel 𝕄 s ts`)** between a source
    machine configuration `s : State M` and an extracted target configuration `ts : TargetState`. -/
structure ErasedStateRel (s : State M) (ts : TargetState) : Prop where
  heapRel : ErasedHeapRel 𝕄 s.heap ts.heap
  headEq : ts.head = erase 𝕄 false .nonStrict s.head
  envEq : ts.env = s.env
  stackEq : ts.stack = compileStack 𝕄 s.stack
  headCompat : ErasureCompatible 𝕄 s.head
  stackCompat : StackErasureCompatible 𝕄 s.stack

theorem erasedStateRel_initial {𝕄 : Modality M} (k : Nat) {t : GTerm M}
    (ht : ErasureCompatible 𝕄 t) :
    ErasedStateRel 𝕄 (initialState k t) (compileState 𝕄 (initialState k t)) := by
  rw [compileState_initial]
  exact ⟨ErasedHeapRel.of_erasedHeap k, rfl, rfl, rfl, ht, trivial⟩

end CompilerAndSimulation

/-! ## 3. Erasure Non-Access Theorem & Lockstep Simulation (`erased_slot_never_accessed`, `erased_heap_lockstep_sim`) -/

/-- **Erasure Non-Access Lemma (`erased_slot_never_accessed`)**:
    Under `𝕄.HasWellBehavedZero`, any source `HeapLookup 𝕄 H x q e H'` with non-zero demand
    `q ≠ 𝕄.zero`:
    1. **Never accesses an erased (`0`-graded) binding** in `H` (if the slot at index `x`
       had grade `𝕄.zero`, `SubEq 𝕄 𝕄.zero r q` would force `q = 𝕄.zero`, contradiction),
    2. Succeeds in `TargetLookup TH x (compileEntry 𝕄 e)` on any related target heap `TH`,
    3. Preserves `ErasedHeapRel 𝕄 H' TH` (without modifying `TH`!). -/
theorem erased_slot_never_accessed {M : Type} {𝕄 : Modality M}
    (hw : 𝕄.HasWellBehavedZero)
    {H H' : Heap M} {TH : TargetHeap} {x : Nat} {q : M} {e : Entry M}
    (hrel : ErasedHeapRel 𝕄 H TH)
    (hq : q ≠ 𝕄.zero)
    (hl : HeapLookup 𝕄 H x q e H') :
    TargetLookup TH x (compileEntry 𝕄 e) ∧
    ErasureCompatible 𝕄 e.term ∧
    ErasedHeapRel 𝕄 H' TH := by
  induction hrel generalizing x e H' with
  | nil => cases hl
  | @cons_live H₀ TH₀ p e₀ hp hec hrel ih =>
    cases hl with
    | here _ =>
      refine ⟨.here, hec, .cons_erased (fun _ ↦ ⟨rfl, hec⟩) hrel⟩
    | there hl' =>
      rcases ih hl' with ⟨tl', hec', hrel'⟩
      refine ⟨.there tl', hec', .cons_live hp hec hrel'⟩
  | @cons_erased H₀ TH₀ p e₀ te₀ hcond hrel ih =>
    cases hl with
    | here hsub =>
      have hp : p ≠ 𝕄.zero := by
        intro hp0
        rw [hp0] at hsub
        exact hq (hw.zero_sub_eq hsub).2
      rcases hcond hp with ⟨hte, hec⟩
      subst hte
      refine ⟨.here, hec, .cons_erased (fun _ ↦ ⟨rfl, hec⟩) hrel⟩
    | there hl' =>
      rcases ih hl' with ⟨tl', hec', hrel'⟩
      refine ⟨.there tl', hec', .cons_erased hcond hrel'⟩
  | dummy hrel ih =>
    cases hl with
    | thereDummy hl' =>
      rcases ih hl' with ⟨tl', hec', hrel'⟩
      refine ⟨.thereDummy tl', hec', .dummy hrel'⟩

/-- Helper relating `GNumeral` on source terms to `TargetTerm.Numeral` on erased terms. -/
theorem erase_numeral_iff {M : Type} (𝕄 : Modality M) {t : GTerm M}
    (hec : ErasureCompatible 𝕄 t) :
    GNumeral t ↔ TargetTerm.Numeral (erase 𝕄 false .nonStrict t) := by
  induction t with
  | zero =>
    simp [erase]
    exact ⟨fun _ ↦ .zero, fun _ ↦ .zero⟩
  | succ t ih =>
    simp only [erase]
    constructor
    · intro h
      cases h with
      | succ hn => exact .succ ((ih hec).mp hn)
    · intro h
      cases h with
      | succ hn => exact .succ ((ih hec).mpr hn)
  | var _ | univ | pi _ _ _ _ | sigma _ _ _ _ _ | nat | unit | star =>
    simp only [erase]
    constructor
    · intro h; cases h
    · intro h; cases h
  | lam p t =>
    by_cases hp : p = 𝕄.zero <;> simp only [erase, hp, ↓reduceIte]
    · constructor <;> (intro h; cases h)
    · constructor <;> (intro h; cases h)
  | app p t u =>
    simp only [erase, appZero]
    constructor
    · intro h; cases h
    · intro h; split at h <;> cases h
  | prod s p t u =>
    rcases hec with ⟨hp, _, _⟩
    simp only [erase, hp, ↓reduceIte]
    constructor <;> (intro h; cases h)
  | fst p t =>
    rcases hec with ⟨hp, _⟩
    simp only [erase, hp, ↓reduceIte]
    constructor <;> (intro h; cases h)
  | snd p t =>
    rcases hec with ⟨hp, _⟩
    simp only [erase, hp, ↓reduceIte]
    constructor <;> (intro h; cases h)
  | prodrec r p q A t u =>
    rcases hec with ⟨hr, _, _, _⟩
    simp only [erase, hr, ↓reduceIte]
    constructor <;> (intro h; cases h)
  | unitrec p q A t u =>
    rcases hec with ⟨hp, _, _⟩
    simp only [erase, hp, ↓reduceIte]
    constructor <;> (intro h; cases h)
  | natrec p q r A z s n =>
    simp only [erase]
    constructor <;> (intro h; cases h)

/-- Helper computing `erase 𝕄 false .nonStrict (.app p f a)` as `appOrZero`. -/
theorem erase_app_eq_appOrZero {M : Type} (𝕄 : Modality M) (p : M) (f a : GTerm M) :
    erase 𝕄 false .nonStrict (.app p f a) =
      appOrZero false .nonStrict (decide (p = 𝕄.zero))
        (erase 𝕄 false .nonStrict f) (erase 𝕄 false .nonStrict a) := by
  simp only [erase, appOrZero]
  by_cases hp : p = 𝕄.zero <;> simp [hp]

/-- **Single-Step Lockstep Simulation (`erased_heap_lockstep_sim`)**:
    Under `𝕄.HasWellBehavedZero` and `NatrecMultFn 𝕄 nr₂`, if `ErasedStateRel 𝕄 s₁ ts₁`
    holds and the source machine takes a tracked step `HeapNumStep 𝕄 nr₂ s₁ s₁'`, then
    the extracted target closure machine takes a matching step `TargetHeapNumStep ts₁ ts₁'`
    such that `ErasedStateRel 𝕄 s₁' ts₁'` holds. -/
theorem erased_heap_lockstep_sim {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s₁ s₁' : State M} {ts₁ : TargetState}
    (hrel : ErasedStateRel 𝕄 s₁ ts₁)
    (hstep : HeapNumStep 𝕄 nr₂ s₁ s₁') :
    ∃ ts₁' : TargetState,
      TargetHeapNumStep ts₁ ts₁' ∧ ErasedStateRel 𝕄 s₁' ts₁' := by
  rcases s₁ with ⟨H, t, ρ, S⟩
  rcases ts₁ with ⟨TH, tt, tρ, TS⟩
  rcases hrel with ⟨hH, htt, hρ, hTS, hec_t, hec_S⟩
  dsimp only at hH htt hρ hTS hec_t hec_S
  subst htt; cases hρ; subst hTS
  have hmult_nz : Stack.mult 𝕄 nr₂ S ≠ 𝕄.zero :=
    hec_S.mult_ne_zero hw (hnr.ne_zero hw)
  cases hstep with
  | elimStep he =>
    cases he with
    | @var _ H' x u ρ_e ρ' S hl =>
      rcases erased_slot_never_accessed hw hH hmult_nz hl with ⟨tl, hec_u, hH'⟩
      refine ⟨⟨TH, erase 𝕄 false .nonStrict u, ρ', compileStack 𝕄 S⟩,
        .elimStep (.var tl), ⟨hH', rfl, rfl, rfl, hec_u, hec_S⟩⟩
    | elim hel =>
      cases hel with
      | @appₕ _ p f u ρ S =>
        rcases hec_t with ⟨hec_f, hec_u⟩
        by_cases hp : p = 𝕄.zero
        · subst hp
          refine ⟨⟨TH, erase 𝕄 false .nonStrict f, ρ,
              .appₑ .undef ρ :: compileStack 𝕄 S⟩,
            ?_, ?_⟩
          · simp only [erase, ↓reduceIte, appZero]
            exact .elimStep (.elim .appₕ)
          · refine ⟨hH, rfl, rfl, ?_, hec_f, ⟨fun hne ↦ False.elim (hne rfl), hec_S⟩⟩
            simp [compileStack, compileCont]
        · refine ⟨⟨TH, erase 𝕄 false .nonStrict f, ρ,
              .appₑ (erase 𝕄 false .nonStrict u) ρ :: compileStack 𝕄 S⟩,
            ?_, ?_⟩
          · simp only [erase, hp, ↓reduceIte]
            exact .elimStep (.elim .appₕ)
          · refine ⟨hH, rfl, rfl, ?_, hec_f, ⟨fun _ ↦ hec_u, hec_S⟩⟩
            simp [compileStack, compileCont, hp]
      | @fstₕ _ p t₀ ρ S =>
        rcases hec_t with ⟨hp, hec_t₀⟩
        refine ⟨⟨TH, erase 𝕄 false .nonStrict t₀, ρ, .fstₑ :: compileStack 𝕄 S⟩, ?_, ?_⟩
        · simp only [erase, hp, ↓reduceIte]
          exact .elimStep (.elim .fstₕ)
        · exact ⟨hH, rfl, rfl, rfl, hec_t₀, ⟨trivial, hec_S⟩⟩
      | @sndₕ _ p t₀ ρ S =>
        rcases hec_t with ⟨hp, hec_t₀⟩
        refine ⟨⟨TH, erase 𝕄 false .nonStrict t₀, ρ, .sndₑ :: compileStack 𝕄 S⟩, ?_, ?_⟩
        · simp only [erase, hp, ↓reduceIte]
          exact .elimStep (.elim .sndₕ)
        · exact ⟨hH, rfl, rfl, rfl, hec_t₀, ⟨trivial, hec_S⟩⟩
      | @prodrecₕ _ r p q A t₀ u ρ S =>
        rcases hec_t with ⟨hr, hp, hec_t₀, hec_u⟩
        refine ⟨⟨TH, erase 𝕄 false .nonStrict t₀, ρ,
            .prodrecₑ (decide (p = 𝕄.zero)) (erase 𝕄 false .nonStrict u) ρ :: compileStack 𝕄 S⟩,
          ?_, ?_⟩
        · simp only [erase, hr, ↓reduceIte]
          exact .elimStep (.elim .prodrecₕ)
        · exact ⟨hH, rfl, rfl, rfl, hec_t₀, ⟨⟨hr, hp, hec_u⟩, hec_S⟩⟩
      | @unitrecₕ _ p q A t₀ u ρ S =>
        rcases hec_t with ⟨hp, hec_t₀, hec_u⟩
        refine ⟨⟨TH, erase 𝕄 false .nonStrict t₀, ρ,
            .unitrecₑ (erase 𝕄 false .nonStrict u) ρ :: compileStack 𝕄 S⟩,
          ?_, ?_⟩
        · simp only [erase, hp, ↓reduceIte]
          exact .elimStep (.elim .unitrecₕ)
        · exact ⟨hH, rfl, rfl, rfl, hec_t₀, ⟨⟨hp, hec_u⟩, hec_S⟩⟩
      | @natrecₕ _ p q r A z s n ρ S =>
        rcases hec_t with ⟨hec_z, hec_s, hec_n⟩
        refine ⟨⟨TH, erase 𝕄 false .nonStrict n, ρ,
            .natrecₑ (decide (p = 𝕄.zero)) (decide (r = 𝕄.zero))
              (erase 𝕄 false .nonStrict z) (erase 𝕄 false .nonStrict s) ρ :: compileStack 𝕄 S⟩,
          .elimStep (.elim .natrecₕ),
          ⟨hH, rfl, rfl, rfl, hec_n, ⟨⟨hec_z, hec_s⟩, hec_S⟩⟩⟩
  | valStep hv =>
    cases hv with
    | @lamₕ _ p body u ρ ρ' S₀ =>
      rcases hec_S with ⟨hc, hS₀⟩
      let u_erased := if p = 𝕄.zero then TargetTerm.undef else erase 𝕄 false .nonStrict u
      refine ⟨⟨.cons TH ⟨u_erased, ρ'⟩,
          erase 𝕄 false .nonStrict body, .lift ρ, TargetStack.wk1 (compileStack 𝕄 S₀)⟩,
        ?_, ?_⟩
      · simp only [erase]
        split <;> exact .valStep .lamₕ
      · refine ⟨?_, rfl, rfl, (compileStack_wk1 𝕄 S₀).symm, hec_t, hS₀.wk (.step .id)⟩
        apply ErasedHeapRel.cons_erased _ hH
        intro hmul_nz
        have hp_nz : p ≠ 𝕄.zero := by
          intro hp0
          rw [hp0, 𝕄.mul_zero] at hmul_nz
          exact hmul_nz rfl
        simp [u_erased, hp_nz, compileEntry, hc hp_nz]
    | @prodStrongₕ₁ _ p t₁ t₂ ρ S₀ =>
      rcases hec_t with ⟨hp, hec₁, _⟩
      refine ⟨⟨TH, erase 𝕄 false .nonStrict t₁, ρ, compileStack 𝕄 S₀⟩, ?_, ?_⟩
      · simp only [erase, hp, ↓reduceIte]
        exact .valStep .prodStrongₕ₁
      · exact ⟨hH, rfl, rfl, rfl, hec₁, hec_S.2⟩
    | @prodStrongₕ₂ _ p t₁ t₂ ρ S₀ =>
      rcases hec_t with ⟨hp, _, hec₂⟩
      refine ⟨⟨TH, erase 𝕄 false .nonStrict t₂, ρ, compileStack 𝕄 S₀⟩, ?_, ?_⟩
      · simp only [erase, hp, ↓reduceIte]
        exact .valStep .prodStrongₕ₂
      · exact ⟨hH, rfl, rfl, rfl, hec₂, hec_S.2⟩
    | @prodWeakₕ _ r p q t₁ t₂ A u ρ ρ' S₀ =>
      rcases hec_t with ⟨hp_pair, hec₁, hec₂⟩
      rcases hec_S with ⟨⟨hr, hp, hec_u⟩, hS₀⟩
      have hrp_nz : 𝕄.mul r p ≠ 𝕄.zero := by
        intro h0
        rcases hw.zero_product h0 with h | h
        · exact hr h
        · exact hp h
      refine ⟨⟨.cons (.cons TH (compileEntry 𝕄 ⟨t₁, ρ⟩)) (compileEntry 𝕄 ⟨t₂, .step ρ⟩),
          .app .nonStrict (.app .nonStrict (TargetTerm.wk (.step (.step .id)) (erase 𝕄 false .nonStrict u)) (.var 1)) (.var 0),
          .lift (.lift ρ'), TargetStack.wk2 (compileStack 𝕄 S₀)⟩,
        ?_, ?_⟩
      · simp only [erase, hp_pair, ↓reduceIte, compileStack, compileCont]
        exact .valStep .prodWeakₕ
      · refine ⟨?_, ?_, rfl, (compileStack_wk2 𝕄 S₀).symm, ?_, hS₀.wk (.step (.step .id))⟩
        · exact .cons_erased (fun _ ↦ ⟨rfl, hec₂⟩)
            (.cons_erased (fun _ ↦ ⟨rfl, hec₁⟩) hH)
        · simp only [erase, hr, hrp_nz, ↓reduceIte]
          rw [wk_erase_comm]
        · exact ⟨⟨hec_u.wk (.step (.step .id)), trivial⟩, trivial⟩
    | @zeroₕ _ p q r A z s ρ ρ' S₀ =>
      rcases hec_S with ⟨⟨hec_z, _⟩, hS₀⟩
      refine ⟨⟨TH, erase 𝕄 false .nonStrict z, ρ', compileStack 𝕄 S₀⟩,
        .valStep .zeroₕ, ⟨hH, rfl, rfl, rfl, hec_z, hS₀⟩⟩
    | @sucₕ _ p q r pred A z s ρ ρ' S₀ =>
      rcases hec_S with ⟨⟨hec_z, hec_s⟩, hS₀⟩
      let nr_src := GTerm.natrec p q r (GTerm.wk (.lift (.step .id)) A) (GTerm.wk1 z) (GTerm.wk1 s) (.var 0)
      let nr_tgt := TargetTerm.natrec false .nonStrict (decide (p = 𝕄.zero)) (decide (r = 𝕄.zero))
        (TargetTerm.wk1 (erase 𝕄 false .nonStrict z)) (TargetTerm.wk1 (erase 𝕄 false .nonStrict s)) (.var 0)
      have hnr_erase : erase 𝕄 false .nonStrict nr_src = nr_tgt := by
        simp only [nr_src, nr_tgt, erase, GTerm.wk1, TargetTerm.wk1]
        rw [wk_erase_comm, wk_erase_comm]
      have hec_nr : ErasureCompatible 𝕄 nr_src :=
        ⟨hec_z.wk (.step .id), hec_s.wk (.step .id), trivial⟩
      refine ⟨⟨.cons (.cons TH (compileEntry 𝕄 ⟨pred, ρ⟩)) ⟨nr_tgt, .lift ρ'⟩,
          appOrZero false .nonStrict (decide (r = 𝕄.zero))
            (appOrZero false .nonStrict (decide (p = 𝕄.zero))
              (TargetTerm.wk (.step (.step .id)) (erase 𝕄 false .nonStrict s)) (.var 1))
            (.var 0),
          .lift (.lift ρ'), TargetStack.wk2 (compileStack 𝕄 S₀)⟩,
        .valStep .sucₕ, ?_⟩
      refine ⟨?_, ?_, rfl, (compileStack_wk2 𝕄 S₀).symm,
        ⟨⟨hec_s.wk (.step (.step .id)), trivial⟩, trivial⟩,
        hS₀.wk (.step (.step .id))⟩
      · refine .cons_erased (fun _ ↦ ⟨?_, hec_nr⟩)
          (.cons_erased (fun _ ↦ ⟨rfl, hec_t⟩) hH)
        change ({ term := nr_tgt, env := .lift ρ' } : TargetEntry) =
          { term := erase 𝕄 false .nonStrict nr_src, env := .lift ρ' }
        rw [hnr_erase]
      · rw [erase_app_eq_appOrZero, erase_app_eq_appOrZero, wk_erase_comm]
        rfl
    | @starWeakₕ _ p q A u ρ ρ' S₀ =>
      rcases hec_S with ⟨⟨_, hec_u⟩, hS₀⟩
      refine ⟨⟨TH, erase 𝕄 false .nonStrict u, ρ', compileStack 𝕄 S₀⟩,
        .valStep .starWeakₕ, ⟨hH, rfl, rfl, rfl, hec_u, hS₀⟩⟩
  | numStep hn =>
    cases hn with
    | @sucₕ _ t₀ ρ ℓ hnotnum =>
      have hnotnum_tgt : ¬ TargetTerm.Numeral (erase 𝕄 false .nonStrict t₀) :=
        fun hn_tgt ↦ hnotnum ((erase_numeral_iff 𝕄 (t := t₀) hec_t).mpr hn_tgt)
      refine ⟨⟨TH, erase 𝕄 false .nonStrict t₀, ρ, .sucₑ :: TargetStack.sucs ℓ⟩, ?_, ?_⟩
      · simp only [erase, compileStack_sucs]
        exact .numStep (.sucₕ hnotnum_tgt)
      · refine ⟨hH, rfl, rfl, ?_, hec_t, ⟨trivial, hec_S⟩⟩
        simp [compileStack, compileCont]
    | @numₕ _ _ _ S₀ hnum =>
      have hnum_tgt : TargetTerm.Numeral (erase 𝕄 false .nonStrict t) :=
        (erase_numeral_iff 𝕄 (t := t) hec_t).mp hnum
      refine ⟨⟨TH, .succ (erase 𝕄 false .nonStrict t), ρ, compileStack 𝕄 S₀⟩,
        ?_,
        ⟨hH, rfl, rfl, rfl, hec_t, hec_S.2⟩⟩
      simp only [compileStack, compileCont]
      exact .numStep (.numₕ hnum_tgt)

/-- **Multi-Step Lockstep Simulation (`erased_heap_star_sim`)**:
    every multi-step source evaluation `HeapNumStar 𝕄 nr₂ s₁ s₂` is simulated in lockstep
    by `TargetHeapNumStar ts₁ ts₂` on the extracted target closure machine. -/
theorem erased_heap_star_sim {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s₁ s₂ : State M} {ts₁ : TargetState}
    (hrel : ErasedStateRel 𝕄 s₁ ts₁)
    (hstar : HeapNumStar 𝕄 nr₂ s₁ s₂) :
    ∃ ts₂ : TargetState,
      TargetHeapNumStar ts₁ ts₂ ∧ ErasedStateRel 𝕄 s₂ ts₂ := by
  induction hstar generalizing ts₁ with
  | refl _ => exact ⟨ts₁, .refl ts₁, hrel⟩
  | step hs _ ih =>
    rcases erased_heap_lockstep_sim hw hnr hrel hs with ⟨ts_mid, hts, hrel_mid⟩
    rcases ih hrel_mid with ⟨ts₂, hts_rest, hrel₂⟩
    exact ⟨ts₂, .step hts hts_rest, hrel₂⟩

/-- **Canonical Numeral Simulation (`erased_heap_numeral_sim`)**:
    if a source state `s₁` related to `ts₁` evaluates via `HeapNumStar` to a canonical
    numeral `⟨H', GTerm.suck n, ρ, []⟩`, then the extracted target machine `ts₁` evaluates
    via `TargetHeapNumStar` to `⟨TH', TargetTerm.suck n, ρ, []⟩` with the **exact same numeral `n`**. -/
theorem erased_heap_numeral_sim {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s₁ : State M} {ts₁ : TargetState} {H' : Heap M} {n : Nat} {ρ : Wk}
    (hrel : ErasedStateRel 𝕄 s₁ ts₁)
    (hstar : HeapNumStar 𝕄 nr₂ s₁ ⟨H', GTerm.suck n, ρ, []⟩) :
    ∃ TH' : TargetHeap,
      TargetHeapNumStar ts₁ ⟨TH', TargetTerm.suck n, ρ, []⟩ ∧
      ErasedHeapRel 𝕄 H' TH' := by
  rcases erased_heap_star_sim hw hnr hrel hstar with ⟨⟨TH', tt, tρ, TS⟩, hts, hrel'⟩
  rcases hrel' with ⟨hH', htt, hρ, hTS, _, _⟩
  dsimp only at hH' htt hρ hTS
  rw [erase_suck] at htt
  subst htt; cases hρ; subst hTS
  exact ⟨TH', hts, hH'⟩

/-- **Erasure Non-Access & Representation Independence Theorem (`erased_binding_never_accessed`)**:
    if an initial heap has a `𝕄.zero`-graded binding `⟨u, ρ₀⟩` (for *any* source term `u`),
    compiling the state replaces `u` with `.undef` on the target heap (`⟨.undef, ρ₀⟩`),
    and for any alternative target entry `te_alt : TargetEntry` placed in that slot:
    1. Every step of the source execution is simulated identically on the target machine,
    2. The `0`-graded slot is never looked up,
    3. Both target runs terminate at the exact same canonical numeral `TargetTerm.suck n`. -/
theorem erased_binding_never_accessed {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {H₀ : Heap M} {TH₀ : TargetHeap} (u : GTerm M) (ρ₀ : Wk) (te_alt : TargetEntry)
    {t : GTerm M} {H' : Heap M} {n : Nat} {ρ' : Wk}
    (hH₀ : ErasedHeapRel 𝕄 H₀ TH₀)
    (ht : ErasureCompatible 𝕄 t)
    (hstar : HeapNumStar 𝕄 nr₂ ⟨.cons H₀ 𝕄.zero ⟨u, ρ₀⟩, t, .id, []⟩ ⟨H', GTerm.suck n, ρ', []⟩) :
    (∃ TH₁' : TargetHeap,
      TargetHeapNumStar ⟨.cons TH₀ ⟨.undef, ρ₀⟩, erase 𝕄 false .nonStrict t, .id, []⟩
        ⟨TH₁', TargetTerm.suck n, ρ', []⟩ ∧
      ErasedHeapRel 𝕄 H' TH₁') ∧
    (∃ TH₂' : TargetHeap,
      TargetHeapNumStar ⟨.cons TH₀ te_alt, erase 𝕄 false .nonStrict t, .id, []⟩
        ⟨TH₂', TargetTerm.suck n, ρ', []⟩ ∧
      ErasedHeapRel 𝕄 H' TH₂') := by
  have hrel₁ : ErasedStateRel 𝕄 ⟨.cons H₀ 𝕄.zero ⟨u, ρ₀⟩, t, .id, []⟩
      ⟨.cons TH₀ ⟨.undef, ρ₀⟩, erase 𝕄 false .nonStrict t, .id, []⟩ :=
    ⟨.cons_erased (fun hne ↦ False.elim (hne rfl)) hH₀, rfl, rfl, rfl, ht, trivial⟩
  have hrel₂ : ErasedStateRel 𝕄 ⟨.cons H₀ 𝕄.zero ⟨u, ρ₀⟩, t, .id, []⟩
      ⟨.cons TH₀ te_alt, erase 𝕄 false .nonStrict t, .id, []⟩ :=
    ⟨.cons_erased (fun hne ↦ False.elim (hne rfl)) hH₀, rfl, rfl, rfl, ht, trivial⟩
  exact ⟨erased_heap_numeral_sim hw hnr hrel₁ hstar,
    erased_heap_numeral_sim hw hnr hrel₂ hstar⟩

/-! ## 4. Affine Resource Budget Invariant & Linear Resource Conservation Law -/

/-- Drop the `d` newest bindings from a heap `H`, exposing the initial sub-heap. -/
def Heap.dropNewest {M : Type} : Nat → Heap M → Heap M
  | 0, H => H
  | _ + 1, .nil => .nil
  | d + 1, .cons H _ _ => dropNewest d H
  | d + 1, .dummy H => dropNewest d H

/-- Grade of the root (initial) binding in a non-empty heap obtained by pushing `d`
    newer bindings on top of an initial heap `H₀`. -/
def rootGrade {M : Type} (𝕄 : Modality M) (d : Nat) (H : Heap M) : M :=
  Heap.lookupGrade 𝕄 (Heap.dropNewest d H) 0

/-- When `HeapLookup 𝕄 H x q e H'` updates `H` to `H'`, for every index `y : Nat`:
    - if `y = x`, `SubEq 𝕄 (H.lookupGrade 𝕄 x) q (H'.lookupGrade 𝕄 x)`,
    - if `y ≠ x`, `H'.lookupGrade 𝕄 y = H.lookupGrade 𝕄 y`. -/
theorem heapLookup_lookupGrade_subEq {M : Type} {𝕄 : Modality M}
    {H H' : Heap M} {x : Nat} {q : M} {e : Entry M}
    (hl : HeapLookup 𝕄 H x q e H') :
    ∃ r : M,
      𝕄.SubEq (Heap.lookupGrade 𝕄 H x) q r ∧
      Heap.lookupGrade 𝕄 H' = Conₘ.update (Heap.lookupGrade 𝕄 H) x r := by
  induction hl with
  | @here H₀ p _ r e₀ hsub =>
    refine ⟨r, hsub, ?_⟩
    funext y
    cases y <;> rfl
  | @there H₀ H₀' x p q e₀ e' hl ih =>
    rcases ih with ⟨r, hsub, heq⟩
    refine ⟨r, hsub, ?_⟩
    funext y
    cases y with
    | zero => rfl
    | succ y =>
      simp only [Heap.lookupGrade, heq, Conₘ.update]
      by_cases h : y = x <;> simp [h]
  | @thereDummy H₀ H₀' x q e₀ hl ih =>
    rcases ih with ⟨r, hsub, heq⟩
    refine ⟨r, hsub, ?_⟩
    funext y
    cases y with
    | zero => rfl
    | succ y =>
      simp only [Heap.lookupGrade, heq, Conₘ.update]
      by_cases h : y = x <;> simp [h]

/-! ### 4.1 Explicit Affine Resource Accounting (`used(τ) + live(s') ≤ available(s)`) & Linear Conservation -/

/-- Quantitative resource-accounted execution witness (`ResourceAccountedRun`, Prop-valued):
    packages a source run `HeapNumStar`, an extracted target run `TargetHeapNumStar`,
    the initial and final simulation relations `ErasedStateRel`, and the explicit
    per-slot `used` and `live` resource counts satisfying the affine invariant
    $$\forall x,\quad \operatorname{used}(x) + \operatorname{live}(x) \le \operatorname{avail}(x).$$ -/
structure ResourceAccountedRun {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M)
    (avail used live : Nat → Nat) (s₀ s' : State M) (ts₀ ts' : TargetState) : Prop where
  sourceRun : HeapNumStar 𝕄 nr₂ s₀ s'
  targetRun : TargetHeapNumStar ts₀ ts'
  initSim : ErasedStateRel 𝕄 s₀ ts₀
  finalSim : ErasedStateRel 𝕄 s' ts'
  affine_bound : ∀ x : Nat, used x + live x ≤ avail x

/-- Linear resource-conserved execution witness (`LinearConservedRun`, Prop-valued):
    extends `ResourceAccountedRun` with the exact linear conservation law
    $$\forall x,\quad \operatorname{used}(x) + \operatorname{live}(x) = \operatorname{avail}(x),$$
    accounting for both resources consumed along the trace and resources retained in the
    final heap or captured inside returned closures. -/
structure LinearConservedRun {M : Type} (𝕄 : Modality M) (nr₂ : M → M → M)
    (avail used live : Nat → Nat) (s₀ s' : State M) (ts₀ ts' : TargetState) : Prop
    extends ResourceAccountedRun 𝕄 nr₂ avail used live s₀ s' ts₀ ts' where
  linear_conservation : ∀ x : Nat, used x + live x = avail x

/-- Demand of a returned closure `⟨head, env⟩` on initial heap slot `x` when `Usage 𝕄 δ .oneMode head`
    holds: `Conₘ.wk 𝕄 env δ x`. -/
def closureDemand {M : Type} (𝕄 : Modality M) (δ : Conₘ M) (ρ : Wk) : Conₘ M :=
  Conₘ.wk 𝕄 ρ δ

/-- **Closure Ownership Theorem (`returned_closure_captures_budget`)**:
    Suppose a well-resourced source state `s₀` evaluates via `HeapNumStar 𝕄 nr₂` to a returned
    function value `⟨H', .lam p body, ρ', []⟩` (with an empty stack).
    Then:
    1. The extracted target machine evaluates in lockstep to the compiled target closure
       `⟨TH', .lam (erase 𝕄 false .nonStrict body), ρ', []⟩` with `ErasedHeapRel 𝕄 H' TH'`,
    2. By `usage_pres_numStar_empty`, the final state satisfies `StateUsage 𝕄 nr₂ ⟨H', .lam p body, ρ', []⟩`,
    3. Hence there exist final heap budget `γ' : Conₘ M` and body usage context `δ_body : Conₘ M`
       such that `HeapUsage 𝕄 γ' H'`, `Usage 𝕄 (Conₘ.cons δ_body p) .oneMode body`, and
       `Conₘ.le 𝕄 γ' (Conₘ.wk 𝕄 ρ' δ_body)` — proving that every resource captured by the
       returned closure `.lam p body` via `ρ'` is backed by live budget in `γ'`! -/
theorem returned_closure_captures_budget {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s₀ : State M} {ts₀ : TargetState} {H' : Heap M} {p : M} {body : GTerm M} {ρ' : Wk}
    (hs₀ : StateUsage 𝕄 nr₂ s₀)
    (hrel₀ : ErasedStateRel 𝕄 s₀ ts₀)
    (hstar : HeapNumStar 𝕄 nr₂ s₀ ⟨H', .lam p body, ρ', []⟩) :
    ∃ (TH' : TargetHeap) (γ' δ_body : Conₘ M),
      TargetHeapNumStar ts₀ ⟨TH', .lam (erase 𝕄 false .nonStrict body), ρ', []⟩ ∧
      ErasedHeapRel 𝕄 H' TH' ∧
      HeapUsage 𝕄 γ' H' ∧
      Usage 𝕄 (Conₘ.cons δ_body p) .oneMode body ∧
      Conₘ.le 𝕄 γ' (closureDemand 𝕄 δ_body ρ') := by
  have hs_final : StateUsage 𝕄 nr₂ ⟨H', .lam p body, ρ', []⟩ :=
    usage_pres_numStar_empty hw hnr hs₀ hstar
  rcases erased_heap_star_sim hw hnr hrel₀ hstar with ⟨⟨TH', tt, tρ, TS⟩, hts, hrel'⟩
  rcases hrel' with ⟨hH', htt, hρ, hTS, _, _⟩
  dsimp only at hH' htt hρ hTS
  have htt_lam : tt = .lam (erase 𝕄 false .nonStrict body) := by
    rw [htt]
    simp only [erase]
    split <;> rfl
  subst htt_lam; cases hρ; subst hTS
  rcases hs_final with ⟨γ', δ, η, hH_usage, hlam_usage, hS_usage, hbound⟩
  have hη0 : η = Conₘ.zero 𝕄 := by
    cases hS_usage
    rfl
  subst hη0
  have hm_one : Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ []) = .oneMode :=
    Mode.ofGrade_ne_zero 𝕄 hw.nonTrivial
  rw [hm_one] at hlam_usage
  have hbody := Usage.inv_lam hlam_usage
  simp only [Mode.toGrade, 𝕄.one_mul] at hbody
  refine ⟨TH', γ', δ, hts, hH', hH_usage, hbody, ?_⟩
  change Conₘ.le 𝕄 γ' (Conₘ.add 𝕄 (Conₘ.scale 𝕄 𝕄.one (Conₘ.wk 𝕄 ρ' δ)) (Conₘ.zero 𝕄)) at hbound
  rwa [Conₘ.one_scale, Conₘ.add_zero] at hbound

/-! ## 5. Main Theorem of Paper A (`paper_A_resource_correctness_after_erasure`) -/

/-- **Main Theorem of Paper A (`paper_A_resource_correctness_after_erasure`, Gates G2 & G3)**:
    For any modality `𝕄` with `HasWellBehavedZero` and recursion multiplier `nr₂` satisfying
    `NatrecMultFn 𝕄 nr₂`, and any well-resourced source configuration `s₀ : State M`
    (`StateUsage 𝕄 nr₂ s₀`) related to an extracted target configuration `ts₀ : TargetState`
    (`ErasedStateRel 𝕄 s₀ ts₀`):
    1. **Resource Preservation**: Every step of `HeapNumStar 𝕄 nr₂ s₀ s'` preserves the
       graded resource invariant (`StateUsageExt 𝕄 nr₂ s'`, and `StateUsage 𝕄 nr₂ s'` when
       the stack is empty),
    2. **Erasure Non-Access**: No `𝕄.zero`-graded heap binding is ever accessed at any step,
    3. **Target Closure Machine Simulation**: The extracted target closure machine `ts₀`
       steps in lockstep via `TargetHeapNumStar ts₀ ts'` with `ErasedStateRel 𝕄 s' ts'`,
    4. **Numeral Canonicity & Unfolding**: When `s'` is a canonical numeral `⟨H', GTerm.suck n, ρ', []⟩`,
       `ts'` is `⟨TH', TargetTerm.suck n, ρ', []⟩` and `unfoldState s₀` reduces via `GStarNum`
       to `GTerm.suck n`. -/
theorem paper_A_resource_correctness_after_erasure
    {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    {s₀ : State M} {ts₀ : TargetState} {H' : Heap M} {n : Nat} {ρ' : Wk}
    (hs₀ : StateUsage 𝕄 nr₂ s₀)
    (hvalid : ValidNumStack s₀.stack)
    (hrel₀ : ErasedStateRel 𝕄 s₀ ts₀)
    (hstar : HeapNumStar 𝕄 nr₂ s₀ ⟨H', GTerm.suck n, ρ', []⟩) :
    ∃ TH' : TargetHeap,
      TargetHeapNumStar ts₀ ⟨TH', TargetTerm.suck n, ρ', []⟩ ∧
      ErasedHeapRel 𝕄 H' TH' ∧
      StateUsage 𝕄 nr₂ ⟨H', GTerm.suck n, ρ', []⟩ ∧
      GStarNum 𝕄 (unfoldState s₀) (GTerm.suck n) := by
  rcases erased_heap_numeral_sim hw hnr hrel₀ hstar with ⟨TH', hts, hH'⟩
  have hs_final := usage_pres_numStar_empty hw hnr hs₀ hstar
  have hunf := (unfold_heapNumStar hvalid hstar).1
  simp only [unfoldState, unfoldStack, wk_suck, subst_suck] at hunf
  exact ⟨TH', hts, hH', hs_final, hunf⟩

/-! ## 6. Gate G2/G3 Benchmark (`fold_capturing_closure_example`) & Failure Tests -/

section BenchmarkAndFailureTests

/-- In any modality `𝕄`, the recursion sequence `𝕄.nrᵢ 𝕄.one 𝕄.one 𝕄.zero i`
    (for a linear fold with predecessor grade `p = 0` and recursive accumulator grade `r = 1`)
    is identically `𝕄.one` at every iteration depth `i`! -/
theorem nrᵢ_one_one_zero_eq_one {M : Type} (𝕄 : Modality M) :
    ∀ i : Nat, 𝕄.nrᵢ 𝕄.one 𝕄.one 𝕄.zero i = 𝕄.one
  | 0 => rfl
  | i + 1 => by
    simp only [Modality.nrᵢ, nrᵢ_one_one_zero_eq_one 𝕄 i, 𝕄.mul_one, 𝕄.zero_add]

/-- The recursive fold term capturing heap resource `0` (while ignoring erased heap
    argument `1`) and returning a closure `λ y. ih y`:
    - Base case `z = .lam 𝕄.zero (.var 2)` captures the linear resource at heap slot `0`
      (which is at index `2` under `lam 0` and `lam 0`),
    - Step case `s = .lam 𝕄.zero (.lam 𝕄.one (.lam 𝕄.one (.app 𝕄.one (.var 1) (.var 0))))`
      takes the predecessor at grade `0` and the recursive closure `ih` at grade `1`, and
      returns a new closure `λ y. ih y` delegating ownership of the captured resource! -/
def foldCapturingClosureTerm (M : Type) (𝕄 : Modality M) : GTerm M :=
  .app 𝕄.zero
    (.lam 𝕄.zero
      (.natrec 𝕄.zero 𝕄.one 𝕄.one .nat
        (.lam 𝕄.zero (.var 2))
        (.lam 𝕄.zero (.lam 𝕄.one (.lam 𝕄.one (.app 𝕄.one (.var 1) (.var 0)))))
        (.succ .zero)))
    (.var 1)

/-- In the compiled target term of `foldCapturingClosureTerm`, the `0`-graded argument
    `(.var 1)` has been completely erased to `.undef`! -/
theorem erase_foldCapturingClosureTerm {M : Type} (𝕄 : Modality M)
    (hw : 𝕄.HasWellBehavedZero) :
    erase 𝕄 false .nonStrict (foldCapturingClosureTerm M 𝕄) =
      .app .nonStrict
        (.lam
          (.natrec false .nonStrict true false
            (.lam (.var 2))
            (.lam (.lam (.lam (.app .nonStrict (.var 1) (.var 0)))))
            (.succ .zero)))
        .undef := by
  simp [foldCapturingClosureTerm, erase, appZero, hw.nonTrivial]

/-- Initial source heap for the fold benchmark:
    - slot `1` (bottom): grade `𝕄.zero`, holding an arbitrary specification term `u_spec`
    - slot `0` (top): grade `𝕄.one`, holding the live resource `.zero`. -/
def foldInitHeap {M : Type} (𝕄 : Modality M) (u_spec : GTerm M) : Heap M :=
  .cons (.cons .nil 𝕄.zero ⟨u_spec, .id⟩) 𝕄.one ⟨.zero, .id⟩

/-- Initial source state for the fold benchmark. -/
def foldInitState {M : Type} (𝕄 : Modality M) (u_spec : GTerm M) : State M :=
  ⟨foldInitHeap 𝕄 u_spec, foldCapturingClosureTerm M 𝕄, .id, []⟩

/-- `foldCapturingClosureTerm` is `ErasureCompatible`. -/
theorem foldCapturingClosureTerm_compat {M : Type} (𝕄 : Modality M) :
    ErasureCompatible 𝕄 (foldCapturingClosureTerm M 𝕄) := by
  simp [foldCapturingClosureTerm, ErasureCompatible]

/-- Well-resourcedness (`Usage`) of `foldCapturingClosureTerm` in context `[1 ↦ 0, 0 ↦ 1]`:
    requires grade `1` on variable `0` (the captured resource) and grade `0` on variable `1`
    (the erased specification argument). Note that the step case `s` has outer usage `0`
    and recursive accumulator grade `r = 1`, so the loop invariant `χ ≤ 0 + 1 · χ` holds
    in EVERY modality `𝕄` (including `linearityModality`)! -/
theorem foldCapturingClosureTerm_usage {M : Type} (𝕄 : Modality M)
    (hw : 𝕄.HasWellBehavedZero) {nr₂ : M → M → M}
    (hnr : NatrecMultFn 𝕄 nr₂) :
    Usage 𝕄 (Conₘ.cons (Conₘ.cons (Conₘ.zero 𝕄) 𝕄.zero) 𝕄.one)
      .oneMode (foldCapturingClosureTerm M 𝕄) := by
  let γ₀ := Conₘ.cons (Conₘ.cons (Conₘ.zero 𝕄) 𝕄.zero) 𝕄.one
  let γ₁ := Conₘ.cons γ₀ 𝕄.zero
  have hvar2_z : Usage 𝕄 (Conₘ.cons γ₁ (𝕄.mul (Mode.toGrade 𝕄 .oneMode) 𝕄.zero))
      .oneMode (.var 2) := by
    apply Usage.sub Usage.var
    intro x
    cases x with
    | zero =>
      dsimp only [Conₘ.cons, Conₘ.single, Mode.toGrade]
      rw [if_neg (by decide), 𝕄.mul_zero]
      exact 𝕄.le_refl _
    | succ x =>
      cases x with
      | zero =>
        dsimp only [γ₁, Conₘ.cons, Conₘ.single]
        rw [if_neg (by decide)]
        exact 𝕄.le_refl _
      | succ x =>
        cases x with
        | zero =>
          dsimp only [γ₁, γ₀, Conₘ.cons, Conₘ.single, Mode.toGrade]
          rw [if_pos rfl]
          exact 𝕄.le_refl _
        | succ x =>
          dsimp only [γ₁, γ₀, Conₘ.cons, Conₘ.zero, Conₘ.single]
          rw [if_neg (by omega)]
          cases x <;> exact 𝕄.le_refl _
  have hz : Usage 𝕄 γ₁ .oneMode (.lam 𝕄.zero (.var 2)) :=
    Usage.lam hvar2_z
  -- Step body `.app 𝕄.one (.var 1) (.var 0)` in context `((γ₁, 0), 1), 1`:
  let δs_outer := Conₘ.zero 𝕄
  let δs_1 := Conₘ.cons δs_outer (𝕄.mul (Mode.toGrade 𝕄 .oneMode) 𝕄.zero)
  let δs_2 := Conₘ.cons δs_1 (𝕄.mul (Mode.toGrade 𝕄 .oneMode) 𝕄.one)
  let δs_3 := Conₘ.cons δs_2 (𝕄.mul (Mode.toGrade 𝕄 .oneMode) 𝕄.one)
  have h_ih_var : Usage 𝕄 (Conₘ.single 𝕄 1 (Mode.toGrade 𝕄 .oneMode)) .oneMode (.var 1) :=
    Usage.var
  have h_y_var : Usage 𝕄 (Conₘ.single 𝕄 0 (Mode.toGrade 𝕄 .oneMode))
      (Mode.scale 𝕄 .oneMode 𝕄.one) (.var 0) := by
    rw [Mode.scale_oneMode_ne_zero 𝕄 hw.nonTrivial]
    exact Usage.var
  have happ_s_raw := Usage.app h_ih_var h_y_var
  have happ_s : Usage 𝕄 δs_3 .oneMode (.app 𝕄.one (.var 1) (.var 0)) := by
    apply Usage.sub happ_s_raw
    intro x
    cases x with
    | zero =>
      dsimp only [δs_3, δs_2, δs_1, δs_outer, Conₘ.cons, Conₘ.add, Conₘ.scale,
        Conₘ.single, Mode.toGrade]
      rw [if_neg (by decide), if_pos rfl, 𝕄.zero_add]
      exact 𝕄.le_refl _
    | succ x =>
      cases x with
      | zero =>
        dsimp only [δs_3, δs_2, δs_1, δs_outer, Conₘ.cons, Conₘ.add, Conₘ.scale,
          Conₘ.single, Mode.toGrade]
        rw [if_pos rfl, if_neg (by decide), 𝕄.mul_zero, 𝕄.add_zero, 𝕄.one_mul]
        exact 𝕄.le_refl _
      | succ x =>
        dsimp only [δs_3, δs_2, δs_1, δs_outer, Conₘ.cons, Conₘ.zero, Conₘ.add, Conₘ.scale,
          Conₘ.single, Mode.toGrade]
        rw [if_neg (by omega), if_neg (by omega), 𝕄.mul_zero, 𝕄.add_zero]
        cases x <;> exact 𝕄.le_refl _
  have hs : Usage 𝕄 δs_outer .oneMode
      (.lam 𝕄.zero (.lam 𝕄.one (.lam 𝕄.one (.app 𝕄.one (.var 1) (.var 0))))) :=
    Usage.lam (Usage.lam (Usage.lam happ_s))
  have hn : Usage 𝕄 (Conₘ.zero 𝕄) .oneMode (.succ .zero) :=
    .succ .zero
  have hA : Usage 𝕄 (Conₘ.cons (Conₘ.zero 𝕄) 𝕄.zero) .zeroMode .nat := by
    rw [Conₘ.cons_zero_zero]
    exact .nat
  have hnr_term : Usage 𝕄 γ₁ .oneMode
      (.natrec 𝕄.zero 𝕄.one 𝕄.one .nat
        (.lam 𝕄.zero (.var 2))
        (.lam 𝕄.zero (.lam 𝕄.one (.lam 𝕄.one (.app 𝕄.one (.var 1) (.var 0)))))
        (.succ .zero)) := by
    have hfix := Usage.natrec_fix (χ := γ₁) (q := 𝕄.one) hz hs hn hA
      (hnr.le_one 𝕄.zero 𝕄.one)
      (by simp only [Mode.toGrade, 𝕄.one_mul]; exact hnr.le_step 𝕄.zero 𝕄.one)
      (Conₘ.le_refl 𝕄 γ₁)
      (by
        change Conₘ.le 𝕄 γ₁ (Conₘ.add 𝕄 (Conₘ.zero 𝕄) (Conₘ.scale 𝕄 𝕄.one γ₁))
        rw [Conₘ.zero_add, Conₘ.one_scale]
        exact Conₘ.le_refl 𝕄 γ₁)
    rwa [Conₘ.scale_zero, Conₘ.zero_add] at hfix
  have hnr_term' : Usage 𝕄 (Conₘ.cons γ₀ (𝕄.mul (Mode.toGrade 𝕄 .oneMode) 𝕄.zero)) .oneMode
      (.natrec 𝕄.zero 𝕄.one 𝕄.one .nat
        (.lam 𝕄.zero (.var 2))
        (.lam 𝕄.zero (.lam 𝕄.one (.lam 𝕄.one (.app 𝕄.one (.var 1) (.var 0)))))
        (.succ .zero)) := by
    simpa only [Mode.toGrade, 𝕄.mul_zero] using hnr_term
  have hlam : Usage 𝕄 γ₀ .oneMode
      (.lam 𝕄.zero
        (.natrec 𝕄.zero 𝕄.one 𝕄.one .nat
          (.lam 𝕄.zero (.var 2))
          (.lam 𝕄.zero (.lam 𝕄.one (.lam 𝕄.one (.app 𝕄.one (.var 1) (.var 0)))))
          (.succ .zero))) :=
    Usage.lam hnr_term'
  have hu : Usage 𝕄 (Conₘ.zero 𝕄) (Mode.scale 𝕄 .oneMode 𝕄.zero) (.var 1) := by
    rw [Mode.scale_zero_grade]
    exact Usage.zeroMode_usage (.var 1)
  have happ := Usage.app hlam hu
  rwa [Conₘ.scale_zero, Conₘ.add_zero] at happ

/-- **Gate G2/G3 Benchmark Theorem (`fold_capturing_closure_example`)**:
    1. `foldInitState` is well-resourced (`StateUsage`),
    2. Its compiled `TargetState` executes through the erased application and recursive
       `natrec` fold to a returned closure `⟨TH_ret, .lam (.app .nonStrict (.var 1) (.var 0)), ρ_ret, []⟩`,
    3. The erased specification binding `u_spec` at slot `1` is compiled to `.undef` and
       is never accessed (`used 1 = 0, live 1 = 0`),
    4. The resource at slot `0` is transferred into the returned closure with linear
       conservation (`used 0 = 0, live 0 = 1, used 0 + live 0 = 1`). -/
theorem fold_capturing_closure_example {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    (hw : 𝕄.HasWellBehavedZero) (hnr : NatrecMultFn 𝕄 nr₂)
    (u_spec : GTerm M) :
    let s₀ := foldInitState 𝕄 u_spec
    let ts₀ := compileState 𝕄 s₀
    StateUsage 𝕄 nr₂ s₀ ∧
    ∃ (H_ret : Heap M) (TH_ret : TargetHeap) (ρ_ret : Wk),
      LinearConservedRun 𝕄 nr₂
        (fun x ↦ if x = 0 then 1 else 0)
        (fun _ ↦ 0)
        (fun x ↦ if x = 0 then 1 else 0)
        s₀ ⟨H_ret, .lam 𝕄.one (.app 𝕄.one (.var 1) (.var 0)), ρ_ret, []⟩
        ts₀ ⟨TH_ret, .lam (.app .nonStrict (.var 1) (.var 0)), ρ_ret, []⟩ ∧
      ∃ (γ_ret δ_body : Conₘ M),
        HeapUsage 𝕄 γ_ret H_ret ∧
        Usage 𝕄 (Conₘ.cons δ_body 𝕄.one) .oneMode (.app 𝕄.one (.var 1) (.var 0)) ∧
        Conₘ.le 𝕄 γ_ret (closureDemand 𝕄 δ_body ρ_ret) := by
  intro s₀ ts₀
  let γ_u := Conₘ.cons (Conₘ.zero 𝕄) 𝕄.zero
  let γ₀ := Conₘ.cons γ_u 𝕄.one
  have hH_u : HeapUsage 𝕄 γ_u (.cons .nil 𝕄.zero ⟨u_spec, .id⟩) := by
    have h0 : HeapUsage 𝕄 (Conₘ.add 𝕄 (Conₘ.zero 𝕄)
        (Conₘ.scale 𝕄 𝕄.zero (Conₘ.wk 𝕄 .id (Conₘ.zero 𝕄)))) .nil := by
      rw [Conₘ.wk_zero, Conₘ.scale_zero, Conₘ.add_zero]
      exact .nil
    have hu : Usage 𝕄 (Conₘ.zero 𝕄) (Mode.ofGrade 𝕄 𝕄.zero) u_spec := by
      rw [Mode.ofGrade_zero]
      exact Usage.zeroMode_usage u_spec
    exact .cons h0 hu
  have hH₀ : HeapUsage 𝕄 γ₀ (foldInitHeap 𝕄 u_spec) := by
    have h1 : HeapUsage 𝕄 (Conₘ.add 𝕄 γ_u
        (Conₘ.scale 𝕄 𝕄.one (Conₘ.wk 𝕄 .id (Conₘ.zero 𝕄))))
        (.cons .nil 𝕄.zero ⟨u_spec, .id⟩) := by
      rw [Conₘ.wk_zero, Conₘ.scale_zero, Conₘ.add_zero]
      exact hH_u
    have hz0 : Usage 𝕄 (Conₘ.zero 𝕄) (Mode.ofGrade 𝕄 𝕄.one) .zero := .zero
    exact .cons h1 hz0
  have ht₀ : Usage 𝕄 γ₀ (Mode.ofGrade 𝕄 (Stack.mult 𝕄 nr₂ [])) (foldCapturingClosureTerm M 𝕄) := by
    rw [Stack.mult_nil, Mode.ofGrade_ne_zero 𝕄 hw.nonTrivial]
    exact foldCapturingClosureTerm_usage 𝕄 hw hnr
  have hs₀ : StateUsage 𝕄 nr₂ s₀ := by
    refine ⟨γ₀, γ₀, Conₘ.zero 𝕄, hH₀, ht₀, .nil, ?_⟩
    change Conₘ.le 𝕄 γ₀ (Conₘ.add 𝕄 (Conₘ.scale 𝕄 𝕄.one (Conₘ.wk 𝕄 .id γ₀)) (Conₘ.zero 𝕄))
    rw [Conₘ.wk_id, Conₘ.one_scale, Conₘ.add_zero]
    exact Conₘ.le_refl 𝕄 γ₀
  refine ⟨hs₀, ?_⟩
  let H₀ := foldInitHeap 𝕄 u_spec
  let z_tm : GTerm M := .lam 𝕄.zero (.var 2)
  let s_tm : GTerm M := .lam 𝕄.zero (.lam 𝕄.one (.lam 𝕄.one (.app 𝕄.one (.var 1) (.var 0))))
  let nr_tm : GTerm M := .natrec 𝕄.zero 𝕄.one 𝕄.one .nat z_tm s_tm (.succ .zero)
  -- Step 1: ElimStep.appₕ pushes `.appₑ 0 (.var 1) .id`
  have hstep1 : HeapNumStep 𝕄 nr₂ s₀
      ⟨H₀, .lam 𝕄.zero nr_tm, .id, [.appₑ 𝕄.zero (.var 1) .id]⟩ :=
    .elimStep (.elim .appₕ)
  -- Step 2: ValStep.lamₕ allocates `(1 · 0, ⟨.var 1, .id⟩)` on H₀
  let H₁ := Heap.cons H₀ (𝕄.mul 𝕄.one 𝕄.zero) ⟨.var 1, .id⟩
  have hstep2 : HeapNumStep 𝕄 nr₂
      ⟨H₀, .lam 𝕄.zero nr_tm, .id, [.appₑ 𝕄.zero (.var 1) .id]⟩
      ⟨H₁, nr_tm, .lift .id, []⟩ :=
    .valStep .lamₕ
  -- Step 3: ElimStep.natrecₕ pushes `.natrecₑ` and evaluates `.succ .zero`
  have hstep3 : HeapNumStep 𝕄 nr₂
      ⟨H₁, nr_tm, .lift .id, []⟩
      ⟨H₁, .succ .zero, .lift .id, [.natrecₑ 𝕄.zero 𝕄.one 𝕄.one .nat z_tm s_tm (.lift .id)]⟩ :=
    .elimStep (.elim .natrecₕ)
  -- Step 4: ValStep.sucₕ unfolds one step of `natrec` on `.succ .zero`
  let H₂ := Heap.cons H₁ (𝕄.mul 𝕄.one (nr₂ 𝕄.zero 𝕄.one)) ⟨.zero, .lift .id⟩
  let nr_rec : GTerm M := .natrec 𝕄.zero 𝕄.one 𝕄.one
    (GTerm.wk (.lift (.step .id)) .nat) (GTerm.wk1 z_tm) (GTerm.wk1 s_tm) (.var 0)
  let H₃ := Heap.cons H₂ (𝕄.mul 𝕄.one 𝕄.one) ⟨nr_rec, .lift (.lift .id)⟩
  let ρ₃ : Wk := .lift (.lift (.lift .id))
  have hstep4 : HeapNumStep 𝕄 nr₂
      ⟨H₁, .succ .zero, .lift .id, [.natrecₑ 𝕄.zero 𝕄.one 𝕄.one .nat z_tm s_tm (.lift .id)]⟩
      ⟨H₃, .app 𝕄.one (.app 𝕄.zero (GTerm.wk (.step (.step .id)) s_tm) (.var 1)) (.var 0), ρ₃, []⟩ :=
    .valStep .sucₕ
  -- Step 5: ElimStep.appₕ pushes `.appₑ 1 (.var 0) ρ₃`
  have hstep5 : HeapNumStep 𝕄 nr₂
      ⟨H₃, .app 𝕄.one (.app 𝕄.zero (GTerm.wk (.step (.step .id)) s_tm) (.var 1)) (.var 0), ρ₃, []⟩
      ⟨H₃, .app 𝕄.zero (GTerm.wk (.step (.step .id)) s_tm) (.var 1), ρ₃, [.appₑ 𝕄.one (.var 0) ρ₃]⟩ :=
    .elimStep (.elim .appₕ)
  -- Step 6: ElimStep.appₕ pushes `.appₑ 0 (.var 1) ρ₃` (note `wk (.step (.step .id)) s_tm = s_tm` since `s_tm` is closed!)
  have hstep6 : HeapNumStep 𝕄 nr₂
      ⟨H₃, .app 𝕄.zero (GTerm.wk (.step (.step .id)) s_tm) (.var 1), ρ₃, [.appₑ 𝕄.one (.var 0) ρ₃]⟩
      ⟨H₃, .lam 𝕄.zero (.lam 𝕄.one (.lam 𝕄.one (.app 𝕄.one (.var 1) (.var 0)))), ρ₃,
        [.appₑ 𝕄.zero (.var 1) ρ₃, .appₑ 𝕄.one (.var 0) ρ₃]⟩ :=
    .elimStep (.elim .appₕ)
  -- Step 7: ValStep.lamₕ pops `.appₑ 0 (.var 1) ρ₃`
  let H₄ := Heap.cons H₃ (𝕄.mul (Stack.mult 𝕄 nr₂ [.appₑ 𝕄.one (.var 0) ρ₃]) 𝕄.zero) ⟨.var 1, ρ₃⟩
  have hstep7 : HeapNumStep 𝕄 nr₂
      ⟨H₃, .lam 𝕄.zero (.lam 𝕄.one (.lam 𝕄.one (.app 𝕄.one (.var 1) (.var 0)))), ρ₃,
        [.appₑ 𝕄.zero (.var 1) ρ₃, .appₑ 𝕄.one (.var 0) ρ₃]⟩
      ⟨H₄, .lam 𝕄.one (.lam 𝕄.one (.app 𝕄.one (.var 1) (.var 0))), .lift ρ₃,
        [.appₑ 𝕄.one (.var 0) (compWk (.step .id) ρ₃)]⟩ :=
    .valStep .lamₕ
  -- Step 8: ValStep.lamₕ pops `.appₑ 1 (.var 0) (compWk (.step .id) ρ₃)` and returns the closure `.lam 1 (.app 1 (.var 1) (.var 0))`!
  let H₅ := Heap.cons H₄ (𝕄.mul 𝕄.one 𝕄.one) ⟨.var 0, compWk (.step .id) ρ₃⟩
  let ρ_ret : Wk := .lift (.lift ρ₃)
  have hstep8 : HeapNumStep 𝕄 nr₂
      ⟨H₄, .lam 𝕄.one (.lam 𝕄.one (.app 𝕄.one (.var 1) (.var 0))), .lift ρ₃,
        [.appₑ 𝕄.one (.var 0) (compWk (.step .id) ρ₃)]⟩
      ⟨H₅, .lam 𝕄.one (.app 𝕄.one (.var 1) (.var 0)), ρ_ret, []⟩ :=
    .valStep .lamₕ
  have hstar : HeapNumStar 𝕄 nr₂ s₀ ⟨H₅, .lam 𝕄.one (.app 𝕄.one (.var 1) (.var 0)), ρ_ret, []⟩ :=
    .step hstep1 (.step hstep2 (.step hstep3 (.step hstep4
      (.step hstep5 (.step hstep6 (.step hstep7 (.step hstep8 (.refl _))))))))
  have hrel₀ : ErasedStateRel 𝕄 s₀ ts₀ := by
    refine ⟨?_, rfl, rfl, rfl, foldCapturingClosureTerm_compat 𝕄, trivial⟩
    refine .cons_erased (fun _ ↦ ⟨?_, trivial⟩)
      (.cons_erased (fun hne ↦ False.elim (hne rfl)) .nil)
    letI := 𝕄.decEqZero 𝕄.one
    dsimp only [compileEntry]
    rw [if_neg hw.nonTrivial]
  rcases returned_closure_captures_budget hw hnr hs₀ hrel₀ hstar with
    ⟨TH_ret, γ_ret, δ_body, hts, hH_ret, hH_usage, hbody, hdemand⟩
  have h_erase_body : erase 𝕄 false .nonStrict (.app 𝕄.one (.var 1) (.var 0)) =
      .app .nonStrict (.var 1) (.var 0) := by
    letI := 𝕄.decEqZero 𝕄.one
    dsimp only [erase, appZero]
    rw [if_neg hw.nonTrivial]
  have h_erase_lam : erase 𝕄 false .nonStrict (.lam 𝕄.one (.app 𝕄.one (.var 1) (.var 0))) =
      .lam (.app .nonStrict (.var 1) (.var 0)) := by
    letI := 𝕄.decEqZero 𝕄.one
    dsimp only [erase]
    rw [if_neg hw.nonTrivial, if_neg hw.nonTrivial]
  have hts_norm : TargetHeapNumStar ts₀
      ⟨TH_ret, .lam (.app .nonStrict (.var 1) (.var 0)), ρ_ret, []⟩ := by
    rwa [h_erase_body] at hts
  refine ⟨H₅, TH_ret, ρ_ret, ?_, γ_ret, δ_body, hH_usage, hbody, hdemand⟩
  refine ⟨⟨hstar, hts_norm, hrel₀,
    ⟨hH_ret, h_erase_lam.symm, rfl, rfl, ⟨trivial, trivial⟩, trivial⟩,
    fun x ↦ Nat.le_of_eq (Nat.zero_add _)⟩,
    fun x ↦ Nat.zero_add _⟩

/-! ### 6.2 Failure-Test Counterexamples (`docs/proof-ideas.md` §1)

As required by `docs/proof-ideas.md` (§1, "Failure tests"):
1. **Unqualified CBV Evaluation of an Erased Argument (`cbv_erased_eval_counterexample`)**:
   In strict mode (`Strictness.strict`) without erasing `0`-graded arguments, an application
   `.app .strict (.lam .zero) u_div` forces evaluation of `u_div` (`TargetStep.app_subst_arg`)
   before `beta` can fire (`ValueIfStrict .strict u_div` requires `Value u_div`).
   By contrast, under our compiler (`erase 𝕄 false .nonStrict`), `.app 𝕄.zero (.lam 𝕄.zero .zero) u_div`
   erases `u_div` at compile time to `.undef` and steps in 1 β-step to `.zero`!
2. **Affine Resource Duplication Rejected (`affine_duplication_counterexample`)**:
   Attempting to use a `1`-graded affine variable twice (`app 1 (.var 0) (.var 0)`)
   is rejected both statically by `Usage ZeroOneMany.affineModality` (`1 ≤ 1 + 1 = ω` is False in
   `affineModality`!) and dynamically by `HeapLookup ZeroOneMany.affineModality` (after one lookup at `.one`,
   the remaining slot budget is `.zero`, and a second lookup at `.one` from `.zero` fails).
3. **Linear Resource Discard Rejected (`linear_discard_counterexample`)**:
   In a linear conservation discipline (`LinearConservedRun`), supplying an initial budget of
   `1` at slot `0` and returning `.zero` without accessing slot `0` (`used 0 = 0`, `live 0 = 0`)
   violates `used 0 + live 0 = avail 0` (`0 + 0 ≠ 1`). -/

/-- **Failure Test 1 (`cbv_erased_eval_counterexample`)**:
    - Under naive strict evaluation without erasing the argument, `.app .strict (.lam .zero) (.fst .zero)`
      is **blocked** from `TargetStep.beta` because `.fst .zero` is not a `TargetTerm.Value`,
      and is stuck altogether because `.fst .zero` cannot step!
    - Under our erasing compiler (`erase 𝕄 false .nonStrict`), `.app 𝕄.zero (.lam 𝕄.zero .zero) (.fst 𝕄.one .zero)`
      erases the `0`-graded argument to `.undef` and reduces in 1 step to `.zero`. -/
theorem cbv_erased_eval_counterexample {M : Type} (𝕄 : Modality M) :
    (∀ t' : TargetTerm, ¬ TargetTerm.TargetStep (.app .strict (.lam .zero) (.fst .zero)) t') ∧
    TargetTerm.TargetStep
      (erase 𝕄 false .nonStrict (.app 𝕄.zero (.lam 𝕄.zero .zero) (.fst 𝕄.one .zero)))
      .zero := by
  refine ⟨?_, ?_⟩
  · intro t' hstep
    cases hstep with
    | app_subst hs => cases hs
    | app_subst_arg _ hs =>
      cases hs with
      | fst_subst hs' => cases hs'
    | beta hv =>
      cases hv
  · simp only [erase, ↓reduceIte, appZero]
    exact TargetTerm.TargetStep.beta trivial

/-- **Failure Test 2 (`affine_duplication_counterexample`)**:
    In `ZeroOneMany.affineModality` (`0` = `.zero`, `1` = `.one`, `add .one .one = .omega`, and `¬ (.one ≤ .omega)`):
    1. A heap slot with grade `.zero` (after an affine resource has been consumed down to `.zero`)
       **cannot** be looked up at demand `.one` (`¬ HeapLookup ZeroOneMany.affineModality (.cons .nil .zero e) 0 .one e' H'`),
    2. Static `Usage ZeroOneMany.affineModality` **rejects** duplicating variable `0` with budget `.one`
       in `.app .one (.var 0) (.var 0)`. -/
theorem affine_duplication_counterexample (e : Entry ZeroOneMany) :
    (∀ e' H', ¬ HeapLookup ZeroOneMany.affineModality (.cons .nil .zero e) 0 .one e' H') ∧
    ¬ Usage ZeroOneMany.affineModality (Conₘ.single ZeroOneMany.affineModality 0 .one) .oneMode
        (.app .one (.var 0) (.var 0)) := by
  refine ⟨?_, ?_⟩
  · intro e' H' hl
    cases hl with
    | @here _ _ _ r _ hsub =>
      have h0 := (ZeroOneMany.affineHasWellBehavedZero.zero_sub_eq hsub).2
      cases h0
  · intro hu
    rcases Usage.inv_app hu with ⟨γ, δ, h1, h2, hle⟩
    have hγ := Usage.inv_var h1 0
    have hδ := Usage.inv_var h2 0
    simp only [Conₘ.single, ↓reduceIte, Mode.toGrade, Mode.scale] at hγ hδ
    have hle0 := hle 0
    simp only [Conₘ.single, ↓reduceIte, Conₘ.add, Conₘ.scale] at hle0
    dsimp [ZeroOneMany.affineModality, Modality.le] at hγ hδ hle0
    revert hγ hδ hle0
    generalize γ 0 = g0
    generalize δ 0 = d0
    cases g0 <;> cases d0 <;> decide

/-- **Failure Test 3 (`linear_discard_counterexample`)**:
    Discarding a `1`-graded linear resource (`used 0 = 0` and `live 0 = 0` when `avail 0 = 1`)
    cannot satisfy `LinearConservedRun`: any run with `used 0 = 0` and `live 0 = 0` from
    `avail 0 = 1` is impossible. -/
theorem linear_discard_counterexample {M : Type} {𝕄 : Modality M} {nr₂ : M → M → M}
    {used live : Nat → Nat} {s₀ s' : State M} {ts₀ ts' : TargetState}
    (hrun : LinearConservedRun 𝕄 nr₂ (fun x ↦ if x = 0 then 1 else 0) used live s₀ s' ts₀ ts')
    (h_unused : used 0 = 0)
    (h_discarded : live 0 = 0) :
    False := by
  have hcons := hrun.linear_conservation 0
  rw [h_unused, h_discarded] at hcons
  simp at hcons

end BenchmarkAndFailureTests

end FeasibleUnivalence
