/-
Copyright (c) 2023 Robert Atkey.
Lean 4 translation prepared for the Feasible Univalence project, 2026.
Released under the BSD 3-Clause license of the source artefact; see LICENSE.

Source: Robert Atkey, *Polynomial Time and Dependent Types*, POPL 2024
(arXiv:2307.09145v2), Section 5.1 and Figure 1.
Reference artefact: bobatkey/qtt-models, tag `popl-2024-artefact-submission`,
commit 76fdbacd6e7bee19cb448b4d41bc21ac3687d63e, `src/AmortisedModel/Machine.agda`.

This module is milestone M4.0 of the M4 mission plan in `docs/atkey-rule-audit.md`:
the untyped call-by-value target language with its costed big-step semantics,
in which every evaluation rule costs one unit. The determinism theorem, the
fuel-bounded evaluator, and the example program are additions that the
source does not contain.
-/

namespace Atkey2024

/-! ## Syntax (Figure 1) -/

/-- Expressions over `n` variables, intrinsically scoped as in the Agda artefact.
Variables are de Bruijn indices; index `0` is the most recently bound value.
Apart from `lam` and `seq`, expressions take variables, not subexpressions, as
arguments. The body of a `lam` sees two extra variables: index `0` is the argument
and index `1` is the closure itself, which permits recursion. -/
inductive Expr : Nat → Type where
  | var {n : Nat} : Fin n → Expr n
  | lam {n : Nat} : Expr (n + 2) → Expr n
  | app {n : Nat} : Fin n → Fin n → Expr n
  | unit {n : Nat} : Expr n
  | pair {n : Nat} : Fin n → Fin n → Expr n
  | letpair {n : Nat} : Fin n → Expr (n + 2) → Expr n
  | true {n : Nat} : Expr n
  | false {n : Nat} : Expr n
  | cond {n : Nat} : Fin n → Expr n → Expr n → Expr n
  | seq {n : Nat} : Expr n → Expr (n + 1) → Expr n

mutual
  /-- Values: unit, pairs, booleans, and closures `clo⟨E, η⟩`. -/
  inductive Val : Type where
    | unit : Val
    | pair : Val → Val → Val
    | true : Val
    | false : Val
    | clo {n : Nat} : Expr (n + 2) → Env n → Val

  /-- Environments of `n` values, extended on the right. -/
  inductive Env : Nat → Type where
    | nil : Env 0
    | snoc {n : Nat} : Env n → Val → Env (n + 1)
end

/-- The unary encoding of natural numbers used for inputs (§6.1.3):
`natValue 0 = (true, ∗)` and `natValue (1 + n) = (false, natValue n)`. -/
def natValue : Nat → Val
  | 0 => .pair .true .unit
  | n + 1 => .pair .false (natValue n)

/-! ## Variable lookup -/

/-- Variable lookup `η[i]`, counting from the right. -/
def Env.get : {n : Nat} → Env n → Fin n → Val
  | _, .nil, i => i.elim0
  | _, .snoc _ v, ⟨0, _⟩ => v
  | _, .snoc η _, ⟨i + 1, h⟩ => Env.get η ⟨i, Nat.lt_of_succ_lt_succ h⟩

@[simp] theorem Env.get_snoc_zero {n : Nat} (η : Env n) (v : Val) :
    (Env.snoc η v).get ⟨0, Nat.succ_pos n⟩ = v := rfl

@[simp] theorem Env.get_snoc_succ {n : Nat} (η : Env n) (v : Val) (i : Fin n) :
    (Env.snoc η v).get i.succ = η.get i := rfl

/-- The artefact's lookup relation `i , η ⇓v V`. -/
inductive Lookup : {n : Nat} → Fin n → Env n → Val → Prop where
  | zero {n : Nat} {η : Env n} {v : Val} : Lookup ⟨0, Nat.succ_pos n⟩ (.snoc η v) v
  | succ {n : Nat} {i : Fin n} {η : Env n} {v v' : Val} :
      Lookup i η v → Lookup i.succ (.snoc η v') v

theorem Lookup.get_eq {n : Nat} {i : Fin n} {η : Env n} {v : Val} (h : Lookup i η v) :
    η.get i = v := by
  induction h with
  | zero => rfl
  | succ _ ih => exact ih

theorem Lookup.of_get_eq : ∀ {n : Nat} {i : Fin n} {η : Env n} {v : Val},
    η.get i = v → Lookup i η v
  | _, i, .nil, _, _ => i.elim0
  | _, ⟨0, _⟩, .snoc _ _, _, h => by subst h; exact .zero
  | _, ⟨j + 1, hj⟩, .snoc _ _, _, h =>
      .succ (i := ⟨j, Nat.lt_of_succ_lt_succ hj⟩) (Lookup.of_get_eq h)

/-- The lookup relation is the graph of `Env.get`. -/
theorem lookup_iff_get {n : Nat} {i : Fin n} {η : Env n} {v : Val} :
    Lookup i η v ↔ η.get i = v :=
  ⟨Lookup.get_eq, Lookup.of_get_eq⟩

/-! ## Costed big-step evaluation (Figure 1) -/

/-- `Eval E η k V` is the paper's `E, η ⇓ₖ V`: in environment `η`, the expression `E`
evaluates to the value `V` in `k` steps. Lookup premises are stated with `Env.get`;
`lookup_iff_get` relates them to the artefact's relation. Costs are written exactly
as in the artefact, for example `1 + k` and `k₁ + 1 + k₂`. -/
inductive Eval : {n : Nat} → Expr n → Env n → Nat → Val → Prop where
  | access {n : Nat} {i : Fin n} {η : Env n} {v : Val} :
      η.get i = v → Eval (.var i) η 1 v
  | lam {n : Nat} {E : Expr (n + 2)} {η : Env n} :
      Eval (.lam E) η 1 (.clo E η)
  | app {n n' : Nat} {x₁ x₂ : Fin n} {E : Expr (n' + 2)} {η : Env n} {η' : Env n'}
      {V V' : Val} {k : Nat} :
      η.get x₁ = .clo E η' → η.get x₂ = V →
      Eval E (.snoc (.snoc η' (.clo E η')) V) k V' →
      Eval (.app x₁ x₂) η (1 + k) V'
  | mkunit {n : Nat} {η : Env n} :
      Eval .unit η 1 .unit
  | mkpair {n : Nat} {x₁ x₂ : Fin n} {η : Env n} {V₁ V₂ : Val} :
      η.get x₁ = V₁ → η.get x₂ = V₂ → Eval (.pair x₁ x₂) η 1 (.pair V₁ V₂)
  | letpair {n : Nat} {x : Fin n} {E : Expr (n + 2)} {η : Env n} {V₁ V₂ V' : Val} {k : Nat} :
      η.get x = .pair V₁ V₂ → Eval E (.snoc (.snoc η V₁) V₂) k V' →
      Eval (.letpair x E) η (1 + k) V'
  | true {n : Nat} {η : Env n} :
      Eval .true η 1 .true
  | false {n : Nat} {η : Env n} :
      Eval .false η 1 .false
  | condTrue {n : Nat} {x : Fin n} {E₁ E₂ : Expr n} {η : Env n} {V : Val} {k : Nat} :
      η.get x = .true → Eval E₁ η k V → Eval (.cond x E₁ E₂) η (1 + k) V
  | condFalse {n : Nat} {x : Fin n} {E₁ E₂ : Expr n} {η : Env n} {V : Val} {k : Nat} :
      η.get x = .false → Eval E₂ η k V → Eval (.cond x E₁ E₂) η (1 + k) V
  | seq {n : Nat} {E₁ : Expr n} {E₂ : Expr (n + 1)} {η : Env n} {V V' : Val}
      {k₁ k₂ : Nat} :
      Eval E₁ η k₁ V → Eval E₂ (.snoc η V) k₂ V' → Eval (.seq E₁ E₂) η (k₁ + 1 + k₂) V'

/-- Rewrite the cost of an evaluation along an equation. -/
theorem Eval.cast_cost {n : Nat} {E : Expr n} {η : Env n} {k k' : Nat} {V : Val}
    (h : Eval E η k V) (hk : k = k') : Eval E η k' V := hk ▸ h

/-! ## Determinism

The programme's bound `steps_M(e, x) ≤ P(|x|)` presupposes that the step count
is a function of the program and its input. The machine is deterministic in both
the value and the cost. -/

/-- Evaluation is deterministic in both the result value and the step count. -/
theorem Eval.deterministic {n : Nat} {E : Expr n} {η : Env n} {k₁ k₂ : Nat} {V₁ V₂ : Val}
    (h₁ : Eval E η k₁ V₁) (h₂ : Eval E η k₂ V₂) : k₁ = k₂ ∧ V₁ = V₂ := by
  induction h₁ generalizing k₂ V₂ with
  | access hv =>
    cases h₂ with
    | access hv' => exact ⟨rfl, hv.symm.trans hv'⟩
  | lam =>
    cases h₂ with
    | lam => exact ⟨rfl, rfl⟩
  | app hx₁ hx₂ _ ih =>
    cases h₂ with
    | app hx₁' hx₂' hE =>
      have hc := hx₁.symm.trans hx₁'
      cases hc
      have hv := hx₂.symm.trans hx₂'
      subst hv
      obtain ⟨hk, hV⟩ := ih hE
      exact ⟨by rw [hk], hV⟩
  | mkunit =>
    cases h₂ with
    | mkunit => exact ⟨rfl, rfl⟩
  | mkpair hx₁ hx₂ =>
    cases h₂ with
    | mkpair hx₁' hx₂' => exact ⟨rfl, by rw [← hx₁, ← hx₂, hx₁', hx₂']⟩
  | letpair hx _ ih =>
    cases h₂ with
    | letpair hx' hE =>
      have hp := hx.symm.trans hx'
      cases hp
      obtain ⟨hk, hV⟩ := ih hE
      exact ⟨by rw [hk], hV⟩
  | true =>
    cases h₂ with
    | true => exact ⟨rfl, rfl⟩
  | false =>
    cases h₂ with
    | false => exact ⟨rfl, rfl⟩
  | condTrue hx _ ih =>
    cases h₂ with
    | condTrue _ hE =>
      obtain ⟨hk, hV⟩ := ih hE
      exact ⟨by rw [hk], hV⟩
    | condFalse hx' _ => exact absurd (hx.symm.trans hx') (by intro h; cases h)
  | condFalse hx _ ih =>
    cases h₂ with
    | condTrue hx' _ => exact absurd (hx.symm.trans hx') (by intro h; cases h)
    | condFalse _ hE =>
      obtain ⟨hk, hV⟩ := ih hE
      exact ⟨by rw [hk], hV⟩
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq hE₁ hE₂ =>
      obtain ⟨hk₁, hV⟩ := ih₁ hE₁
      subst hk₁ hV
      obtain ⟨hk₂, hV'⟩ := ih₂ hE₂
      exact ⟨by rw [hk₂], hV'⟩

/-! ## A fuel-bounded evaluator

`run fuel E η` follows the rules of `Eval`. It returns `none` when the fuel runs
out or when a lookup returns a value of the wrong shape. -/

/-- Fuel-bounded execution, returning the step count and the value. -/
def run : Nat → {n : Nat} → Expr n → Env n → Option (Nat × Val)
  | 0, _, _, _ => none
  | _ + 1, _, .var i, η => some (1, η.get i)
  | _ + 1, _, .lam E, η => some (1, .clo E η)
  | f + 1, _, .app x₁ x₂, η =>
      match η.get x₁ with
      | .clo E η' =>
          match run f E (.snoc (.snoc η' (.clo E η')) (η.get x₂)) with
          | some (k, V) => some (1 + k, V)
          | none => none
      | _ => none
  | _ + 1, _, .unit, _ => some (1, .unit)
  | _ + 1, _, .pair x₁ x₂, η => some (1, .pair (η.get x₁) (η.get x₂))
  | f + 1, _, .letpair x E, η =>
      match η.get x with
      | .pair V₁ V₂ =>
          match run f E (.snoc (.snoc η V₁) V₂) with
          | some (k, V) => some (1 + k, V)
          | none => none
      | _ => none
  | _ + 1, _, .true, _ => some (1, .true)
  | _ + 1, _, .false, _ => some (1, .false)
  | f + 1, _, .cond x E₁ E₂, η =>
      match η.get x with
      | .true =>
          match run f E₁ η with
          | some (k, V) => some (1 + k, V)
          | none => none
      | .false =>
          match run f E₂ η with
          | some (k, V) => some (1 + k, V)
          | none => none
      | _ => none
  | f + 1, _, .seq E₁ E₂, η =>
      match run f E₁ η with
      | some (k₁, V) =>
          match run f E₂ (.snoc η V) with
          | some (k₂, V') => some (k₁ + 1 + k₂, V')
          | none => none
      | none => none

/-- Soundness: every result of the evaluator is an evaluation derivation. -/
theorem run_sound : ∀ (fuel : Nat) {n : Nat} (E : Expr n) (η : Env n) (k : Nat) (V : Val),
    run fuel E η = some (k, V) → Eval E η k V := by
  intro fuel
  induction fuel with
  | zero => intro n E η k V h; simp [run] at h
  | succ f ih =>
    intro n E η k V h
    cases E with
    | var i =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .access rfl
    | lam E =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .lam
    | app x₁ x₂ =>
      simp only [run] at h
      split at h
      next n' E η' hget =>
        split at h
        next k' V' hrun =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .app hget rfl (ih _ _ _ _ hrun)
        next => cases h
      next => cases h
    | unit =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .mkunit
    | pair x₁ x₂ =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .mkpair rfl rfl
    | letpair x E =>
      simp only [run] at h
      split at h
      next V₁ V₂ hget =>
        split at h
        next k' V' hrun =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .letpair hget (ih _ _ _ _ hrun)
        next => cases h
      next => cases h
    | true =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .true
    | false =>
      simp only [run, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .false
    | cond x E₁ E₂ =>
      simp only [run] at h
      split at h
      next hget =>
        split at h
        next k' V' hrun =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .condTrue hget (ih _ _ _ _ hrun)
        next => cases h
      next hget =>
        split at h
        next k' V' hrun =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .condFalse hget (ih _ _ _ _ hrun)
        next => cases h
      next => cases h
    | seq E₁ E₂ =>
      simp only [run] at h
      split at h
      next k₁ V hrun₁ =>
        split at h
        next k₂ V' hrun₂ =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .seq (ih _ _ _ _ hrun₁) (ih _ _ _ _ hrun₂)
        next => cases h
      next => cases h

/-! Arithmetic on costs, proved without `omega` to keep the axiom footprint minimal. -/

private theorem not_one_add_le_zero (k : Nat) : ¬ 1 + k ≤ 0 := by
  rw [Nat.add_comm]; exact Nat.not_succ_le_zero k

private theorem le_of_one_add_le_succ {k f : Nat} (h : 1 + k ≤ f + 1) : k ≤ f := by
  rw [Nat.add_comm] at h; exact Nat.le_of_succ_le_succ h

private theorem not_seq_cost_le_zero (k₁ k₂ : Nat) : ¬ k₁ + 1 + k₂ ≤ 0 := by
  rw [Nat.add_right_comm]; exact Nat.not_succ_le_zero (k₁ + k₂)

private theorem seq_cost_le {k₁ k₂ f : Nat} (h : k₁ + 1 + k₂ ≤ f + 1) : k₁ + k₂ ≤ f := by
  rw [Nat.add_right_comm] at h; exact Nat.le_of_succ_le_succ h

/-- Completeness: an evaluation in `k` steps is found by the evaluator with any fuel
of at least `k`. -/
theorem run_complete {n : Nat} {E : Expr n} {η : Env n} {k : Nat} {V : Val}
    (h : Eval E η k V) : ∀ fuel, k ≤ fuel → run fuel E η = some (k, V) := by
  induction h with
  | access hv =>
    intro fuel hf
    cases fuel with
    | zero => exact absurd hf (Nat.not_succ_le_zero 0)
    | succ f => simp only [run, hv]
  | lam =>
    intro fuel hf
    cases fuel with
    | zero => exact absurd hf (Nat.not_succ_le_zero 0)
    | succ f => simp only [run]
  | app hx₁ hx₂ _ ih =>
    intro fuel hf
    cases fuel with
    | zero => exact absurd hf (not_one_add_le_zero _)
    | succ f => simp only [run, hx₁, hx₂, ih f (le_of_one_add_le_succ hf)]
  | mkunit =>
    intro fuel hf
    cases fuel with
    | zero => exact absurd hf (Nat.not_succ_le_zero 0)
    | succ f => simp only [run]
  | mkpair hx₁ hx₂ =>
    intro fuel hf
    cases fuel with
    | zero => exact absurd hf (Nat.not_succ_le_zero 0)
    | succ f => simp only [run, hx₁, hx₂]
  | letpair hx _ ih =>
    intro fuel hf
    cases fuel with
    | zero => exact absurd hf (not_one_add_le_zero _)
    | succ f => simp only [run, hx, ih f (le_of_one_add_le_succ hf)]
  | true =>
    intro fuel hf
    cases fuel with
    | zero => exact absurd hf (Nat.not_succ_le_zero 0)
    | succ f => simp only [run]
  | false =>
    intro fuel hf
    cases fuel with
    | zero => exact absurd hf (Nat.not_succ_le_zero 0)
    | succ f => simp only [run]
  | condTrue hx _ ih =>
    intro fuel hf
    cases fuel with
    | zero => exact absurd hf (not_one_add_le_zero _)
    | succ f => simp only [run, hx, ih f (le_of_one_add_le_succ hf)]
  | condFalse hx _ ih =>
    intro fuel hf
    cases fuel with
    | zero => exact absurd hf (not_one_add_le_zero _)
    | succ f => simp only [run, hx, ih f (le_of_one_add_le_succ hf)]
  | @seq _ _ _ _ _ _ k₁ k₂ _ _ ih₁ ih₂ =>
    intro fuel hf
    cases fuel with
    | zero => exact absurd hf (not_seq_cost_le_zero _ _)
    | succ f =>
      have hk := seq_cost_le hf
      simp only [run, ih₁ f (Nat.le_trans (Nat.le_add_right k₁ k₂) hk),
        ih₂ f (Nat.le_trans (Nat.le_add_left k₂ k₁) hk)]

/-- The evaluator decides evaluation: `Eval E η k V` holds exactly when running with
fuel `k` returns `(k, V)`. -/
theorem eval_iff_run {n : Nat} {E : Expr n} {η : Env n} {k : Nat} {V : Val} :
    Eval E η k V ↔ run k E η = some (k, V) :=
  ⟨fun h ↦ run_complete h k (Nat.le_refl k), run_sound k E η k V⟩

/-! ## Example: a recursive traversal of a unary input in linear time

`countdown` takes the input `natValue m` at index `0`. It builds a closure that
walks down the unary chain by self-application and finally returns `∗`. The
theorem `countdown_cost` gives its exact step count, `3 * m + 6`: the bound is
uniform in the input, as in Theorems 6.1 and 6.2, and is proved by induction, not
by running the program. -/

/-- The loop body. In context `x :: self :: input`, after `letpair` the context is
`tail :: tag :: x :: self :: input`. -/
def countdownBody : Expr 3 :=
  .letpair 0 (.cond 1 .unit (.app 3 0))

/-- Build the closure, then apply it to the input. -/
def countdown : Expr 1 :=
  .seq (.lam countdownBody) (.app 0 1)

theorem countdownBody_cost (η : Env 1) (m : Nat) :
    Eval countdownBody (.snoc (.snoc η (.clo countdownBody η)) (natValue m))
      (3 * m + 3) .unit := by
  induction m with
  | zero =>
    exact (Eval.letpair rfl (Eval.condTrue rfl Eval.mkunit)).cast_cost rfl
  | succ m ih =>
    -- `3 * (m + 1) + 3` unfolds definitionally to `3 * m + 3 + 1 + 1 + 1`.
    refine (Eval.letpair rfl (Eval.condFalse rfl (Eval.app rfl rfl ih))).cast_cost ?_
    rw [Nat.add_comm 1 (3 * m + 3), Nat.add_comm 1 (3 * m + 3 + 1),
      Nat.add_comm 1 (3 * m + 3 + 1 + 1)]
    rfl

/-- `countdown` runs in exactly `3 * m + 6` steps on the input `natValue m`. -/
theorem countdown_cost (m : Nat) :
    Eval countdown (.snoc .nil (natValue m)) (3 * m + 6) .unit := by
  refine (Eval.seq Eval.lam (Eval.app rfl rfl (countdownBody_cost _ m))).cast_cost ?_
  rw [Nat.add_comm 1 (3 * m + 3), Nat.add_comm (1 + 1) (3 * m + 3 + 1)]

end Atkey2024
