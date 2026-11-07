/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Untyped/Properties.agda, extended with Σ, Unit and Empty
(mr-ohman/logrel-mltt master, commit 9d6e290064962a1987c9e1a131c2fb967d6ef928).
-/
import LogrelMLTT.Syntax

namespace LogrelMLTT

theorem wkVar_lift {ρ ρ' : Wk} (h : ∀ x, wkVar ρ x = wkVar ρ' x) :
    ∀ x, wkVar (.lift ρ) x = wkVar (.lift ρ') x
  | 0 => rfl
  | x + 1 => congrArg (· + 1) (h x)

theorem wkVar_to_wk {ρ ρ' : Wk} (h : ∀ x, wkVar ρ x = wkVar ρ' x) :
    ∀ t, wk ρ t = wk ρ' t
  | .univ => rfl
  | .pi A B => by
      simp [wk, wkVar_to_wk h A, wkVar_to_wk (wkVar_lift h) B]
  | .nat => rfl
  | .var x => congrArg Term.var (h x)
  | .lam t => congrArg Term.lam (wkVar_to_wk (wkVar_lift h) t)
  | .app t u => by
      simp [wk, wkVar_to_wk h t, wkVar_to_wk h u]
  | .zero => rfl
  | .succ t => congrArg Term.succ (wkVar_to_wk h t)
  | .natrec A z s n => by
      simp [wk, wkVar_to_wk (wkVar_lift h) A,
        wkVar_to_wk h z, wkVar_to_wk h s, wkVar_to_wk h n]
  | .sigma A B => by
      simp [wk, wkVar_to_wk h A, wkVar_to_wk (wkVar_lift h) B]
  | .prod t u => by
      simp [wk, wkVar_to_wk h t, wkVar_to_wk h u]
  | .fst t => congrArg Term.fst (wkVar_to_wk h t)
  | .snd t => congrArg Term.snd (wkVar_to_wk h t)
  | .unit => rfl
  | .star => rfl
  | .empty => rfl
  | .emptyrec A e => by
      simp [wk, wkVar_to_wk h A, wkVar_to_wk h e]
  | .id A t u => by
      simp [wk, wkVar_to_wk h A, wkVar_to_wk h t, wkVar_to_wk h u]
  | .rfl => rfl
  | .idrec A P r t u b => by
      simp [wk, wkVar_to_wk h A, wkVar_to_wk (wkVar_lift (wkVar_lift h)) P,
        wkVar_to_wk h r, wkVar_to_wk h t, wkVar_to_wk h u, wkVar_to_wk h b]

theorem wkVar_lift_id : ∀ x, wkVar (.lift .id) x = wkVar .id x
  | 0 => rfl
  | _ + 1 => rfl

theorem wkVar_id (x : Nat) : wkVar .id x = x := rfl

@[simp]
theorem wk_id : ∀ t, wk .id t = t
  | .univ => rfl
  | .pi A B => by
      rw [wk, wk_id A, wkVar_to_wk wkVar_lift_id B, wk_id B]
  | .nat => rfl
  | .var _ => rfl
  | .lam t => by
      rw [wk, wkVar_to_wk wkVar_lift_id t, wk_id t]
  | .app t u => by
      rw [wk, wk_id t, wk_id u]
  | .zero => rfl
  | .succ t => congrArg Term.succ (wk_id t)
  | .natrec A z s n => by
      rw [wk, wkVar_to_wk wkVar_lift_id A, wk_id A, wk_id z, wk_id s, wk_id n]
  | .sigma A B => by
      rw [wk, wk_id A, wkVar_to_wk wkVar_lift_id B, wk_id B]
  | .prod t u => by
      rw [wk, wk_id t, wk_id u]
  | .fst t => congrArg Term.fst (wk_id t)
  | .snd t => congrArg Term.snd (wk_id t)
  | .unit => rfl
  | .star => rfl
  | .empty => rfl
  | .emptyrec A e => by
      rw [wk, wk_id A, wk_id e]
  | .id A t u => by
      rw [wk, wk_id A, wk_id t, wk_id u]
  | .rfl => rfl
  | .idrec A P r t u b => by
      rw [wk, wk_id A, wkVar_to_wk (wkVar_lift wkVar_lift_id) P,
        wkVar_to_wk wkVar_lift_id P, wk_id P, wk_id r, wk_id t, wk_id u, wk_id b]

@[simp]
theorem wk_lift_id (t : Term) : wk (.lift .id) t = t :=
  (wkVar_to_wk wkVar_lift_id t).trans (wk_id t)

theorem wkVar_comp : ∀ (ρ ρ' : Wk) (x : Nat),
    wkVar ρ (wkVar ρ' x) = wkVar (compWk ρ ρ') x
  | .id, _, _ => rfl
  | .step ρ, ρ', x => congrArg (· + 1) (wkVar_comp ρ ρ' x)
  | .lift _, .id, _ => rfl
  | .lift ρ, .step ρ', x => congrArg (· + 1) (wkVar_comp ρ ρ' x)
  | .lift _, .lift _, 0 => rfl
  | .lift ρ, .lift ρ', x + 1 => congrArg (· + 1) (wkVar_comp ρ ρ' x)

theorem wk_comp : ∀ (ρ ρ' : Wk) (t : Term),
    wk ρ (wk ρ' t) = wk (compWk ρ ρ') t
  | ρ, ρ', .univ => rfl
  | ρ, ρ', .pi A B => by
      simp [wk, wk_comp ρ ρ' A, wk_comp (.lift ρ) (.lift ρ') B, compWk]
  | ρ, ρ', .nat => rfl
  | ρ, ρ', .var x => congrArg Term.var (wkVar_comp ρ ρ' x)
  | ρ, ρ', .lam t => by
      simp [wk, wk_comp (.lift ρ) (.lift ρ') t, compWk]
  | ρ, ρ', .app t u => by
      simp [wk, wk_comp ρ ρ' t, wk_comp ρ ρ' u]
  | ρ, ρ', .zero => rfl
  | ρ, ρ', .succ t => congrArg Term.succ (wk_comp ρ ρ' t)
  | ρ, ρ', .natrec A z s n => by
      simp [wk, wk_comp (.lift ρ) (.lift ρ') A,
        wk_comp ρ ρ' z, wk_comp ρ ρ' s, wk_comp ρ ρ' n, compWk]
  | ρ, ρ', .sigma A B => by
      simp [wk, wk_comp ρ ρ' A, wk_comp (.lift ρ) (.lift ρ') B, compWk]
  | ρ, ρ', .prod t u => by
      simp [wk, wk_comp ρ ρ' t, wk_comp ρ ρ' u]
  | ρ, ρ', .fst t => congrArg Term.fst (wk_comp ρ ρ' t)
  | ρ, ρ', .snd t => congrArg Term.snd (wk_comp ρ ρ' t)
  | ρ, ρ', .unit => rfl
  | ρ, ρ', .star => rfl
  | ρ, ρ', .empty => rfl
  | ρ, ρ', .emptyrec A e => by
      simp [wk, wk_comp ρ ρ' A, wk_comp ρ ρ' e]
  | ρ, ρ', .id A t u => by
      simp [wk, wk_comp ρ ρ' A, wk_comp ρ ρ' t, wk_comp ρ ρ' u]
  | _, _, .rfl => rfl
  | ρ, ρ', .idrec A P r t u b => by
      simp [wk, wk_comp ρ ρ' A, wk_comp (.lift (.lift ρ)) (.lift (.lift ρ')) P,
        wk_comp ρ ρ' r, wk_comp ρ ρ' t, wk_comp ρ ρ' u, wk_comp ρ ρ' b, compWk]

theorem lift_step_comp : ∀ ρ : Wk,
    compWk (.step .id) ρ = compWk (.lift ρ) (.step .id)
  | .id => rfl
  | .step ρ => congrArg Wk.step (lift_step_comp ρ)
  | .lift _ => rfl

theorem wk1_wk (ρ : Wk) (t : Term) : wk1 (wk ρ t) = wk (.step ρ) t :=
  wk_comp (.step .id) ρ t

theorem lift_wk1 (ρ : Wk) (t : Term) : wk (.lift ρ) (wk1 t) = wk (.step ρ) t := by
  unfold wk1
  rw [wk_comp (.lift ρ) (.step .id) t, ← lift_step_comp ρ]
  rfl

theorem wk1_wk_eq_lift_wk1 (ρ : Wk) (t : Term) :
    wk1 (wk ρ t) = wk (.lift ρ) (wk1 t) :=
  (wk1_wk ρ t).trans (lift_wk1 ρ t).symm

theorem substVar_lift {σ σ' : Subst} (h : ∀ x, σ x = σ' x) :
    ∀ x, liftSubst σ x = liftSubst σ' x
  | 0 => rfl
  | x + 1 => congrArg wk1 (h x)

theorem substVar_to_subst {σ σ' : Subst} (h : ∀ x, σ x = σ' x) :
    ∀ t, subst σ t = subst σ' t
  | .univ => rfl
  | .pi A B => by
      simp [subst, substVar_to_subst h A, substVar_to_subst (substVar_lift h) B]
  | .nat => rfl
  | .var x => h x
  | .lam t => congrArg Term.lam (substVar_to_subst (substVar_lift h) t)
  | .app t u => by
      simp [subst, substVar_to_subst h t, substVar_to_subst h u]
  | .zero => rfl
  | .succ t => congrArg Term.succ (substVar_to_subst h t)
  | .natrec A z s n => by
      simp [subst, substVar_to_subst (substVar_lift h) A,
        substVar_to_subst h z, substVar_to_subst h s, substVar_to_subst h n]
  | .sigma A B => by
      simp [subst, substVar_to_subst h A, substVar_to_subst (substVar_lift h) B]
  | .prod t u => by
      simp [subst, substVar_to_subst h t, substVar_to_subst h u]
  | .fst t => congrArg Term.fst (substVar_to_subst h t)
  | .snd t => congrArg Term.snd (substVar_to_subst h t)
  | .unit => rfl
  | .star => rfl
  | .empty => rfl
  | .emptyrec A e => by
      simp [subst, substVar_to_subst h A, substVar_to_subst h e]
  | .id A t u => by
      simp [subst, substVar_to_subst h A, substVar_to_subst h t, substVar_to_subst h u]
  | .rfl => rfl
  | .idrec A P r t u b => by
      simp [subst, substVar_to_subst h A, substVar_to_subst (substVar_lift (substVar_lift h)) P,
        substVar_to_subst h r, substVar_to_subst h t, substVar_to_subst h u, substVar_to_subst h b]

theorem subst_lift_id : ∀ x, liftSubst idSubst x = idSubst x
  | 0 => rfl
  | _ + 1 => rfl

@[simp]
theorem subst_id : ∀ t, subst idSubst t = t
  | .univ => rfl
  | .pi A B => by
      rw [subst, subst_id A, substVar_to_subst subst_lift_id B, subst_id B]
  | .nat => rfl
  | .var _ => rfl
  | .lam t => by
      rw [subst, substVar_to_subst subst_lift_id t, subst_id t]
  | .app t u => by
      rw [subst, subst_id t, subst_id u]
  | .zero => rfl
  | .succ t => congrArg Term.succ (subst_id t)
  | .natrec A z s n => by
      rw [subst, substVar_to_subst subst_lift_id A, subst_id A,
        subst_id z, subst_id s, subst_id n]
  | .sigma A B => by
      rw [subst, subst_id A, substVar_to_subst subst_lift_id B, subst_id B]
  | .prod t u => by
      rw [subst, subst_id t, subst_id u]
  | .fst t => congrArg Term.fst (subst_id t)
  | .snd t => congrArg Term.snd (subst_id t)
  | .unit => rfl
  | .star => rfl
  | .empty => rfl
  | .emptyrec A e => by
      rw [subst, subst_id A, subst_id e]
  | .id A t u => by
      rw [subst, subst_id A, subst_id t, subst_id u]
  | .rfl => rfl
  | .idrec A P r t u b => by
      rw [subst, subst_id A, substVar_to_subst (substVar_lift subst_lift_id) P,
        substVar_to_subst subst_lift_id P, subst_id P,
        subst_id r, subst_id t, subst_id u, subst_id b]

theorem subst_lift_wkSubst {ρ : Wk} {σ : Subst} (t : Term) :
    subst (wkSubst (.lift ρ) (liftSubst σ)) t = subst (liftSubst (wkSubst ρ σ)) t := by
  apply substVar_to_subst
  intro x
  cases x with
  | zero => rfl
  | succ x => exact (wk1_wk_eq_lift_wk1 ρ (σ x)).symm

theorem subst_lift2_wkSubst {ρ : Wk} {σ : Subst} (t : Term) :
    subst (wkSubst (.lift (.lift ρ)) (liftSubst (liftSubst σ))) t =
      subst (liftSubst (liftSubst (wkSubst ρ σ))) t := by
  apply substVar_to_subst
  intro x
  cases x with
  | zero => rfl
  | succ x =>
      cases x with
      | zero => rfl
      | succ x =>
          change wk (.lift (.lift ρ)) (wk1 (wk1 (σ x))) = wk1 (wk1 (wk ρ (σ x)))
          rw [← wk1_wk_eq_lift_wk1 (.lift ρ), ← wk1_wk_eq_lift_wk1 ρ]

theorem subst_lift_substWk {ρ : Wk} {σ : Subst} (t : Term) :
    subst (substWk (liftSubst σ) (.lift ρ)) t = subst (liftSubst (substWk σ ρ)) t := by
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem subst_lift2_substWk {ρ : Wk} {σ : Subst} (t : Term) :
    subst (substWk (liftSubst (liftSubst σ)) (.lift (.lift ρ))) t =
      subst (liftSubst (liftSubst (substWk σ ρ))) t := by
  apply substVar_to_subst
  intro x
  cases x with
  | zero => rfl
  | succ x =>
      cases x <;> rfl

theorem wk_subst {ρ : Wk} {σ : Subst} :
    ∀ t, wk ρ (subst σ t) = subst (wkSubst ρ σ) t
  | .univ => rfl
  | .pi A B => by
      rw [subst, wk, subst, wk_subst A, wk_subst B, subst_lift_wkSubst B]
  | .nat => rfl
  | .var _ => rfl
  | .lam t => by
      rw [subst, wk, subst, wk_subst t, subst_lift_wkSubst t]
  | .app t u => by
      rw [subst, wk, subst, wk_subst t, wk_subst u]
  | .zero => rfl
  | .succ t => congrArg Term.succ (wk_subst t)
  | .natrec A z s n => by
      rw [subst, wk, subst, wk_subst A, subst_lift_wkSubst A,
        wk_subst z, wk_subst s, wk_subst n]
  | .sigma A B => by
      rw [subst, wk, subst, wk_subst A, wk_subst B, subst_lift_wkSubst B]
  | .prod t u => by
      rw [subst, wk, subst, wk_subst t, wk_subst u]
  | .fst t => congrArg Term.fst (wk_subst t)
  | .snd t => congrArg Term.snd (wk_subst t)
  | .unit => rfl
  | .star => rfl
  | .empty => rfl
  | .emptyrec A e => by
      rw [subst, wk, subst, wk_subst A, wk_subst e]
  | .id A t u => by
      rw [subst, wk, subst, wk_subst A, wk_subst t, wk_subst u]
  | .rfl => rfl
  | .idrec A P r t u b => by
      rw [subst, wk, subst, wk_subst A, wk_subst P, subst_lift2_wkSubst P,
        wk_subst r, wk_subst t, wk_subst u, wk_subst b]

theorem subst_wk {ρ : Wk} {σ : Subst} :
    ∀ t, subst σ (wk ρ t) = subst (substWk σ ρ) t
  | .univ => rfl
  | .pi A B => by
      rw [wk, subst, subst, subst_wk A, subst_wk B, subst_lift_substWk B]
  | .nat => rfl
  | .var _ => rfl
  | .lam t => by
      rw [wk, subst, subst, subst_wk t, subst_lift_substWk t]
  | .app t u => by
      rw [wk, subst, subst, subst_wk t, subst_wk u]
  | .zero => rfl
  | .succ t => congrArg Term.succ (subst_wk t)
  | .natrec A z s n => by
      rw [wk, subst, subst, subst_wk A, subst_lift_substWk A,
        subst_wk z, subst_wk s, subst_wk n]
  | .sigma A B => by
      rw [wk, subst, subst, subst_wk A, subst_wk B, subst_lift_substWk B]
  | .prod t u => by
      rw [wk, subst, subst, subst_wk t, subst_wk u]
  | .fst t => congrArg Term.fst (subst_wk t)
  | .snd t => congrArg Term.snd (subst_wk t)
  | .unit => rfl
  | .star => rfl
  | .empty => rfl
  | .emptyrec A e => by
      rw [wk, subst, subst, subst_wk A, subst_wk e]
  | .id A t u => by
      rw [wk, subst, subst, subst_wk A, subst_wk t, subst_wk u]
  | .rfl => rfl
  | .idrec A P r t u b => by
      rw [wk, subst, subst, subst_wk A, subst_wk P, subst_lift2_substWk P,
        subst_wk r, subst_wk t, subst_wk u, subst_wk b]

theorem wk_subst_lift {ρ : Wk} {σ : Subst} (G : Term) :
    wk (.lift ρ) (subst (liftSubst σ) G) = subst (liftSubst (wkSubst ρ σ)) G :=
  (wk_subst G).trans (subst_lift_wkSubst G)

theorem wk_subst_lift2 {ρ : Wk} {σ : Subst} (G : Term) :
    wk (.lift (.lift ρ)) (subst (liftSubst (liftSubst σ)) G) =
      subst (liftSubst (liftSubst (wkSubst ρ σ))) G :=
  (wk_subst G).trans (subst_lift2_wkSubst G)

theorem wk_eq_subst (ρ : Wk) (t : Term) : wk ρ t = subst (toSubst ρ) t := by
  have h : wk ρ (subst idSubst t) = subst (wkSubst ρ idSubst) t := wk_subst t
  rw [subst_id] at h
  exact h

theorem substCompLift {σ σ' : Subst} :
    ∀ x, compSubst (liftSubst σ) (liftSubst σ') x = liftSubst (compSubst σ σ') x
  | 0 => rfl
  | x + 1 => (subst_wk (σ' x)).trans (wk_subst (σ' x)).symm

theorem substCompLift2 {σ σ' : Subst} :
    ∀ x, compSubst (liftSubst (liftSubst σ)) (liftSubst (liftSubst σ')) x =
      liftSubst (liftSubst (compSubst σ σ')) x :=
  fun x ↦ (substCompLift x).trans (substVar_lift substCompLift x)

theorem substCompEq {σ σ' : Subst} :
    ∀ t, subst σ (subst σ' t) = subst (compSubst σ σ') t
  | .univ => rfl
  | .pi A B => by
      rw [subst, subst, substCompEq A, substCompEq B, substVar_to_subst substCompLift B]
      rfl
  | .nat => rfl
  | .var _ => rfl
  | .lam t => by
      rw [subst, subst, substCompEq t, substVar_to_subst substCompLift t]
      rfl
  | .app t u => by
      rw [subst, subst, substCompEq t, substCompEq u]
      rfl
  | .zero => rfl
  | .succ t => congrArg Term.succ (substCompEq t)
  | .natrec A z s n => by
      rw [subst, subst, substCompEq A, substVar_to_subst substCompLift A,
        substCompEq z, substCompEq s, substCompEq n]
      rfl
  | .sigma A B => by
      rw [subst, subst, substCompEq A, substCompEq B, substVar_to_subst substCompLift B]
      rfl
  | .prod t u => by
      rw [subst, subst, substCompEq t, substCompEq u]
      rfl
  | .fst t => congrArg Term.fst (substCompEq t)
  | .snd t => congrArg Term.snd (substCompEq t)
  | .unit => rfl
  | .star => rfl
  | .empty => rfl
  | .emptyrec A e => by
      rw [subst, subst, substCompEq A, substCompEq e]
      rfl
  | .id A t u => by
      rw [subst, subst, substCompEq A, substCompEq t, substCompEq u]
      rfl
  | .rfl => rfl
  | .idrec A P r t u b => by
      rw [subst, subst, substCompEq A, substCompEq P, substVar_to_subst substCompLift2 P,
        substCompEq r, substCompEq t, substCompEq u, substCompEq b]
      rfl

theorem wk_comp_subst {a : Term} (ρ ρ' : Wk) (G : Term) :
    subst0 (wk (.lift (compWk ρ ρ')) G) a =
      subst0 (wk (.lift ρ) (wk (.lift ρ') G)) a :=
  congrArg (fun x ↦ subst0 x a) (wk_comp (.lift ρ) (.lift ρ') G).symm

theorem wk_beta {ρ : Wk} {a : Term} (t : Term) :
    wk ρ (subst0 t a) = subst0 (wk (.lift ρ) t) (wk ρ a) := by
  unfold subst0
  rw [wk_subst t, subst_wk t]
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem wk_betaKeep {ρ : Wk} {a : Term} (t : Term) :
    wk (.lift ρ) (substKeep t a) = substKeep (wk (.lift ρ) t) (wk (.lift ρ) a) := by
  unfold substKeep
  rw [wk_subst t, subst_wk t]
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem wk_arr (ρ : Wk) (A B : Term) :
    wk ρ (arr A B) = arr (wk ρ A) (wk ρ B) := by
  unfold arr
  rw [wk, wk1_wk_eq_lift_wk1]

theorem wk_beta_natrec (ρ : Wk) (G : Term) :
    wk ρ (recStepType G) = recStepType (wk (.lift ρ) G) := by
  unfold recStepType arr
  rw [wk, wk, ← wk1_wk_eq_lift_wk1 (.lift ρ), wk_betaKeep G]
  rfl

theorem substVarSingletonComp {u : Term} {σ : Subst} :
    ∀ x, compSubst (sgSubst u) (liftSubst σ) x = consSubst σ u x
  | 0 => rfl
  | x + 1 => (subst_wk (σ x)).trans (subst_id (σ x))

theorem substSingletonComp {a : Term} {σ : Subst} (t : Term) :
    subst (compSubst (sgSubst a) (liftSubst σ)) t = subst (consSubst σ a) t :=
  substVar_to_subst substVarSingletonComp t

theorem singleSubstComp (t : Term) (σ : Subst) (G : Term) :
    subst0 (subst (liftSubst σ) G) t = subst (consSubst σ t) G :=
  (substCompEq G).trans (substSingletonComp G)

theorem singleSubstWkComp {ρ : Wk} (t : Term) (σ : Subst) (G : Term) :
    subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) t =
      subst (consSubst (wkSubst ρ σ) t) G := by
  rw [wk_subst_lift, singleSubstComp]

theorem singleSubstLift {σ : Subst} (G t : Term) :
    subst σ (subst0 G t) = subst0 (subst (liftSubst σ) G) (subst σ t) := by
  unfold subst0
  rw [substCompEq G, substCompEq G]
  apply substVar_to_subst
  intro x
  cases x with
  | zero => rfl
  | succ x => exact (substVarSingletonComp (x + 1)).symm

theorem idWkLiftSubstLemma (σ : Subst) (G : Term) :
    subst0 (wk (.lift (.step .id)) (subst (liftSubst σ) G)) (.var 0) =
      subst (liftSubst σ) G := by
  rw [singleSubstWkComp (.var 0) σ G]
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem substVarCompKeep {t : Term} (σ : Subst) :
    ∀ x, compSubst (consSubst (wk1Subst idSubst) (subst (liftSubst σ) t)) (liftSubst σ) x =
      compSubst (liftSubst σ) (consSubst (wk1Subst idSubst) t) x
  | 0 => rfl
  | x + 1 => (subst_wk (σ x)).trans (wk_eq_subst (.step .id) (σ x)).symm

theorem singleSubstLiftKeep (σ : Subst) (G t : Term) :
    subst (liftSubst σ) (substKeep G t) =
      substKeep (subst (liftSubst σ) G) (subst (liftSubst σ) t) := by
  unfold substKeep
  rw [substCompEq G, substCompEq G]
  exact (substVar_to_subst (substVarCompKeep σ) G).symm

theorem substConsComp {σ : Subst} {t G : Term} :
    subst (consSubst (fun x ↦ σ (x + 1)) (subst (tailSubst σ) t)) G =
      subst σ (subst (consSubst (fun x ↦ .var (x + 1)) (wk1 t)) G) := by
  rw [substCompEq G]
  apply substVar_to_subst
  intro x
  cases x with
  | zero => exact (subst_wk (σ := σ) (ρ := .step .id) t).symm
  | succ _ => rfl

@[simp]
theorem subst_consSubst_wk1 (σ : Subst) (a m : Term) :
    subst (consSubst σ a) (wk1 m) = subst σ m :=
  subst_wk (σ := consSubst σ a) (ρ := .step .id) m

@[simp]
theorem subst_sgSubst_wk1 (a m : Term) : subst (sgSubst a) (wk1 m) = m := by
  unfold sgSubst
  rw [subst_consSubst_wk1, subst_id]

theorem wkSingleSubstId (F : Term) :
    subst0 (wk (.lift (.step .id)) F) (.var 0) = F := by
  unfold subst0
  rw [subst_wk F]
  refine Eq.trans ?_ (subst_id F)
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem cons_wk_subst (ρ : Wk) (σ : Subst) (a t : Term) :
    subst (compSubst (substWk (sgSubst a) (.lift ρ)) (liftSubst σ)) t =
      subst (consSubst (wkSubst ρ σ) a) t := by
  apply substVar_to_subst
  intro x
  cases x with
  | zero => rfl
  | succ x => exact (subst_wk (σ x)).trans (wk_eq_subst ρ (σ x)).symm

theorem natrecSucCaseLemma {σ : Subst} :
    ∀ x, compSubst (wkSubst (.step .id) (consSubst (wk1Subst idSubst) (.succ (.var 0))))
      (liftSubst σ) x =
      compSubst (substWk (liftSubst (liftSubst σ)) (.step .id))
        (consSubst (wk1Subst idSubst) (.succ (.var 0))) x
  | 0 => rfl
  | x + 1 => by
      change subst (wkSubst (.step .id) (consSubst (wk1Subst idSubst) (.succ (.var 0))))
        (wk (.step .id) (σ x)) = wk (.step .id) (wk (.step .id) (σ x))
      rw [← wk_subst (ρ := .step .id), subst_wk (ρ := .step .id) (σ x)]
      exact congrArg (wk (.step .id)) (wk_eq_subst (.step .id) (σ x)).symm

theorem natrecSucCase (σ : Subst) (F : Term) :
    subst σ (recStepType F) = recStepType (subst (liftSubst σ) F) := by
  unfold recStepType arr substKeep
  dsimp [subst, liftSubst]
  congr 1
  congr 1
  unfold wk1
  rw [subst_wk (ρ := .step .id), substCompEq F, wk_subst (ρ := .step .id), substCompEq F]
  exact (substVar_to_subst natrecSucCaseLemma F).symm

theorem natrecIrrelevantSubstLemma (F z s m : Term) (σ : Subst) :
    ∀ x,
      compSubst
        (substWk
          (compSubst
            (compSubst (sgSubst (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m))
              (liftSubst (sgSubst m)))
            (liftSubst (liftSubst σ)))
          (.step .id))
        (consSubst (tailSubst idSubst) (.succ (.var 0))) x =
      consSubst σ (.succ m) x
  | 0 => by
      change Term.succ (subst (sgSubst (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m)) (wk1 m)) =
        Term.succ m
      rw [subst_sgSubst_wk1]
  | x + 1 => by
      dsimp [compSubst, substWk, consSubst, tailSubst, idSubst, liftSubst, wkVar, subst]
      rw [substSingletonComp, subst_consSubst_wk1, subst_sgSubst_wk1]

theorem natrecIrrelevantSubst (F z s m : Term) (σ : Subst) :
    subst (consSubst σ (.succ m)) F =
      subst0
        (subst (liftSubst (sgSubst m))
          (subst (liftSubst (liftSubst σ))
            (wk1 (substKeep F (.succ (.var 0))))))
        (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m) := by
  unfold subst0 substKeep wk1
  rw [substCompEq, substCompEq, subst_wk (ρ := .step .id), substCompEq]
  exact (substVar_to_subst (natrecIrrelevantSubstLemma F z s m σ) F).symm

theorem natrecIrrelevantSubstLemma' (F z s n : Term) :
    ∀ x,
      compSubst
        (substWk
          (compSubst (sgSubst (.natrec F z s n)) (liftSubst (sgSubst n)))
          (.step .id))
        (consSubst (tailSubst idSubst) (.succ (.var 0))) x =
      consSubst idSubst (.succ n) x
  | 0 => by
      change Term.succ (subst (sgSubst (.natrec F z s n)) (wk1 n)) = Term.succ n
      rw [subst_sgSubst_wk1]
  | _ + 1 => rfl

theorem natrecIrrelevantSubst' (F z s n : Term) :
    subst0
      (subst (liftSubst (sgSubst n))
        (wk1 (substKeep F (.succ (.var 0)))))
      (.natrec F z s n) =
      subst0 F (.succ n) := by
  unfold subst0 substKeep wk1
  rw [substCompEq, subst_wk (ρ := .step .id), substCompEq]
  exact substVar_to_subst (natrecIrrelevantSubstLemma' F z s n) F

theorem cons0wkLift1_id (σ : Subst) (G : Term) :
    subst (sgSubst (.var 0)) (wk (.lift (.step .id)) (subst (liftSubst σ) G)) =
      subst (liftSubst σ) G := by
  rw [subst_wk (subst (liftSubst σ) G)]
  refine Eq.trans ?_ (subst_id (subst (liftSubst σ) G))
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem substConsId {σ : Subst} {t : Term} (G : Term) :
    subst (consSubst σ (subst σ t)) G = subst σ (subst (sgSubst t) G) := by
  rw [substCompEq G]
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem substConsTailId {G t : Term} {σ : Subst} :
    subst (consSubst (tailSubst σ) (subst σ t)) G =
      subst σ (subst (consSubst (tailSubst idSubst) t) G) := by
  rw [substCompEq G]
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem substConcatSingleton' {a : Term} {σ : Subst} (t : Term) :
    subst (compSubst σ (sgSubst a)) t = subst (consSubst σ (subst σ a)) t := by
  apply substVar_to_subst
  intro x
  cases x <;> rfl

theorem wk1_tailId (t : Term) : wk1 t = subst (tailSubst idSubst) t := by
  unfold wk1
  exact (subst_id (wk (.step .id) t)).symm.trans (subst_wk (ρ := .step .id) t)

theorem wk_beta_doubleSubst {ρ : Wk} (t u v : Term) :
    wk ρ (subst2 t u v) = subst2 (wk (.lift (.lift ρ)) t) (wk ρ u) (wk ρ v) := by
  unfold subst2
  rw [wk_subst t, subst_wk t]
  apply substVar_to_subst
  intro x
  cases x with
  | zero => rfl
  | succ x =>
      cases x <;> rfl

theorem doubleSubstComp (t u v : Term) (σ : Subst) :
    subst2 (subst (liftSubst (liftSubst σ)) t) u v =
      subst (consSubst (consSubst σ u) v) t := by
  unfold subst2
  rw [substCompEq t]
  apply substVar_to_subst
  intro x
  cases x with
  | zero => rfl
  | succ x =>
      cases x with
      | zero => rfl
      | succ x =>
          dsimp [compSubst, consSubst, sgSubst, idSubst, liftSubst]
          rw [subst_consSubst_wk1, subst_consSubst_wk1]
          exact subst_id (σ x)

theorem subst2_subst_fusion (t u v : Term) (σ : Subst) :
    subst σ (subst2 t u v) =
      subst (consSubst (consSubst σ (subst σ u)) (subst σ v)) t := by
  unfold subst2
  rw [substCompEq t]
  apply substVar_to_subst
  intro x
  cases x with
  | zero => rfl
  | succ x =>
      cases x <;> rfl

theorem subst2_subst_commute (t u v : Term) (σ : Subst) :
    subst σ (subst2 t u v) =
      subst2 (subst (liftSubst (liftSubst σ)) t) (subst σ u) (subst σ v) :=
  (subst2_subst_fusion t u v σ).trans (doubleSubstComp t (subst σ u) (subst σ v) σ).symm

theorem subst2_eq_subst0_wk1 (t u v : Term) :
    subst2 t u v = subst0 (subst0 t (wk1 v)) u := by
  unfold subst2 subst0
  rw [substCompEq t]
  apply substVar_to_subst
  intro x
  cases x with
  | zero => exact (subst_sgSubst_wk1 u v).symm
  | succ x =>
      cases x <;> rfl

theorem id_eq_subst0_wk1 (A t u : Term) :
    Term.id A t u = subst0 (.id (wk1 A) (wk1 t) (.var 0)) u := by
  unfold subst0
  dsimp [subst, consSubst]
  rw [subst_consSubst_wk1, subst_id, subst_consSubst_wk1, subst_id]

theorem wk1_liftSubst (σ : Subst) (t : Term) :
    subst (liftSubst σ) (wk1 t) = wk1 (subst σ t) := by
  unfold wk1
  rw [subst_wk t, wk_subst t]
  rfl

theorem id_wk1_wk1_0_liftSubst (σ : Subst) (A t : Term) :
    subst (liftSubst σ) (.id (wk1 A) (wk1 t) (.var 0)) =
      .id (wk1 (subst σ A)) (wk1 (subst σ t)) (.var 0) := by
  dsimp [subst, liftSubst]
  rw [wk1_liftSubst, wk1_liftSubst]

theorem id_wk1_wk1_0_wk_lift (ρ : Wk) (A t : Term) :
    wk (.lift ρ) (.id (wk1 A) (wk1 t) (.var 0)) =
      .id (wk1 (wk ρ A)) (wk1 (wk ρ t)) (.var 0) := by
  dsimp [wk, wkVar]
  rw [← wk1_wk_eq_lift_wk1 ρ A, ← wk1_wk_eq_lift_wk1 ρ t]

theorem subst_consSubst_id_wk1 (σ : Subst) (u A t : Term) :
    subst (consSubst σ u) (.id (wk1 A) (wk1 t) (.var 0)) =
      .id (subst σ A) (subst σ t) u := by
  dsimp [subst, consSubst]
  rw [subst_consSubst_wk1, subst_consSubst_wk1]

end LogrelMLTT
