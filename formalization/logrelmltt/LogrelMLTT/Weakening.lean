/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Typed/Weakening.agda (Lemma 2.7 of POPL 2018).
-/
import LogrelMLTT.UntypedProperties
import LogrelMLTT.Judgments

namespace LogrelMLTT

/-- Typed weakening relation `ρ ∷ Δ ⊆ Γ` on newest-first contexts. -/
inductive WkCtx : Wk → Context → Context → Prop where
  | id {Γ} : WkCtx .id Γ Γ
  | step {Γ Δ A ρ} : WkCtx ρ Δ Γ → WkCtx (.step ρ) (A :: Δ) Γ
  | lift {Γ Δ A ρ} : WkCtx ρ Δ Γ → WkCtx (.lift ρ) (wk ρ A :: Δ) (A :: Γ)

/-- Composition of typed weakenings (`_•ₜ_`). -/
theorem WkCtx.comp {ρ ρ' : Wk} {Γ Δ Δ' : Context}
    (h₁ : WkCtx ρ Γ Δ) (h₂ : WkCtx ρ' Δ Δ') : WkCtx (compWk ρ ρ') Γ Δ' := by
  induction h₁ generalizing ρ' Δ' with
  | id => exact h₂
  | step h₁ ih => exact .step (ih h₂)
  | @lift Δ₀ Γ₀ B ρ₀ h₁ ih =>
      cases h₂ with
      | id => exact .lift h₁
      | step h₂ => exact .step (ih h₂)
      | @lift Δ'₀ _ A ρ'₀ h₂ =>
          have hcomp : WkCtx (.lift (compWk ρ₀ ρ'₀)) (wk (compWk ρ₀ ρ'₀) A :: Γ₀) (A :: Δ'₀) :=
            .lift (ih h₂)
          rw [← wk_comp ρ₀ ρ'₀ A] at hcomp
          exact hcomp

/-- Weakening of context membership (`wkIndex`). -/
theorem wkIndex {Γ Δ : Context} {n : Nat} {A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (_hΔ : CtxWf Δ) (hm : Member n A Γ) :
    Member (wkVar ρ n) (wk ρ A) Δ := by
  induction hρ generalizing n A with
  | id =>
      rw [wk_id]
      exact hm
  | @step Γ₀ Δ₀ B ρ₀ hρ ih =>
      cases _hΔ with
      | cons hΔ₀ _ =>
          have h := Member.there (B := B) (ih hΔ₀ hm)
          rw [wk1_wk] at h
          exact h
  | @lift Γ₀ Δ₀ B ρ₀ hρ ih =>
      cases _hΔ with
      | cons hΔ₀ _ =>
          cases hm with
          | here =>
              have h : Member 0 (wk1 (wk ρ₀ B)) (wk ρ₀ B :: Δ₀) := .here
              rw [wk1_wk_eq_lift_wk1] at h
              exact h
          | there hm₀ =>
              have h := Member.there (B := wk ρ₀ B) (ih hΔ₀ hm₀)
              rw [wk1_wk_eq_lift_wk1] at h
              exact h

private abbrev WkTypeWfMotive (Γ : Context) (A : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → TypeWf Δ (wk ρ A)

private abbrev WkHasTypeMotive (Γ : Context) (t A : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → HasType Δ (wk ρ t) (wk ρ A)

private abbrev WkTypeEqMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → TypeEq Δ (wk ρ A) (wk ρ B)

private abbrev WkTermEqMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → TermEq Δ (wk ρ t) (wk ρ u) (wk ρ A)

private theorem wk_nat_case {Γ : Context} (_hΓ : CtxWf Γ) : WkTypeWfMotive Γ .nat :=
  fun _ hΔ ↦ .nat hΔ

private theorem wk_univ_case {Γ : Context} (_hΓ : CtxWf Γ) : WkTypeWfMotive Γ .univ :=
  fun _ hΔ ↦ .univ hΔ

private theorem wk_pi_type_case {Γ : Context} {F G : Term}
    (_hF : TypeWf Γ F) (_hG : TypeWf (F :: Γ) G)
    (ihF : WkTypeWfMotive Γ F) (ihG : WkTypeWfMotive (F :: Γ) G) :
    WkTypeWfMotive Γ (.pi F G) :=
  fun hρ hΔ ↦
    let hρF := ihF hρ hΔ
    .pi hρF (ihG (.lift hρ) (.cons hΔ hρF))

private theorem wk_fromUniv_type_case {Γ : Context} {A : Term}
    (_hA : HasType Γ A .univ) (ihA : WkHasTypeMotive Γ A .univ) :
    WkTypeWfMotive Γ A :=
  fun hρ hΔ ↦ .fromUniv (ihA hρ hΔ)

private theorem wk_nat_term_case {Γ : Context} (_hΓ : CtxWf Γ) :
    WkHasTypeMotive Γ .nat .univ :=
  fun _ hΔ ↦ .nat hΔ

private theorem wk_pi_term_case {Γ : Context} {F G : Term}
    (_hF : HasType Γ F .univ) (_hG : HasType (F :: Γ) G .univ)
    (ihF : WkHasTypeMotive Γ F .univ) (ihG : WkHasTypeMotive (F :: Γ) G .univ) :
    WkHasTypeMotive Γ (.pi F G) .univ :=
  fun hρ hΔ ↦
    let hρF := ihF hρ hΔ
    .pi hρF (ihG (.lift hρ) (.cons hΔ (.fromUniv hρF)))

private theorem wk_var_case {Γ : Context} {A : Term} {x : Nat}
    (_hΓ : CtxWf Γ) (hm : Member x A Γ) :
    WkHasTypeMotive Γ (.var x) A :=
  fun hρ hΔ ↦ .var hΔ (wkIndex hρ hΔ hm)

private theorem wk_lam_case {Γ : Context} {F G t : Term}
    (_hF : TypeWf Γ F) (_ht : HasType (F :: Γ) t G)
    (ihF : WkTypeWfMotive Γ F) (iht : WkHasTypeMotive (F :: Γ) t G) :
    WkHasTypeMotive Γ (.lam t) (.pi F G) :=
  fun hρ hΔ ↦
    let hρF := ihF hρ hΔ
    .lam hρF (iht (.lift hρ) (.cons hΔ hρF))

private theorem wk_app_case {Γ : Context} {g a F G : Term}
    (_hg : HasType Γ g (.pi F G)) (_ha : HasType Γ a F)
    (ihg : WkHasTypeMotive Γ g (.pi F G)) (iha : WkHasTypeMotive Γ a F) :
    WkHasTypeMotive Γ (.app g a) (subst0 G a) := by
  intro Δ ρ hρ hΔ
  rw [wk, wk_beta (ρ := ρ) (a := a) G]
  exact HasType.app (ihg hρ hΔ) (iha hρ hΔ)

private theorem wk_zero_case {Γ : Context} (_hΓ : CtxWf Γ) :
    WkHasTypeMotive Γ .zero .nat :=
  fun _ hΔ ↦ .zero hΔ

private theorem wk_succ_case {Γ : Context} {n : Term}
    (_hn : HasType Γ n .nat) (ihn : WkHasTypeMotive Γ n .nat) :
    WkHasTypeMotive Γ (.succ n) .nat :=
  fun hρ hΔ ↦ .succ (ihn hρ hΔ)

private theorem wk_natrec_case {Γ : Context} {G s z n : Term}
    (_hG : TypeWf (.nat :: Γ) G) (_hz : HasType Γ z (subst0 G .zero))
    (_hs : HasType Γ s (recStepType G)) (_hn : HasType Γ n .nat)
    (ihG : WkTypeWfMotive (.nat :: Γ) G)
    (ihz : WkHasTypeMotive Γ z (subst0 G .zero))
    (ihs : WkHasTypeMotive Γ s (recStepType G))
    (ihn : WkHasTypeMotive Γ n .nat) :
    WkHasTypeMotive Γ (.natrec G z s n) (subst0 G n) := by
  intro Δ ρ hρ hΔ
  have hρG : TypeWf (.nat :: Δ) (wk (.lift ρ) G) :=
    ihG (WkCtx.lift (A := .nat) hρ) (.cons hΔ (.nat hΔ))
  have hρz : HasType Δ (wk ρ z) (subst0 (wk (.lift ρ) G) .zero) := by
    have hz' := ihz hρ hΔ
    rw [wk_beta (ρ := ρ) (a := .zero) G] at hz'
    exact hz'
  have hρs : HasType Δ (wk ρ s) (recStepType (wk (.lift ρ) G)) := by
    have hs' := ihs hρ hΔ
    rw [wk_beta_natrec ρ G] at hs'
    exact hs'
  have hρn : HasType Δ (wk ρ n) .nat := ihn hρ hΔ
  rw [wk, wk_beta (ρ := ρ) (a := n) G]
  exact HasType.natrec hρG hρz hρs hρn

private theorem wk_conv_case {Γ : Context} {t A B : Term}
    (_ht : HasType Γ t A) (_hEq : TypeEq Γ A B)
    (iht : WkHasTypeMotive Γ t A) (ihEq : WkTypeEqMotive Γ A B) :
    WkHasTypeMotive Γ t B :=
  fun hρ hΔ ↦ .conv (iht hρ hΔ) (ihEq hρ hΔ)

private theorem wk_fromUniv_eq_case {Γ : Context} {A B : Term}
    (_hEq : TermEq Γ A B .univ) (ihEq : WkTermEqMotive Γ A B .univ) :
    WkTypeEqMotive Γ A B :=
  fun hρ hΔ ↦ .fromUniv (ihEq hρ hΔ)

private theorem wk_refl_type_case {Γ : Context} {A : Term}
    (_hA : TypeWf Γ A) (ihA : WkTypeWfMotive Γ A) :
    WkTypeEqMotive Γ A A :=
  fun hρ hΔ ↦ .refl (ihA hρ hΔ)

private theorem wk_symm_type_case {Γ : Context} {A B : Term}
    (_hEq : TypeEq Γ A B) (ihEq : WkTypeEqMotive Γ A B) :
    WkTypeEqMotive Γ B A :=
  fun hρ hΔ ↦ .symm (ihEq hρ hΔ)

private theorem wk_trans_type_case {Γ : Context} {A B C : Term}
    (_h₁ : TypeEq Γ A B) (_h₂ : TypeEq Γ B C)
    (ih₁ : WkTypeEqMotive Γ A B) (ih₂ : WkTypeEqMotive Γ B C) :
    WkTypeEqMotive Γ A C :=
  fun hρ hΔ ↦ .trans (ih₁ hρ hΔ) (ih₂ hρ hΔ)

private theorem wk_pi_type_eq_case {Γ : Context} {F H G E : Term}
    (_hF : TypeWf Γ F) (_hFH : TypeEq Γ F H) (_hGE : TypeEq (F :: Γ) G E)
    (ihF : WkTypeWfMotive Γ F)
    (ihFH : WkTypeEqMotive Γ F H)
    (ihGE : WkTypeEqMotive (F :: Γ) G E) :
    WkTypeEqMotive Γ (.pi F G) (.pi H E) :=
  fun hρ hΔ ↦
    let hρF := ihF hρ hΔ
    .pi hρF (ihFH hρ hΔ) (ihGE (.lift hρ) (.cons hΔ hρF))

private theorem wk_refl_term_case {Γ : Context} {t A : Term}
    (_ht : HasType Γ t A) (iht : WkHasTypeMotive Γ t A) :
    WkTermEqMotive Γ t t A :=
  fun hρ hΔ ↦ .refl (iht hρ hΔ)

private theorem wk_symm_term_case {Γ : Context} {t u A : Term}
    (_hEq : TermEq Γ t u A) (ihEq : WkTermEqMotive Γ t u A) :
    WkTermEqMotive Γ u t A :=
  fun hρ hΔ ↦ .symm (ihEq hρ hΔ)

private theorem wk_trans_term_case {Γ : Context} {t u r A : Term}
    (_h₁ : TermEq Γ t u A) (_h₂ : TermEq Γ u r A)
    (ih₁ : WkTermEqMotive Γ t u A) (ih₂ : WkTermEqMotive Γ u r A) :
    WkTermEqMotive Γ t r A :=
  fun hρ hΔ ↦ .trans (ih₁ hρ hΔ) (ih₂ hρ hΔ)

private theorem wk_conv_term_case {Γ : Context} {A B t u : Term}
    (_hEq : TermEq Γ t u A) (_hAB : TypeEq Γ A B)
    (ihEq : WkTermEqMotive Γ t u A) (ihAB : WkTypeEqMotive Γ A B) :
    WkTermEqMotive Γ t u B :=
  fun hρ hΔ ↦ .conv (ihEq hρ hΔ) (ihAB hρ hΔ)

private theorem wk_pi_term_eq_case {Γ : Context} {E F G H : Term}
    (_hF : TypeWf Γ F) (_hFH : TermEq Γ F H .univ) (_hGE : TermEq (F :: Γ) G E .univ)
    (ihF : WkTypeWfMotive Γ F)
    (ihFH : WkTermEqMotive Γ F H .univ)
    (ihGE : WkTermEqMotive (F :: Γ) G E .univ) :
    WkTermEqMotive Γ (.pi F G) (.pi H E) .univ :=
  fun hρ hΔ ↦
    let hρF := ihF hρ hΔ
    .pi hρF (ihFH hρ hΔ) (ihGE (.lift hρ) (.cons hΔ hρF))

private theorem wk_app_term_eq_case {Γ : Context} {a b f g F G : Term}
    (_hfg : TermEq Γ f g (.pi F G)) (_hab : TermEq Γ a b F)
    (ihfg : WkTermEqMotive Γ f g (.pi F G))
    (ihab : WkTermEqMotive Γ a b F) :
    WkTermEqMotive Γ (.app f a) (.app g b) (subst0 G a) := by
  intro Δ ρ hρ hΔ
  rw [wk, wk, wk_beta (ρ := ρ) (a := a) G]
  exact TermEq.app (ihfg hρ hΔ) (ihab hρ hΔ)

private theorem wk_beta_term_eq_case {Γ : Context} {a t F G : Term}
    (_hF : TypeWf Γ F) (_ht : HasType (F :: Γ) t G) (_ha : HasType Γ a F)
    (ihF : WkTypeWfMotive Γ F)
    (iht : WkHasTypeMotive (F :: Γ) t G)
    (iha : WkHasTypeMotive Γ a F) :
    WkTermEqMotive Γ (.app (.lam t) a) (subst0 t a) (subst0 G a) := by
  intro Δ ρ hρ hΔ
  let hρF := ihF hρ hΔ
  rw [wk, wk, wk_beta (ρ := ρ) (a := a) t, wk_beta (ρ := ρ) (a := a) G]
  exact TermEq.beta hρF (iht (.lift hρ) (.cons hΔ hρF)) (iha hρ hΔ)

private theorem wk_eta_term_eq_case {Γ : Context} {f g F G : Term}
    (_hF : TypeWf Γ F) (_hf : HasType Γ f (.pi F G)) (_hg : HasType Γ g (.pi F G))
    (_hfg : TermEq (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G)
    (ihF : WkTypeWfMotive Γ F)
    (ihf : WkHasTypeMotive Γ f (.pi F G))
    (ihg : WkHasTypeMotive Γ g (.pi F G))
    (ihfg : WkTermEqMotive (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G) :
    WkTermEqMotive Γ f g (.pi F G) := by
  intro Δ ρ hρ hΔ
  let hρF := ihF hρ hΔ
  have hfg' : TermEq (wk ρ F :: Δ)
      (.app (wk (.lift ρ) (wk1 f)) (.var 0))
      (.app (wk (.lift ρ) (wk1 g)) (.var 0))
      (wk (.lift ρ) G) :=
    ihfg (.lift hρ) (.cons hΔ hρF)
  rw [← wk1_wk_eq_lift_wk1 ρ f, ← wk1_wk_eq_lift_wk1 ρ g] at hfg'
  exact TermEq.eta hρF (ihf hρ hΔ) (ihg hρ hΔ) hfg'

private theorem wk_succ_term_eq_case {Γ : Context} {m n : Term}
    (_hmn : TermEq Γ m n .nat) (ihmn : WkTermEqMotive Γ m n .nat) :
    WkTermEqMotive Γ (.succ m) (.succ n) .nat :=
  fun hρ hΔ ↦ .succ (ihmn hρ hΔ)

private theorem wk_natrec_term_eq_case {Γ : Context} {z z' s s' n n' F F' : Term}
    (_hFF' : TypeEq (.nat :: Γ) F F')
    (_hzz' : TermEq Γ z z' (subst0 F .zero))
    (_hss' : TermEq Γ s s' (recStepType F))
    (_hnn' : TermEq Γ n n' .nat)
    (ihFF' : WkTypeEqMotive (.nat :: Γ) F F')
    (ihzz' : WkTermEqMotive Γ z z' (subst0 F .zero))
    (ihss' : WkTermEqMotive Γ s s' (recStepType F))
    (ihnn' : WkTermEqMotive Γ n n' .nat) :
    WkTermEqMotive Γ (.natrec F z s n) (.natrec F' z' s' n') (subst0 F n) := by
  intro Δ ρ hρ hΔ
  have hρFF' : TypeEq (.nat :: Δ) (wk (.lift ρ) F) (wk (.lift ρ) F') :=
    ihFF' (WkCtx.lift (A := .nat) hρ) (.cons hΔ (.nat hΔ))
  have hρzz' : TermEq Δ (wk ρ z) (wk ρ z') (subst0 (wk (.lift ρ) F) .zero) := by
    have h := ihzz' hρ hΔ
    rw [wk_beta (ρ := ρ) (a := .zero) F] at h
    exact h
  have hρss' : TermEq Δ (wk ρ s) (wk ρ s') (recStepType (wk (.lift ρ) F)) := by
    have h := ihss' hρ hΔ
    rw [wk_beta_natrec ρ F] at h
    exact h
  have hρnn' : TermEq Δ (wk ρ n) (wk ρ n') .nat := ihnn' hρ hΔ
  rw [wk, wk, wk_beta (ρ := ρ) (a := n) F]
  exact TermEq.natrec hρFF' hρzz' hρss' hρnn'

private theorem wk_natrecZero_term_eq_case {Γ : Context} {z s F : Term}
    (_hF : TypeWf (.nat :: Γ) F)
    (_hz : HasType Γ z (subst0 F .zero))
    (_hs : HasType Γ s (recStepType F))
    (ihF : WkTypeWfMotive (.nat :: Γ) F)
    (ihz : WkHasTypeMotive Γ z (subst0 F .zero))
    (ihs : WkHasTypeMotive Γ s (recStepType F)) :
    WkTermEqMotive Γ (.natrec F z s .zero) z (subst0 F .zero) := by
  intro Δ ρ hρ hΔ
  have hρF : TypeWf (.nat :: Δ) (wk (.lift ρ) F) :=
    ihF (WkCtx.lift (A := .nat) hρ) (.cons hΔ (.nat hΔ))
  have hρz : HasType Δ (wk ρ z) (subst0 (wk (.lift ρ) F) .zero) := by
    have h := ihz hρ hΔ
    rw [wk_beta (ρ := ρ) (a := .zero) F] at h
    exact h
  have hρs : HasType Δ (wk ρ s) (recStepType (wk (.lift ρ) F)) := by
    have h := ihs hρ hΔ
    rw [wk_beta_natrec ρ F] at h
    exact h
  rw [wk, wk_beta (ρ := ρ) (a := .zero) F]
  exact TermEq.natrecZero hρF hρz hρs

private theorem wk_natrecSucc_term_eq_case {Γ : Context} {n z s F : Term}
    (_hn : HasType Γ n .nat)
    (_hF : TypeWf (.nat :: Γ) F)
    (_hz : HasType Γ z (subst0 F .zero))
    (_hs : HasType Γ s (recStepType F))
    (ihn : WkHasTypeMotive Γ n .nat)
    (ihF : WkTypeWfMotive (.nat :: Γ) F)
    (ihz : WkHasTypeMotive Γ z (subst0 F .zero))
    (ihs : WkHasTypeMotive Γ s (recStepType F)) :
    WkTermEqMotive Γ (.natrec F z s (.succ n)) (.app (.app s n) (.natrec F z s n))
      (subst0 F (.succ n)) := by
  intro Δ ρ hρ hΔ
  have hρn : HasType Δ (wk ρ n) .nat := ihn hρ hΔ
  have hρF : TypeWf (.nat :: Δ) (wk (.lift ρ) F) :=
    ihF (WkCtx.lift (A := .nat) hρ) (.cons hΔ (.nat hΔ))
  have hρz : HasType Δ (wk ρ z) (subst0 (wk (.lift ρ) F) .zero) := by
    have h := ihz hρ hΔ
    rw [wk_beta (ρ := ρ) (a := .zero) F] at h
    exact h
  have hρs : HasType Δ (wk ρ s) (recStepType (wk (.lift ρ) F)) := by
    have h := ihs hρ hΔ
    rw [wk_beta_natrec ρ F] at h
    exact h
  rw [wk, wk_beta (ρ := ρ) (a := .succ n) F]
  exact TermEq.natrecSucc hρn hρF hρz hρs

/-- Weakening of well-formed types (`wk`, Lemma 2.7). -/
theorem wkTypeWf {Γ Δ : Context} {A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (d : TypeWf Γ A) : TypeWf Δ (wk ρ A) :=
  (TypeWf.rec (motive_1 := fun _ _ ↦ True)
    (motive_2 := fun Γ A _ ↦ WkTypeWfMotive Γ A)
    (motive_3 := fun Γ t A _ ↦ WkHasTypeMotive Γ t A)
    (motive_4 := fun Γ A B _ ↦ WkTypeEqMotive Γ A B)
    (motive_5 := fun Γ t u A _ ↦ WkTermEqMotive Γ t u A)
    trivial
    (fun _ _ _ _ ↦ trivial)
    (fun hΓ _ ↦ wk_nat_case hΓ)
    (fun hΓ _ ↦ wk_univ_case hΓ)
    (fun hF hG ihF ihG ↦ wk_pi_type_case hF hG ihF ihG)
    (fun hA ihA ↦ wk_fromUniv_type_case hA ihA)
    (fun hΓ _ ↦ wk_nat_term_case hΓ)
    (fun hF hG ihF ihG ↦ wk_pi_term_case hF hG ihF ihG)
    (fun hΓ hm _ ↦ wk_var_case hΓ hm)
    (fun hF ht ihF iht ↦ wk_lam_case hF ht ihF iht)
    (fun hg ha ihg iha ↦ wk_app_case hg ha ihg iha)
    (fun hΓ _ ↦ wk_zero_case hΓ)
    (fun hn ihn ↦ wk_succ_case hn ihn)
    (fun hG hz hs hn ihG ihz ihs ihn ↦ wk_natrec_case hG hz hs hn ihG ihz ihs ihn)
    (fun ht hEq iht ihEq ↦ wk_conv_case ht hEq iht ihEq)
    (fun hEq ihEq ↦ wk_fromUniv_eq_case hEq ihEq)
    (fun hA ihA ↦ wk_refl_type_case hA ihA)
    (fun hEq ihEq ↦ wk_symm_type_case hEq ihEq)
    (fun h₁ h₂ ih₁ ih₂ ↦ wk_trans_type_case h₁ h₂ ih₁ ih₂)
    (fun hF hFH hGE ihF ihFH ihGE ↦ wk_pi_type_eq_case hF hFH hGE ihF ihFH ihGE)
    (fun ht iht ↦ wk_refl_term_case ht iht)
    (fun hEq ihEq ↦ wk_symm_term_case hEq ihEq)
    (fun h₁ h₂ ih₁ ih₂ ↦ wk_trans_term_case h₁ h₂ ih₁ ih₂)
    (fun hEq hAB ihEq ihAB ↦ wk_conv_term_case hEq hAB ihEq ihAB)
    (fun hF hFH hGE ihF ihFH ihGE ↦ wk_pi_term_eq_case hF hFH hGE ihF ihFH ihGE)
    (fun hfg hab ihfg ihab ↦ wk_app_term_eq_case hfg hab ihfg ihab)
    (fun hF ht ha ihF iht iha ↦ wk_beta_term_eq_case hF ht ha ihF iht iha)
    (fun hF hf hg hfg ihF ihf ihg ihfg ↦ wk_eta_term_eq_case hF hf hg hfg ihF ihf ihg ihfg)
    (fun hmn ihmn ↦ wk_succ_term_eq_case hmn ihmn)
    (fun hFF' hzz' hss' hnn' ihFF' ihzz' ihss' ihnn' ↦
      wk_natrec_term_eq_case hFF' hzz' hss' hnn' ihFF' ihzz' ihss' ihnn')
    (fun hF hz hs ihF ihz ihs ↦ wk_natrecZero_term_eq_case hF hz hs ihF ihz ihs)
    (fun hn hF hz hs ihn ihF ihz ihs ↦ wk_natrecSucc_term_eq_case hn hF hz hs ihn ihF ihz ihs)
    d) hρ hΔ

/-- Weakening of well-typed terms (`wkTerm`, Lemma 2.7). -/
theorem wkHasType {Γ Δ : Context} {t A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (d : HasType Γ t A) :
    HasType Δ (wk ρ t) (wk ρ A) :=
  (HasType.rec (motive_1 := fun _ _ ↦ True)
    (motive_2 := fun Γ A _ ↦ WkTypeWfMotive Γ A)
    (motive_3 := fun Γ t A _ ↦ WkHasTypeMotive Γ t A)
    (motive_4 := fun Γ A B _ ↦ WkTypeEqMotive Γ A B)
    (motive_5 := fun Γ t u A _ ↦ WkTermEqMotive Γ t u A)
    trivial
    (fun _ _ _ _ ↦ trivial)
    (fun hΓ _ ↦ wk_nat_case hΓ)
    (fun hΓ _ ↦ wk_univ_case hΓ)
    (fun hF hG ihF ihG ↦ wk_pi_type_case hF hG ihF ihG)
    (fun hA ihA ↦ wk_fromUniv_type_case hA ihA)
    (fun hΓ _ ↦ wk_nat_term_case hΓ)
    (fun hF hG ihF ihG ↦ wk_pi_term_case hF hG ihF ihG)
    (fun hΓ hm _ ↦ wk_var_case hΓ hm)
    (fun hF ht ihF iht ↦ wk_lam_case hF ht ihF iht)
    (fun hg ha ihg iha ↦ wk_app_case hg ha ihg iha)
    (fun hΓ _ ↦ wk_zero_case hΓ)
    (fun hn ihn ↦ wk_succ_case hn ihn)
    (fun hG hz hs hn ihG ihz ihs ihn ↦ wk_natrec_case hG hz hs hn ihG ihz ihs ihn)
    (fun ht hEq iht ihEq ↦ wk_conv_case ht hEq iht ihEq)
    (fun hEq ihEq ↦ wk_fromUniv_eq_case hEq ihEq)
    (fun hA ihA ↦ wk_refl_type_case hA ihA)
    (fun hEq ihEq ↦ wk_symm_type_case hEq ihEq)
    (fun h₁ h₂ ih₁ ih₂ ↦ wk_trans_type_case h₁ h₂ ih₁ ih₂)
    (fun hF hFH hGE ihF ihFH ihGE ↦ wk_pi_type_eq_case hF hFH hGE ihF ihFH ihGE)
    (fun ht iht ↦ wk_refl_term_case ht iht)
    (fun hEq ihEq ↦ wk_symm_term_case hEq ihEq)
    (fun h₁ h₂ ih₁ ih₂ ↦ wk_trans_term_case h₁ h₂ ih₁ ih₂)
    (fun hEq hAB ihEq ihAB ↦ wk_conv_term_case hEq hAB ihEq ihAB)
    (fun hF hFH hGE ihF ihFH ihGE ↦ wk_pi_term_eq_case hF hFH hGE ihF ihFH ihGE)
    (fun hfg hab ihfg ihab ↦ wk_app_term_eq_case hfg hab ihfg ihab)
    (fun hF ht ha ihF iht iha ↦ wk_beta_term_eq_case hF ht ha ihF iht iha)
    (fun hF hf hg hfg ihF ihf ihg ihfg ↦ wk_eta_term_eq_case hF hf hg hfg ihF ihf ihg ihfg)
    (fun hmn ihmn ↦ wk_succ_term_eq_case hmn ihmn)
    (fun hFF' hzz' hss' hnn' ihFF' ihzz' ihss' ihnn' ↦
      wk_natrec_term_eq_case hFF' hzz' hss' hnn' ihFF' ihzz' ihss' ihnn')
    (fun hF hz hs ihF ihz ihs ↦ wk_natrecZero_term_eq_case hF hz hs ihF ihz ihs)
    (fun hn hF hz hs ihn ihF ihz ihs ↦ wk_natrecSucc_term_eq_case hn hF hz hs ihn ihF ihz ihs)
    d) hρ hΔ

/-- Weakening of type equality (`wkEq`, Lemma 2.7). -/
theorem wkTypeEq {Γ Δ : Context} {A B : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (d : TypeEq Γ A B) :
    TypeEq Δ (wk ρ A) (wk ρ B) :=
  (TypeEq.rec (motive_1 := fun _ _ ↦ True)
    (motive_2 := fun Γ A _ ↦ WkTypeWfMotive Γ A)
    (motive_3 := fun Γ t A _ ↦ WkHasTypeMotive Γ t A)
    (motive_4 := fun Γ A B _ ↦ WkTypeEqMotive Γ A B)
    (motive_5 := fun Γ t u A _ ↦ WkTermEqMotive Γ t u A)
    trivial
    (fun _ _ _ _ ↦ trivial)
    (fun hΓ _ ↦ wk_nat_case hΓ)
    (fun hΓ _ ↦ wk_univ_case hΓ)
    (fun hF hG ihF ihG ↦ wk_pi_type_case hF hG ihF ihG)
    (fun hA ihA ↦ wk_fromUniv_type_case hA ihA)
    (fun hΓ _ ↦ wk_nat_term_case hΓ)
    (fun hF hG ihF ihG ↦ wk_pi_term_case hF hG ihF ihG)
    (fun hΓ hm _ ↦ wk_var_case hΓ hm)
    (fun hF ht ihF iht ↦ wk_lam_case hF ht ihF iht)
    (fun hg ha ihg iha ↦ wk_app_case hg ha ihg iha)
    (fun hΓ _ ↦ wk_zero_case hΓ)
    (fun hn ihn ↦ wk_succ_case hn ihn)
    (fun hG hz hs hn ihG ihz ihs ihn ↦ wk_natrec_case hG hz hs hn ihG ihz ihs ihn)
    (fun ht hEq iht ihEq ↦ wk_conv_case ht hEq iht ihEq)
    (fun hEq ihEq ↦ wk_fromUniv_eq_case hEq ihEq)
    (fun hA ihA ↦ wk_refl_type_case hA ihA)
    (fun hEq ihEq ↦ wk_symm_type_case hEq ihEq)
    (fun h₁ h₂ ih₁ ih₂ ↦ wk_trans_type_case h₁ h₂ ih₁ ih₂)
    (fun hF hFH hGE ihF ihFH ihGE ↦ wk_pi_type_eq_case hF hFH hGE ihF ihFH ihGE)
    (fun ht iht ↦ wk_refl_term_case ht iht)
    (fun hEq ihEq ↦ wk_symm_term_case hEq ihEq)
    (fun h₁ h₂ ih₁ ih₂ ↦ wk_trans_term_case h₁ h₂ ih₁ ih₂)
    (fun hEq hAB ihEq ihAB ↦ wk_conv_term_case hEq hAB ihEq ihAB)
    (fun hF hFH hGE ihF ihFH ihGE ↦ wk_pi_term_eq_case hF hFH hGE ihF ihFH ihGE)
    (fun hfg hab ihfg ihab ↦ wk_app_term_eq_case hfg hab ihfg ihab)
    (fun hF ht ha ihF iht iha ↦ wk_beta_term_eq_case hF ht ha ihF iht iha)
    (fun hF hf hg hfg ihF ihf ihg ihfg ↦ wk_eta_term_eq_case hF hf hg hfg ihF ihf ihg ihfg)
    (fun hmn ihmn ↦ wk_succ_term_eq_case hmn ihmn)
    (fun hFF' hzz' hss' hnn' ihFF' ihzz' ihss' ihnn' ↦
      wk_natrec_term_eq_case hFF' hzz' hss' hnn' ihFF' ihzz' ihss' ihnn')
    (fun hF hz hs ihF ihz ihs ↦ wk_natrecZero_term_eq_case hF hz hs ihF ihz ihs)
    (fun hn hF hz hs ihn ihF ihz ihs ↦ wk_natrecSucc_term_eq_case hn hF hz hs ihn ihF ihz ihs)
    d) hρ hΔ

/-- Weakening of term equality (`wkEqTerm`, Lemma 2.7). -/
theorem wkTermEq {Γ Δ : Context} {t u A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (d : TermEq Γ t u A) :
    TermEq Δ (wk ρ t) (wk ρ u) (wk ρ A) :=
  (TermEq.rec (motive_1 := fun _ _ ↦ True)
    (motive_2 := fun Γ A _ ↦ WkTypeWfMotive Γ A)
    (motive_3 := fun Γ t A _ ↦ WkHasTypeMotive Γ t A)
    (motive_4 := fun Γ A B _ ↦ WkTypeEqMotive Γ A B)
    (motive_5 := fun Γ t u A _ ↦ WkTermEqMotive Γ t u A)
    trivial
    (fun _ _ _ _ ↦ trivial)
    (fun hΓ _ ↦ wk_nat_case hΓ)
    (fun hΓ _ ↦ wk_univ_case hΓ)
    (fun hF hG ihF ihG ↦ wk_pi_type_case hF hG ihF ihG)
    (fun hA ihA ↦ wk_fromUniv_type_case hA ihA)
    (fun hΓ _ ↦ wk_nat_term_case hΓ)
    (fun hF hG ihF ihG ↦ wk_pi_term_case hF hG ihF ihG)
    (fun hΓ hm _ ↦ wk_var_case hΓ hm)
    (fun hF ht ihF iht ↦ wk_lam_case hF ht ihF iht)
    (fun hg ha ihg iha ↦ wk_app_case hg ha ihg iha)
    (fun hΓ _ ↦ wk_zero_case hΓ)
    (fun hn ihn ↦ wk_succ_case hn ihn)
    (fun hG hz hs hn ihG ihz ihs ihn ↦ wk_natrec_case hG hz hs hn ihG ihz ihs ihn)
    (fun ht hEq iht ihEq ↦ wk_conv_case ht hEq iht ihEq)
    (fun hEq ihEq ↦ wk_fromUniv_eq_case hEq ihEq)
    (fun hA ihA ↦ wk_refl_type_case hA ihA)
    (fun hEq ihEq ↦ wk_symm_type_case hEq ihEq)
    (fun h₁ h₂ ih₁ ih₂ ↦ wk_trans_type_case h₁ h₂ ih₁ ih₂)
    (fun hF hFH hGE ihF ihFH ihGE ↦ wk_pi_type_eq_case hF hFH hGE ihF ihFH ihGE)
    (fun ht iht ↦ wk_refl_term_case ht iht)
    (fun hEq ihEq ↦ wk_symm_term_case hEq ihEq)
    (fun h₁ h₂ ih₁ ih₂ ↦ wk_trans_term_case h₁ h₂ ih₁ ih₂)
    (fun hEq hAB ihEq ihAB ↦ wk_conv_term_case hEq hAB ihEq ihAB)
    (fun hF hFH hGE ihF ihFH ihGE ↦ wk_pi_term_eq_case hF hFH hGE ihF ihFH ihGE)
    (fun hfg hab ihfg ihab ↦ wk_app_term_eq_case hfg hab ihfg ihab)
    (fun hF ht ha ihF iht iha ↦ wk_beta_term_eq_case hF ht ha ihF iht iha)
    (fun hF hf hg hfg ihF ihf ihg ihfg ↦ wk_eta_term_eq_case hF hf hg hfg ihF ihf ihg ihfg)
    (fun hmn ihmn ↦ wk_succ_term_eq_case hmn ihmn)
    (fun hFF' hzz' hss' hnn' ihFF' ihzz' ihss' ihnn' ↦
      wk_natrec_term_eq_case hFF' hzz' hss' hnn' ihFF' ihzz' ihss' ihnn')
    (fun hF hz hs ihF ihz ihs ↦ wk_natrecZero_term_eq_case hF hz hs ihF ihz ihs)
    (fun hn hF hz hs ihn ihF ihz ihs ↦ wk_natrecSucc_term_eq_case hn hF hz hs ihn ihF ihz ihs)
    d) hρ hΔ

/-- Weakening of single-step term reduction (`wkRedTerm`). -/
theorem wkStep {Γ Δ : Context} {t u A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (d : Step Γ t u A) :
    Step Δ (wk ρ t) (wk ρ u) (wk ρ A) := by
  induction d with
  | conv hStep hEq ih => exact .conv ih (wkTypeEq hρ hΔ hEq)
  | @app A B t u a _ ha ih =>
      rw [wk, wk, wk_beta (ρ := ρ) (a := a) B]
      exact Step.app ih (wkHasType hρ hΔ ha)
  | @beta A B a t hA ht ha =>
      let hρA := wkTypeWf hρ hΔ hA
      rw [wk, wk, wk_beta (ρ := ρ) (a := a) t, wk_beta (ρ := ρ) (a := a) B]
      exact Step.beta hρA (wkHasType (.lift hρ) (.cons hΔ hρA) ht) (wkHasType hρ hΔ ha)
  | @natrec z s n n' F hF hz hs _ ih =>
      have hρF : TypeWf (.nat :: Δ) (wk (.lift ρ) F) :=
        wkTypeWf (WkCtx.lift (A := .nat) hρ) (.cons hΔ (.nat hΔ)) hF
      have hρz : HasType Δ (wk ρ z) (subst0 (wk (.lift ρ) F) .zero) := by
        have h := wkHasType hρ hΔ hz
        rw [wk_beta (ρ := ρ) (a := .zero) F] at h
        exact h
      have hρs : HasType Δ (wk ρ s) (recStepType (wk (.lift ρ) F)) := by
        have h := wkHasType hρ hΔ hs
        rw [wk_beta_natrec ρ F] at h
        exact h
      rw [wk, wk, wk_beta (ρ := ρ) (a := n) F]
      exact Step.natrec hρF hρz hρs ih
  | @natrecZero z s F hF hz hs =>
      have hρF : TypeWf (.nat :: Δ) (wk (.lift ρ) F) :=
        wkTypeWf (WkCtx.lift (A := .nat) hρ) (.cons hΔ (.nat hΔ)) hF
      have hρz : HasType Δ (wk ρ z) (subst0 (wk (.lift ρ) F) .zero) := by
        have h := wkHasType hρ hΔ hz
        rw [wk_beta (ρ := ρ) (a := .zero) F] at h
        exact h
      have hρs : HasType Δ (wk ρ s) (recStepType (wk (.lift ρ) F)) := by
        have h := wkHasType hρ hΔ hs
        rw [wk_beta_natrec ρ F] at h
        exact h
      rw [wk, wk_beta (ρ := ρ) (a := .zero) F]
      exact Step.natrecZero hρF hρz hρs
  | @natrecSucc n z s F hn hF hz hs =>
      have hρn : HasType Δ (wk ρ n) .nat := wkHasType hρ hΔ hn
      have hρF : TypeWf (.nat :: Δ) (wk (.lift ρ) F) :=
        wkTypeWf (WkCtx.lift (A := .nat) hρ) (.cons hΔ (.nat hΔ)) hF
      have hρz : HasType Δ (wk ρ z) (subst0 (wk (.lift ρ) F) .zero) := by
        have h := wkHasType hρ hΔ hz
        rw [wk_beta (ρ := ρ) (a := .zero) F] at h
        exact h
      have hρs : HasType Δ (wk ρ s) (recStepType (wk (.lift ρ) F)) := by
        have h := wkHasType hρ hΔ hs
        rw [wk_beta_natrec ρ F] at h
        exact h
      rw [wk, wk_beta (ρ := ρ) (a := .succ n) F]
      exact Step.natrecSucc hρn hρF hρz hρs

/-- Weakening of single-step type reduction (`wkRed`). -/
theorem wkTypeStep {Γ Δ : Context} {A B : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) :
    TypeStep Γ A B → TypeStep Δ (wk ρ A) (wk ρ B)
  | .fromUniv hStep => .fromUniv (wkStep hρ hΔ hStep)

/-- Weakening of multi-step type reduction (`wkRed*`). -/
theorem wkTypeStar {Γ Δ : Context} {A B : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) :
    TypeStar Γ A B → TypeStar Δ (wk ρ A) (wk ρ B)
  | .refl hA => .refl (wkTypeWf hρ hΔ hA)
  | .step h₁ h₂ => .step (wkTypeStep hρ hΔ h₁) (wkTypeStar hρ hΔ h₂)

/-- Weakening of multi-step term reduction (`wkRed*Term`). -/
theorem wkStar {Γ Δ : Context} {t u A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) :
    Star Γ t u A → Star Δ (wk ρ t) (wk ρ u) (wk ρ A)
  | .refl ht => .refl (wkHasType hρ hΔ ht)
  | .step h₁ h₂ => .step (wkStep hρ hΔ h₁) (wkStar hρ hΔ h₂)

/-- Weakening of bundled well-formed multi-step type reduction (`wkRed:*:`). -/
theorem wkTypeStarWf {Γ Δ : Context} {A B : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (h : TypeStarWf Γ A B) :
    TypeStarWf Δ (wk ρ A) (wk ρ B) :=
  ⟨wkTypeWf hρ hΔ h.source, wkTypeWf hρ hΔ h.target, wkTypeStar hρ hΔ h.reduction⟩

/-- Weakening of bundled well-typed multi-step term reduction (`wkRed:*:Term`). -/
theorem wkStarWf {Γ Δ : Context} {t u A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (h : StarWf Γ t u A) :
    StarWf Δ (wk ρ t) (wk ρ u) (wk ρ A) :=
  ⟨wkHasType hρ hΔ h.source, wkHasType hρ hΔ h.target, wkStar hρ hΔ h.reduction⟩

end LogrelMLTT
