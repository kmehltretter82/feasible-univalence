/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Conversion/Soundness.agda,
Definition/Conversion/Stability.agda,
Definition/Conversion/Conversion.agda,
Definition/Conversion/Symmetry.agda,
Definition/Conversion/Transitivity.agda,
Definition/Conversion/Lift.agda,
Definition/Conversion/Universe.agda,
Definition/Conversion/EqRelInstance.agda,
Definition/Conversion/Consequences/Completeness.agda.
-/
import Abel2018.Consequences

namespace Abel2018

/-!
## WHNF Equality Characterization Helpers (`Definition/Typed/Consequences/Equality.agda`)
-/

/-- If `Γ ⊢ ℕ ≡ B` and `B` is in WHNF, then `B = ℕ` (`ℕ≡A`). -/
theorem nat_eq_A_whnf {Γ : Context} {B : Term}
    (h : TypeEq Γ .nat B) (hw : Whnf B) : B = .nat :=
  whnfRedStar (nat_eq_A h) hw

/-- If `Γ ⊢ K ≡ B` with `Neutral K` and `B` in WHNF, then `Neutral B` (`ne≡A`). -/
theorem ne_eq_A_whnf {Γ : Context} {K B : Term}
    (neK : Neutral K) (h : TypeEq Γ K B) (hw : Whnf B) : Neutral B := by
  rcases ne_eq_A neK h with ⟨M, D', neM⟩
  rw [whnfRedStar D'.reduction hw]
  exact neM

/-- If `Γ ⊢ Π F ▹ G ≡ B` and `B` is in WHNF, then `B = Π H ▹ E` for some `H, E` (`Π≡A`). -/
theorem pi_eq_A_whnf {Γ : Context} {F G B : Term}
    (h : TypeEq Γ (.pi F G) B) (hw : Whnf B) :
    ∃ H E, B = .pi H E := by
  rcases pi_eq_A h with ⟨H, E, D'⟩
  exact ⟨H, E, whnfRedStar D' hw⟩

/-!
## Soundness of Algorithmic Equality (`Definition/Conversion/Soundness.agda`, Lemma 4.3)
-/

/-- Soundness of `ConvNeUp` (`soundness~↑`). -/
theorem soundnessNeUp {Γ : Context} {k l A : Term} (d : ConvNeUp Γ k l A) :
    TermEq Γ k l A :=
  @ConvNeUp.rec
    (fun Γ k l A _ ↦ TermEq Γ k l A)
    (fun Γ k l A _ ↦ TermEq Γ k l A)
    (fun Γ A B _ ↦ TypeEq Γ A B)
    (fun Γ A B _ ↦ TypeEq Γ A B)
    (fun Γ t u A _ ↦ TermEq Γ t u A)
    (fun Γ t u A _ ↦ TermEq Γ t u A)
    (fun hx hxy ↦ hxy ▸ .refl hx)
    (fun _ _ ihk iht ↦ .app ihk iht)
    (fun _ _ _ _ ihFG ihab ihhg ihkl ↦ .natrec ihFG ihab ihhg ihkl)
    (fun D _ _ ih ↦ .conv ih (subsetStar D))
    (fun DA DB _ _ _ ih ↦ .trans (subsetStar DA) (.trans ih (.symm (subsetStar DB))))
    (fun hΓ ↦ .refl (.univ hΓ))
    (fun hΓ ↦ .refl (.nat hΓ))
    (fun _ ih ↦ .fromUniv ih)
    (fun hF _ _ ihFH ihGE ↦ .pi hF ihFH ihGE)
    (fun DA dt du _ _ _ _ ih ↦
      .conv (.trans (subsetStarTerm dt) (.trans ih (.symm (subsetStarTerm du))))
        (.symm (subsetStar DA)))
    (fun _ ih ↦ ih)
    (fun hk _ _ hkl ihkl ↦
      let ⟨_, neK, _⟩ := neConvNeDown hkl
      let ⟨_, hkM, _⟩ := syntacticEqTerm ihkl
      .conv ihkl (neTypeEq neK hkM hk))
    (fun hA _ _ ih ↦ inverseUnivEq hA ih)
    (fun hΓ ↦ .refl (.zero hΓ))
    (fun _ ih ↦ .succ ih)
    (fun hF hf hg _ _ _ ih ↦ .eta hF hf hg ih)
    Γ k l A d

/-- Soundness of `ConvNeDown` (`soundness~↓`). -/
theorem soundnessNeDown {Γ : Context} {k l A : Term} :
    ConvNeDown Γ k l A → TermEq Γ k l A
  | .mk D _ hkl => .conv (soundnessNeUp hkl) (subsetStar D)

/-- Soundness of `ConvTypeDown` (`soundnessConv↓`). -/
theorem soundnessConvDown {Γ : Context} {A B : Term} (d : ConvTypeDown Γ A B) :
    TypeEq Γ A B :=
  @ConvTypeDown.rec
    (fun Γ k l A _ ↦ TermEq Γ k l A)
    (fun Γ k l A _ ↦ TermEq Γ k l A)
    (fun Γ A B _ ↦ TypeEq Γ A B)
    (fun Γ A B _ ↦ TypeEq Γ A B)
    (fun Γ t u A _ ↦ TermEq Γ t u A)
    (fun Γ t u A _ ↦ TermEq Γ t u A)
    (fun hx hxy ↦ hxy ▸ .refl hx)
    (fun _ _ ihk iht ↦ .app ihk iht)
    (fun _ _ _ _ ihFG ihab ihhg ihkl ↦ .natrec ihFG ihab ihhg ihkl)
    (fun D _ _ ih ↦ .conv ih (subsetStar D))
    (fun DA DB _ _ _ ih ↦ .trans (subsetStar DA) (.trans ih (.symm (subsetStar DB))))
    (fun hΓ ↦ .refl (.univ hΓ))
    (fun hΓ ↦ .refl (.nat hΓ))
    (fun _ ih ↦ .fromUniv ih)
    (fun hF _ _ ihFH ihGE ↦ .pi hF ihFH ihGE)
    (fun DA dt du _ _ _ _ ih ↦
      .conv (.trans (subsetStarTerm dt) (.trans ih (.symm (subsetStarTerm du))))
        (.symm (subsetStar DA)))
    (fun _ ih ↦ ih)
    (fun hk _ _ hkl ihkl ↦
      let ⟨_, neK, _⟩ := neConvNeDown hkl
      let ⟨_, hkM, _⟩ := syntacticEqTerm ihkl
      .conv ihkl (neTypeEq neK hkM hk))
    (fun hA _ _ ih ↦ inverseUnivEq hA ih)
    (fun hΓ ↦ .refl (.zero hΓ))
    (fun _ ih ↦ .succ ih)
    (fun hF hf hg _ _ _ ih ↦ .eta hF hf hg ih)
    Γ A B d

/-- Soundness of `ConvTypeUp` (`soundnessConv↑`, Lemma 4.3). -/
theorem soundnessConvUp {Γ : Context} {A B : Term} :
    ConvTypeUp Γ A B → TypeEq Γ A B
  | .mk DA DB _ _ hAB =>
      .trans (subsetStar DA) (.trans (soundnessConvDown hAB) (.symm (subsetStar DB)))

/-- Soundness of `ConvTermDown` (`soundnessConv↓Term`). -/
theorem soundnessConvDownTerm {Γ : Context} {t u A : Term} (d : ConvTermDown Γ t u A) :
    TermEq Γ t u A :=
  @ConvTermDown.rec
    (fun Γ k l A _ ↦ TermEq Γ k l A)
    (fun Γ k l A _ ↦ TermEq Γ k l A)
    (fun Γ A B _ ↦ TypeEq Γ A B)
    (fun Γ A B _ ↦ TypeEq Γ A B)
    (fun Γ t u A _ ↦ TermEq Γ t u A)
    (fun Γ t u A _ ↦ TermEq Γ t u A)
    (fun hx hxy ↦ hxy ▸ .refl hx)
    (fun _ _ ihk iht ↦ .app ihk iht)
    (fun _ _ _ _ ihFG ihab ihhg ihkl ↦ .natrec ihFG ihab ihhg ihkl)
    (fun D _ _ ih ↦ .conv ih (subsetStar D))
    (fun DA DB _ _ _ ih ↦ .trans (subsetStar DA) (.trans ih (.symm (subsetStar DB))))
    (fun hΓ ↦ .refl (.univ hΓ))
    (fun hΓ ↦ .refl (.nat hΓ))
    (fun _ ih ↦ .fromUniv ih)
    (fun hF _ _ ihFH ihGE ↦ .pi hF ihFH ihGE)
    (fun DA dt du _ _ _ _ ih ↦
      .conv (.trans (subsetStarTerm dt) (.trans ih (.symm (subsetStarTerm du))))
        (.symm (subsetStar DA)))
    (fun _ ih ↦ ih)
    (fun hk _ _ hkl ihkl ↦
      let ⟨_, neK, _⟩ := neConvNeDown hkl
      let ⟨_, hkM, _⟩ := syntacticEqTerm ihkl
      .conv ihkl (neTypeEq neK hkM hk))
    (fun hA _ _ ih ↦ inverseUnivEq hA ih)
    (fun hΓ ↦ .refl (.zero hΓ))
    (fun _ ih ↦ .succ ih)
    (fun hF hf hg _ _ _ ih ↦ .eta hF hf hg ih)
    Γ t u A d

/-- Soundness of `ConvTermUp` (`soundnessConv↑Term`, Lemma 4.3). -/
theorem soundnessConvUpTerm {Γ : Context} {t u A : Term} :
    ConvTermUp Γ t u A → TermEq Γ t u A
  | .mk DA dt du _ _ _ htu =>
      .conv (.trans (subsetStarTerm dt) (.trans (soundnessConvDownTerm htu) (.symm (subsetStarTerm du))))
        (.symm (subsetStar DA))

/-!
## Context Conversion and Stability (`Definition/Conversion/Stability.agda`)
-/

/-- Judgmental equality of contexts (`⊢ Γ ≡ Δ`). -/
inductive CtxEq : Context → Context → Prop where
  | nil : CtxEq [] []
  | cons {Γ Δ : Context} {A B : Term} :
      CtxEq Γ Δ → TypeEq Γ A B → CtxEq (A :: Γ) (B :: Δ)

/-- Syntactic validity and identity conversion substitution for `CtxEq` (`contextConvSubst`). -/
theorem contextConvSubst {Γ Δ : Context} (h : CtxEq Γ Δ) :
    CtxWf Γ ∧ CtxWf Δ ∧ SubstWf Δ idSubst Γ := by
  induction h with
  | nil => exact ⟨.nil, .nil, .nil⟩
  | @cons Γ Δ A B _ hAB ih =>
      rcases ih with ⟨wfΓ, wfΔ, hσ⟩
      have ⟨wfA, wfB⟩ := syntacticEq hAB
      have wfB_Δ : TypeWf Δ B := by
        have q := substitution wfB hσ wfΔ
        rwa [subst_id] at q
      have hBA_Δ : TypeEq Δ B A := by
        have q := substitutionEq (.symm hAB) (substRefl hσ) wfΔ
        rwa [subst_id, subst_id] at q
      have wfΔB : CtxWf (B :: Δ) := .cons wfΔ wfB_Δ
      have hVar0 : HasType (B :: Δ) (.var 0) (wk1 B) := .var wfΔB .here
      have hEqWk : TypeEq (B :: Δ) (wk1 B) (subst (tailSubst idSubst) A) := by
        rw [← wk1_tailId A]
        exact wkTypeEq (.step .id) wfΔB hBA_Δ
      exact ⟨.cons wfΓ wfA, wfΔB,
        .cons (wk1Subst' wfΓ wfΔ wfB_Δ hσ) (.conv hVar0 hEqWk)⟩

/-- Stability of well-formed types under `CtxEq` (`stability`). -/
theorem stability {Γ Δ : Context} {A : Term} (hΓΔ : CtxEq Γ Δ) (hA : TypeWf Γ A) :
    TypeWf Δ A := by
  rcases contextConvSubst hΓΔ with ⟨_, wfΔ, hσ⟩
  have q := substitution hA hσ wfΔ
  rwa [subst_id] at q

/-- Stability of type equality under `CtxEq` (`stabilityEq`). -/
theorem stabilityEq {Γ Δ : Context} {A B : Term} (hΓΔ : CtxEq Γ Δ) (hAB : TypeEq Γ A B) :
    TypeEq Δ A B := by
  rcases contextConvSubst hΓΔ with ⟨_, wfΔ, hσ⟩
  have q := substitutionEq hAB (substRefl hσ) wfΔ
  rwa [subst_id, subst_id] at q

/-- Reflexivity of `CtxEq` (`reflConEq`). -/
theorem reflConEq {Γ : Context} (hΓ : CtxWf Γ) : CtxEq Γ Γ := by
  induction hΓ using CtxWf.indOnly with
  | nil => exact .nil
  | cons _ wfA ih => exact .cons ih (.refl wfA)

/-- Symmetry of `CtxEq` (`symConEq`). -/
theorem symConEq {Γ Δ : Context} (hΓΔ : CtxEq Γ Δ) : CtxEq Δ Γ := by
  induction hΓΔ with
  | nil => exact .nil
  | cons hΓΔ hAB ih => exact .cons ih (stabilityEq hΓΔ (.symm hAB))

/-- Transitivity of `CtxEq`. -/
theorem transConEq {Γ Δ Ε : Context} (h₁ : CtxEq Γ Δ) (h₂ : CtxEq Δ Ε) : CtxEq Γ Ε := by
  induction h₁ generalizing Ε with
  | nil => exact h₂
  | cons h₁ hAB ih =>
      cases h₂ with
      | cons h₂ hBC =>
          exact .cons (ih h₂) (.trans hAB (stabilityEq (symConEq h₁) hBC))

/-- Stability of well-typed terms under `CtxEq` (`stabilityTerm`). -/
theorem stabilityTerm {Γ Δ : Context} {t A : Term}
    (hΓΔ : CtxEq Γ Δ) (ht : HasType Γ t A) : HasType Δ t A := by
  rcases contextConvSubst hΓΔ with ⟨_, wfΔ, hσ⟩
  have q := substitutionTerm ht hσ wfΔ
  rwa [subst_id, subst_id] at q

/-- Stability of single-step term reduction under `CtxEq` (`stabilityRedTerm`). -/
theorem stabilityRedTerm {Γ Δ : Context} {t u A : Term}
    (hΓΔ : CtxEq Γ Δ) (d : Step Γ t u A) : Step Δ t u A := by
  induction d generalizing Δ with
  | conv _ hAB ih => exact .conv (ih hΓΔ) (stabilityEq hΓΔ hAB)
  | app _ ha ih => exact .app (ih hΓΔ) (stabilityTerm hΓΔ ha)
  | beta hF ht ha =>
      exact .beta (stability hΓΔ hF) (stabilityTerm (.cons hΓΔ (.refl hF)) ht)
        (stabilityTerm hΓΔ ha)
  | natrec hF hz hs _ ih =>
      rcases contextConvSubst hΓΔ with ⟨wfΓ, _, _⟩
      exact .natrec (stability (.cons hΓΔ (.refl (.nat wfΓ))) hF)
        (stabilityTerm hΓΔ hz) (stabilityTerm hΓΔ hs) (ih hΓΔ)
  | natrecZero hF hz hs =>
      rcases contextConvSubst hΓΔ with ⟨wfΓ, _, _⟩
      exact .natrecZero (stability (.cons hΓΔ (.refl (.nat wfΓ))) hF)
        (stabilityTerm hΓΔ hz) (stabilityTerm hΓΔ hs)
  | natrecSucc hn hF hz hs =>
      rcases contextConvSubst hΓΔ with ⟨wfΓ, _, _⟩
      exact .natrecSucc (stabilityTerm hΓΔ hn)
        (stability (.cons hΓΔ (.refl (.nat wfΓ))) hF)
        (stabilityTerm hΓΔ hz) (stabilityTerm hΓΔ hs)

/-- Stability of single-step type reduction under `CtxEq` (`stabilityRed`). -/
theorem stabilityRed {Γ Δ : Context} {A B : Term}
    (hΓΔ : CtxEq Γ Δ) : TypeStep Γ A B → TypeStep Δ A B
  | .fromUniv d => .fromUniv (stabilityRedTerm hΓΔ d)

/-- Stability of multi-step type reduction under `CtxEq` (`stabilityRed*`). -/
theorem stabilityRedStar {Γ Δ : Context} {A B : Term}
    (hΓΔ : CtxEq Γ Δ) (D : TypeStar Γ A B) : TypeStar Δ A B := by
  induction D with
  | refl hA => exact .refl (stability hΓΔ hA)
  | step h₁ _ ih => exact .step (stabilityRed hΓΔ h₁) ih

/-- Stability of multi-step term reduction under `CtxEq` (`stabilityRed*Term`). -/
theorem stabilityRedStarTerm {Γ Δ : Context} {t u A : Term}
    (hΓΔ : CtxEq Γ Δ) (d : Star Γ t u A) : Star Δ t u A := by
  induction d with
  | refl ht => exact .refl (stabilityTerm hΓΔ ht)
  | step h₁ _ ih => exact .step (stabilityRedTerm hΓΔ h₁) ih

private abbrev StabNeUpMotive (Γ : Context) (k l A : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvNeUp Δ k l A
private abbrev StabNeDownMotive (Γ : Context) (k l A : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvNeDown Δ k l A
private abbrev StabTypeUpMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvTypeUp Δ A B
private abbrev StabTypeDownMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvTypeDown Δ A B
private abbrev StabTermUpMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvTermUp Δ t u A
private abbrev StabTermDownMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvTermDown Δ t u A

/-- Stability of `ConvNeUp` under `CtxEq` (`stability~↑`). -/
theorem stabilityNeUp {Γ Δ : Context} {k l A : Term}
    (hΓΔ : CtxEq Γ Δ) (d : ConvNeUp Γ k l A) : ConvNeUp Δ k l A :=
  (@ConvNeUp.rec
    (fun Γ k l A _ ↦ StabNeUpMotive Γ k l A)
    (fun Γ k l A _ ↦ StabNeDownMotive Γ k l A)
    (fun Γ A B _ ↦ StabTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ StabTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ StabTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ StabTermDownMotive Γ t u A)
    (fun hx hxy _ hΓΔ ↦ .var (stabilityTerm hΓΔ hx) hxy)
    (fun _ _ ihk iht _ hΓΔ ↦ .app (ihk hΓΔ) (iht hΓΔ))
    (fun _ _ _ _ ihFG ihab ihhg ihkl _ hΓΔ ↦
      let ⟨wfΓ, _, _⟩ := contextConvSubst hΓΔ
      .natrec (ihFG (.cons hΓΔ (.refl (.nat wfΓ)))) (ihab hΓΔ) (ihhg hΓΔ) (ihkl hΓΔ))
    (fun D hw _ ih _ hΓΔ ↦ .mk (stabilityRedStar hΓΔ D) hw (ih hΓΔ))
    (fun DA DB hwA hwB _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStar hΓΔ DB) hwA hwB (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .univRefl (contextConvSubst hΓΔ).2.1)
    (fun _ _ hΓΔ ↦ .natRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .ne (ih hΓΔ))
    (fun hF _ _ ihFH ihGE _ hΓΔ ↦
      .piCong (stability hΓΔ hF) (ihFH hΓΔ) (ihGE (.cons hΓΔ (.refl hF))))
    (fun DA dt du hwB hwt hwu _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStarTerm hΓΔ dt) (stabilityRedStarTerm hΓΔ du)
        hwB hwt hwu (ih hΓΔ))
    (fun _ ih _ hΓΔ ↦ .natIns (ih hΓΔ))
    (fun hk hl neN _ ih _ hΓΔ ↦
      .neIns (stabilityTerm hΓΔ hk) (stabilityTerm hΓΔ hl) neN (ih hΓΔ))
    (fun hA hB _ ih _ hΓΔ ↦
      .univ (stabilityTerm hΓΔ hA) (stabilityTerm hΓΔ hB) (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .zeroRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .succCong (ih hΓΔ))
    (fun hF hf hg hwf hwg _ ih _ hΓΔ ↦
      .etaEq (stability hΓΔ hF) (stabilityTerm hΓΔ hf) (stabilityTerm hΓΔ hg)
        hwf hwg (ih (.cons hΓΔ (.refl hF))))
    Γ k l A d) hΓΔ

/-- Stability of `ConvNeDown` under `CtxEq` (`stability~↓`). -/
theorem stabilityNeDown {Γ Δ : Context} {k l A : Term}
    (hΓΔ : CtxEq Γ Δ) : ConvNeDown Γ k l A → ConvNeDown Δ k l A
  | .mk D hw hkl => .mk (stabilityRedStar hΓΔ D) hw (stabilityNeUp hΓΔ hkl)

/-- Stability of `ConvTypeDown` under `CtxEq` (`stabilityConv↓`). -/
theorem stabilityConvDown {Γ Δ : Context} {A B : Term}
    (hΓΔ : CtxEq Γ Δ) (d : ConvTypeDown Γ A B) : ConvTypeDown Δ A B :=
  (@ConvTypeDown.rec
    (fun Γ k l A _ ↦ StabNeUpMotive Γ k l A)
    (fun Γ k l A _ ↦ StabNeDownMotive Γ k l A)
    (fun Γ A B _ ↦ StabTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ StabTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ StabTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ StabTermDownMotive Γ t u A)
    (fun hx hxy _ hΓΔ ↦ .var (stabilityTerm hΓΔ hx) hxy)
    (fun _ _ ihk iht _ hΓΔ ↦ .app (ihk hΓΔ) (iht hΓΔ))
    (fun _ _ _ _ ihFG ihab ihhg ihkl _ hΓΔ ↦
      let ⟨wfΓ, _, _⟩ := contextConvSubst hΓΔ
      .natrec (ihFG (.cons hΓΔ (.refl (.nat wfΓ)))) (ihab hΓΔ) (ihhg hΓΔ) (ihkl hΓΔ))
    (fun D hw _ ih _ hΓΔ ↦ .mk (stabilityRedStar hΓΔ D) hw (ih hΓΔ))
    (fun DA DB hwA hwB _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStar hΓΔ DB) hwA hwB (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .univRefl (contextConvSubst hΓΔ).2.1)
    (fun _ _ hΓΔ ↦ .natRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .ne (ih hΓΔ))
    (fun hF _ _ ihFH ihGE _ hΓΔ ↦
      .piCong (stability hΓΔ hF) (ihFH hΓΔ) (ihGE (.cons hΓΔ (.refl hF))))
    (fun DA dt du hwB hwt hwu _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStarTerm hΓΔ dt) (stabilityRedStarTerm hΓΔ du)
        hwB hwt hwu (ih hΓΔ))
    (fun _ ih _ hΓΔ ↦ .natIns (ih hΓΔ))
    (fun hk hl neN _ ih _ hΓΔ ↦
      .neIns (stabilityTerm hΓΔ hk) (stabilityTerm hΓΔ hl) neN (ih hΓΔ))
    (fun hA hB _ ih _ hΓΔ ↦
      .univ (stabilityTerm hΓΔ hA) (stabilityTerm hΓΔ hB) (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .zeroRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .succCong (ih hΓΔ))
    (fun hF hf hg hwf hwg _ ih _ hΓΔ ↦
      .etaEq (stability hΓΔ hF) (stabilityTerm hΓΔ hf) (stabilityTerm hΓΔ hg)
        hwf hwg (ih (.cons hΓΔ (.refl hF))))
    Γ A B d) hΓΔ

/-- Stability of `ConvTypeUp` under `CtxEq` (`stabilityConv↑`). -/
theorem stabilityConvUp {Γ Δ : Context} {A B : Term}
    (hΓΔ : CtxEq Γ Δ) : ConvTypeUp Γ A B → ConvTypeUp Δ A B
  | .mk DA DB hwA hwB hAB =>
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStar hΓΔ DB)
        hwA hwB (stabilityConvDown hΓΔ hAB)

/-- Stability of `ConvTermDown` under `CtxEq` (`stabilityConv↓Term`). -/
theorem stabilityConvDownTerm {Γ Δ : Context} {t u A : Term}
    (hΓΔ : CtxEq Γ Δ) (d : ConvTermDown Γ t u A) : ConvTermDown Δ t u A :=
  (@ConvTermDown.rec
    (fun Γ k l A _ ↦ StabNeUpMotive Γ k l A)
    (fun Γ k l A _ ↦ StabNeDownMotive Γ k l A)
    (fun Γ A B _ ↦ StabTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ StabTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ StabTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ StabTermDownMotive Γ t u A)
    (fun hx hxy _ hΓΔ ↦ .var (stabilityTerm hΓΔ hx) hxy)
    (fun _ _ ihk iht _ hΓΔ ↦ .app (ihk hΓΔ) (iht hΓΔ))
    (fun _ _ _ _ ihFG ihab ihhg ihkl _ hΓΔ ↦
      let ⟨wfΓ, _, _⟩ := contextConvSubst hΓΔ
      .natrec (ihFG (.cons hΓΔ (.refl (.nat wfΓ)))) (ihab hΓΔ) (ihhg hΓΔ) (ihkl hΓΔ))
    (fun D hw _ ih _ hΓΔ ↦ .mk (stabilityRedStar hΓΔ D) hw (ih hΓΔ))
    (fun DA DB hwA hwB _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStar hΓΔ DB) hwA hwB (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .univRefl (contextConvSubst hΓΔ).2.1)
    (fun _ _ hΓΔ ↦ .natRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .ne (ih hΓΔ))
    (fun hF _ _ ihFH ihGE _ hΓΔ ↦
      .piCong (stability hΓΔ hF) (ihFH hΓΔ) (ihGE (.cons hΓΔ (.refl hF))))
    (fun DA dt du hwB hwt hwu _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStarTerm hΓΔ dt) (stabilityRedStarTerm hΓΔ du)
        hwB hwt hwu (ih hΓΔ))
    (fun _ ih _ hΓΔ ↦ .natIns (ih hΓΔ))
    (fun hk hl neN _ ih _ hΓΔ ↦
      .neIns (stabilityTerm hΓΔ hk) (stabilityTerm hΓΔ hl) neN (ih hΓΔ))
    (fun hA hB _ ih _ hΓΔ ↦
      .univ (stabilityTerm hΓΔ hA) (stabilityTerm hΓΔ hB) (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .zeroRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .succCong (ih hΓΔ))
    (fun hF hf hg hwf hwg _ ih _ hΓΔ ↦
      .etaEq (stability hΓΔ hF) (stabilityTerm hΓΔ hf) (stabilityTerm hΓΔ hg)
        hwf hwg (ih (.cons hΓΔ (.refl hF))))
    Γ t u A d) hΓΔ

/-- Stability of `ConvTermUp` under `CtxEq` (`stabilityConv↑Term`). -/
theorem stabilityConvUpTerm {Γ Δ : Context} {t u A : Term}
    (hΓΔ : CtxEq Γ Δ) : ConvTermUp Γ t u A → ConvTermUp Δ t u A
  | .mk DA dt du hwB hwt hwu htu =>
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStarTerm hΓΔ dt) (stabilityRedStarTerm hΓΔ du)
        hwB hwt hwu (stabilityConvDownTerm hΓΔ htu)

/-!
## Type Conversion of Algorithmic Term Equality (`Definition/Conversion/Conversion.agda`)
-/

private abbrev ConvTermUpMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {B : Term}, CtxEq Γ Δ → TypeEq Γ A B → ConvTermUp Δ t u B

private abbrev ConvTermDownMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {B : Term}, CtxEq Γ Δ → TypeEq Γ A B → Whnf B → ConvTermDown Δ t u B

/-- Conversion of `ConvTermDown` (`convConv↓Term`). -/
theorem convConvDownTerm {Γ Δ : Context} {t u A B : Term}
    (hΓΔ : CtxEq Γ Δ) (hAB : TypeEq Γ A B) (hwB : Whnf B) (d : ConvTermDown Γ t u A) :
    ConvTermDown Δ t u B :=
  (@ConvTermDown.rec
    (fun _ _ _ _ _ ↦ True)
    (fun _ _ _ _ _ ↦ True)
    (fun _ _ _ _ ↦ True)
    (fun _ _ _ _ ↦ True)
    (fun Γ t u A _ ↦ ConvTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ ConvTermDownMotive Γ t u A)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ ↦ trivial)
    (fun _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ ↦ trivial)
    -- ConvTermUp.mk
    (fun DA dt du _ hwt hwu _ ih _ _ hΓΔ hAB ↦ by
      have ⟨_, wfB⟩ := syntacticEq hAB
      rcases whNorm wfB with ⟨B', hwB', D'⟩
      have hB₁B' : TypeEq _ _ B' :=
        .trans (.symm (subsetStar DA)) (.trans hAB (subsetStar D'.reduction))
      exact .mk (stabilityRedStar hΓΔ D'.reduction)
        (stabilityRedStarTerm hΓΔ (dt.conv hB₁B'))
        (stabilityRedStarTerm hΓΔ (du.conv hB₁B'))
        hwB' hwt hwu (ih hΓΔ hB₁B' hwB'))
    -- ConvTermDown.natIns
    (fun hkl _ _ _ hΓΔ hAB hwB ↦ by
      rw [nat_eq_A_whnf hAB hwB]
      exact .natIns (stabilityNeDown hΓΔ hkl))
    -- ConvTermDown.neIns
    (fun hk hl neN hkl _ _ _ hΓΔ hAB hwB ↦ by
      have neB : Neutral _ := ne_eq_A_whnf neN hAB hwB
      exact .neIns (stabilityTerm hΓΔ (.conv hk hAB))
        (stabilityTerm hΓΔ (.conv hl hAB)) neB (stabilityNeDown hΓΔ hkl))
    -- ConvTermDown.univ
    (fun hA hB hAB_down _ _ _ hΓΔ hAB _ ↦ by
      rw [U_eq_A hAB]
      exact .univ (stabilityTerm hΓΔ hA) (stabilityTerm hΓΔ hB) (stabilityConvDown hΓΔ hAB_down))
    -- ConvTermDown.zeroRefl
    (fun _ _ _ hΓΔ hAB hwB ↦ by
      rw [nat_eq_A_whnf hAB hwB]
      exact .zeroRefl (contextConvSubst hΓΔ).2.1)
    -- ConvTermDown.succCong
    (fun hmn _ _ _ hΓΔ hAB hwB ↦ by
      rw [nat_eq_A_whnf hAB hwB]
      exact .succCong (stabilityConvUpTerm hΓΔ hmn))
    -- ConvTermDown.etaEq
    (fun _ hf hg hwf hwg _ ih _ _ hΓΔ hAB hwB ↦ by
      rcases pi_eq_A_whnf hAB hwB with ⟨F', G', hB_eq⟩
      subst hB_eq
      have ⟨hFF', hGG'⟩ := injectivity hAB
      have ⟨_, wfF'⟩ := syntacticEq hFF'
      exact .etaEq (stability hΓΔ wfF')
        (stabilityTerm hΓΔ (.conv hf hAB))
        (stabilityTerm hΓΔ (.conv hg hAB))
        hwf hwg
        (ih (.cons hΓΔ hFF') hGG'))
    Γ t u A d) hΓΔ hAB hwB

/-- Conversion of `ConvTermUp` (`convConv↑Term`). -/
theorem convConvUpTerm {Γ Δ : Context} {t u A B : Term}
    (hΓΔ : CtxEq Γ Δ) (hAB : TypeEq Γ A B) :
    ConvTermUp Γ t u A → ConvTermUp Δ t u B
  | .mk DA dt du _ hwt hwu htu => by
      have ⟨_, wfB⟩ := syntacticEq hAB
      rcases whNorm wfB with ⟨B', hwB', D'⟩
      have hB₁B' : TypeEq Γ _ B' :=
        .trans (.symm (subsetStar DA)) (.trans hAB (subsetStar D'.reduction))
      exact .mk (stabilityRedStar hΓΔ D'.reduction)
        (stabilityRedStarTerm hΓΔ (dt.conv hB₁B'))
        (stabilityRedStarTerm hΓΔ (du.conv hB₁B'))
        hwB' hwt hwu (convConvDownTerm hΓΔ hB₁B' hwB' htu)

/-- Conversion of `ConvTermUp` in the same context (`convConvTerm`). -/
theorem convConvTerm {Γ : Context} {t u A B : Term}
    (htu : ConvTermUp Γ t u A) (hAB : TypeEq Γ A B) :
    ConvTermUp Γ t u B :=
  convConvUpTerm (reflConEq (wfTypeEq hAB)) hAB htu

/-!
## Symmetry of Algorithmic Equality (`Definition/Conversion/Symmetry.agda`)
-/

private abbrev SymNeUpMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ∃ B, TypeEq Γ A B ∧ ConvNeUp Δ u t B
private abbrev SymNeDownMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ∃ B, Whnf B ∧ TypeEq Γ A B ∧ ConvNeDown Δ u t B
private abbrev SymTypeUpMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvTypeUp Δ B A
private abbrev SymTypeDownMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvTypeDown Δ B A
private abbrev SymTermUpMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvTermUp Δ u t A
private abbrev SymTermDownMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context}, CtxEq Γ Δ → ConvTermDown Δ u t A

private theorem sym_var_case {Γ : Context} {x y : Nat} {A : Term}
    (hx : HasType Γ (.var x) A) (hxy : x = y) :
    SymNeUpMotive Γ (.var x) (.var y) A := by
  intro Δ hΓΔ
  refine ⟨A, .refl (syntacticTerm hx), ?_⟩
  subst hxy
  exact .var (stabilityTerm hΓΔ hx) rfl

private theorem sym_app_case {Γ : Context} {k l t v F G : Term}
    (_hkl : ConvNeDown Γ k l (.pi F G)) (htv : ConvTermUp Γ t v F)
    (ihkl : SymNeDownMotive Γ k l (.pi F G))
    (ihtv : SymTermUpMotive Γ t v F) :
    SymNeUpMotive Γ (.app k t) (.app l v) (subst0 G t) := by
  intro Δ hΓΔ
  rcases ihkl hΓΔ with ⟨B, hwB, hAB, hlk⟩
  rcases pi_eq_A_whnf hAB hwB with ⟨F', G', hB_eq⟩
  subst hB_eq
  have ⟨hFF', hGG'⟩ := injectivity hAB
  exact ⟨subst0 G' v, substTypeEq hGG' (soundnessConvUpTerm htv),
    .app hlk (convConvTerm (ihtv hΓΔ) (stabilityEq hΓΔ hFF'))⟩

private theorem sym_natrec_case {Γ : Context} {k l h g a₀ b₀ F G : Term}
    (hFG : ConvTypeUp (.nat :: Γ) F G)
    (_hab : ConvTermUp Γ a₀ b₀ (subst0 F .zero))
    (_hhg : ConvTermUp Γ h g (recStepType F))
    (hkl : ConvNeDown Γ k l .nat)
    (ihFG : SymTypeUpMotive (.nat :: Γ) F G)
    (ihab : SymTermUpMotive Γ a₀ b₀ (subst0 F .zero))
    (ihhg : SymTermUpMotive Γ h g (recStepType F))
    (ihkl : SymNeDownMotive Γ k l .nat) :
    SymNeUpMotive Γ (.natrec F a₀ h k) (.natrec G b₀ g l) (subst0 F k) := by
  intro Δ hΓΔ
  rcases contextConvSubst hΓΔ with ⟨wfΓ, wfΔ, _⟩
  rcases ihkl hΓΔ with ⟨B, hwB, hAB, hlk⟩
  have hB_eq : B = .nat := nat_eq_A_whnf hAB hwB
  subst hB_eq
  have hFG_eq : TypeEq (.nat :: Δ) F G :=
    stabilityEq (.cons hΓΔ (.refl (.nat wfΓ))) (soundnessConvUp hFG)
  have hF0G0 : TypeEq Δ (subst0 F .zero) (subst0 G .zero) :=
    substTypeEq hFG_eq (.refl (.zero wfΔ))
  refine ⟨subst0 G l, substTypeEq (soundnessConvUp hFG) (soundnessNeDown hkl),
    .natrec (ihFG (.cons hΓΔ (.refl (.nat wfΓ))))
      (convConvTerm (ihab hΓΔ) hF0G0)
      (convConvTerm (ihhg hΓΔ) (sucCong hFG_eq))
      hlk⟩

private theorem sym_neDown_case {Γ : Context} {k l A B : Term}
    (D : TypeStar Γ A B) (_hw : Whnf B) (_hkl : ConvNeUp Γ k l A)
    (ihkl : SymNeUpMotive Γ k l A) :
    SymNeDownMotive Γ k l B := by
  intro Δ hΓΔ
  rcases ihkl hΓΔ with ⟨B₁, hAB₁, hlk⟩
  have ⟨_, wfB₁⟩ := syntacticEq hAB₁
  rcases whNorm wfB₁ with ⟨B', hwB', D'⟩
  have hBB' : TypeEq Γ B B' :=
    .trans (.symm (subsetStar D)) (.trans hAB₁ (subsetStar D'.reduction))
  exact ⟨B', hwB', hBB', .mk (stabilityRedStar hΓΔ D'.reduction) hwB' hlk⟩

private theorem sym_piCong_case {Γ : Context} {F G H E : Term}
    (_hF : TypeWf Γ F) (hFH : ConvTypeUp Γ F H) (_hGE : ConvTypeUp (F :: Γ) G E)
    (ihFH : SymTypeUpMotive Γ F H) (ihGE : SymTypeUpMotive (F :: Γ) G E) :
    SymTypeDownMotive Γ (.pi F G) (.pi H E) := by
  intro Δ hΓΔ
  have hFH_eq : TypeEq Γ F H := soundnessConvUp hFH
  have ⟨_, wfH⟩ := syntacticEq (stabilityEq hΓΔ hFH_eq)
  exact .piCong wfH (ihFH hΓΔ) (ihGE (.cons hΓΔ hFH_eq))

/-- Symmetry of `ConvNeUp` (`sym~↑`). -/
theorem symNeUp {Γ Δ : Context} {t u A : Term}
    (hΓΔ : CtxEq Γ Δ) (d : ConvNeUp Γ t u A) :
    ∃ B, TypeEq Γ A B ∧ ConvNeUp Δ u t B :=
  (@ConvNeUp.rec
    (fun Γ t u A _ ↦ SymNeUpMotive Γ t u A)
    (fun Γ t u A _ ↦ SymNeDownMotive Γ t u A)
    (fun Γ A B _ ↦ SymTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ SymTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ SymTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ SymTermDownMotive Γ t u A)
    (fun hx hxy ↦ sym_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ sym_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      sym_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ sym_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DB) (stabilityRedStar hΓΔ DA) hwB hwA (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .univRefl (contextConvSubst hΓΔ).2.1)
    (fun _ _ hΓΔ ↦ .natRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨B, _, hUB, hBA⟩
      rw [U_eq_A hUB] at hBA
      exact .ne hBA)
    (fun hF hFH hGE ihFH ihGE ↦ sym_piCong_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStarTerm hΓΔ du) (stabilityRedStarTerm hΓΔ dt)
        hwB hwu hwt (ih hΓΔ))
    (fun _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨B, hwB, hAB, hlk⟩
      rw [nat_eq_A_whnf hAB hwB] at hlk
      exact .natIns hlk)
    (fun hk hl neN _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨_, _, _, hlk⟩
      exact .neIns (stabilityTerm hΓΔ hl) (stabilityTerm hΓΔ hk) neN hlk)
    (fun hA hB _ ih _ hΓΔ ↦
      .univ (stabilityTerm hΓΔ hB) (stabilityTerm hΓΔ hA) (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .zeroRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .succCong (ih hΓΔ))
    (fun hF hf hg hwf hwg _ ih _ hΓΔ ↦
      .etaEq (stability hΓΔ hF) (stabilityTerm hΓΔ hg) (stabilityTerm hΓΔ hf)
        hwg hwf (ih (.cons hΓΔ (.refl hF))))
    Γ t u A d) hΓΔ

/-- Symmetry of `ConvNeDown` (`sym~↓`). -/
theorem symNeDown {Γ Δ : Context} {t u A : Term}
    (hΓΔ : CtxEq Γ Δ) :
    ConvNeDown Γ t u A → ∃ B, Whnf B ∧ TypeEq Γ A B ∧ ConvNeDown Δ u t B
  | .mk D hw hkl => sym_neDown_case D hw hkl (fun hΓΔ' ↦ symNeUp hΓΔ' hkl) hΓΔ

/-- Symmetry of `ConvTypeDown` (`symConv↓`). -/
theorem symConvDown {Γ Δ : Context} {A B : Term}
    (hΓΔ : CtxEq Γ Δ) (d : ConvTypeDown Γ A B) : ConvTypeDown Δ B A :=
  (@ConvTypeDown.rec
    (fun Γ t u A _ ↦ SymNeUpMotive Γ t u A)
    (fun Γ t u A _ ↦ SymNeDownMotive Γ t u A)
    (fun Γ A B _ ↦ SymTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ SymTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ SymTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ SymTermDownMotive Γ t u A)
    (fun hx hxy ↦ sym_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ sym_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      sym_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ sym_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DB) (stabilityRedStar hΓΔ DA) hwB hwA (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .univRefl (contextConvSubst hΓΔ).2.1)
    (fun _ _ hΓΔ ↦ .natRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨B, _, hUB, hBA⟩
      rw [U_eq_A hUB] at hBA
      exact .ne hBA)
    (fun hF hFH hGE ihFH ihGE ↦ sym_piCong_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStarTerm hΓΔ du) (stabilityRedStarTerm hΓΔ dt)
        hwB hwu hwt (ih hΓΔ))
    (fun _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨B, hwB, hAB, hlk⟩
      rw [nat_eq_A_whnf hAB hwB] at hlk
      exact .natIns hlk)
    (fun hk hl neN _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨_, _, _, hlk⟩
      exact .neIns (stabilityTerm hΓΔ hl) (stabilityTerm hΓΔ hk) neN hlk)
    (fun hA hB _ ih _ hΓΔ ↦
      .univ (stabilityTerm hΓΔ hB) (stabilityTerm hΓΔ hA) (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .zeroRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .succCong (ih hΓΔ))
    (fun hF hf hg hwf hwg _ ih _ hΓΔ ↦
      .etaEq (stability hΓΔ hF) (stabilityTerm hΓΔ hg) (stabilityTerm hΓΔ hf)
        hwg hwf (ih (.cons hΓΔ (.refl hF))))
    Γ A B d) hΓΔ

/-- Symmetry of `ConvTypeUp` (`symConv↑`). -/
theorem symConvUp {Γ Δ : Context} {A B : Term}
    (hΓΔ : CtxEq Γ Δ) : ConvTypeUp Γ A B → ConvTypeUp Δ B A
  | .mk DA DB hwA hwB hAB =>
      .mk (stabilityRedStar hΓΔ DB) (stabilityRedStar hΓΔ DA)
        hwB hwA (symConvDown hΓΔ hAB)

/-- Symmetry of `ConvTermDown` (`symConv↓Term`). -/
theorem symConvDownTerm {Γ Δ : Context} {t u A : Term}
    (hΓΔ : CtxEq Γ Δ) (d : ConvTermDown Γ t u A) : ConvTermDown Δ u t A :=
  (@ConvTermDown.rec
    (fun Γ t u A _ ↦ SymNeUpMotive Γ t u A)
    (fun Γ t u A _ ↦ SymNeDownMotive Γ t u A)
    (fun Γ A B _ ↦ SymTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ SymTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ SymTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ SymTermDownMotive Γ t u A)
    (fun hx hxy ↦ sym_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ sym_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      sym_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ sym_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DB) (stabilityRedStar hΓΔ DA) hwB hwA (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .univRefl (contextConvSubst hΓΔ).2.1)
    (fun _ _ hΓΔ ↦ .natRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨B, _, hUB, hBA⟩
      rw [U_eq_A hUB] at hBA
      exact .ne hBA)
    (fun hF hFH hGE ihFH ihGE ↦ sym_piCong_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu _ ih _ hΓΔ ↦
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStarTerm hΓΔ du) (stabilityRedStarTerm hΓΔ dt)
        hwB hwu hwt (ih hΓΔ))
    (fun _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨B, hwB, hAB, hlk⟩
      rw [nat_eq_A_whnf hAB hwB] at hlk
      exact .natIns hlk)
    (fun hk hl neN _ ih _ hΓΔ ↦ by
      rcases ih hΓΔ with ⟨_, _, _, hlk⟩
      exact .neIns (stabilityTerm hΓΔ hl) (stabilityTerm hΓΔ hk) neN hlk)
    (fun hA hB _ ih _ hΓΔ ↦
      .univ (stabilityTerm hΓΔ hB) (stabilityTerm hΓΔ hA) (ih hΓΔ))
    (fun _ _ hΓΔ ↦ .zeroRefl (contextConvSubst hΓΔ).2.1)
    (fun _ ih _ hΓΔ ↦ .succCong (ih hΓΔ))
    (fun hF hf hg hwf hwg _ ih _ hΓΔ ↦
      .etaEq (stability hΓΔ hF) (stabilityTerm hΓΔ hg) (stabilityTerm hΓΔ hf)
        hwg hwf (ih (.cons hΓΔ (.refl hF))))
    Γ t u A d) hΓΔ

/-- Symmetry of `ConvTermUp` (`symConv↑Term`). -/
theorem symConvUpTerm {Γ Δ : Context} {t u A : Term}
    (hΓΔ : CtxEq Γ Δ) : ConvTermUp Γ t u A → ConvTermUp Δ u t A
  | .mk DA dt du hwB hwt hwu htu =>
      .mk (stabilityRedStar hΓΔ DA) (stabilityRedStarTerm hΓΔ du)
        (stabilityRedStarTerm hΓΔ dt) hwB hwu hwt (symConvDownTerm hΓΔ htu)

/-- Symmetry of `ConvTypeUp` in the same context (`symConv`). -/
theorem symConv {Γ : Context} {A B : Term} (hAB : ConvTypeUp Γ A B) :
    ConvTypeUp Γ B A :=
  symConvUp (reflConEq (wfTypeEq (soundnessConvUp hAB))) hAB

/-- Symmetry of `ConvTermUp` in the same context (`symConvTerm`). -/
theorem symConvTerm {Γ : Context} {t u A : Term} (htu : ConvTermUp Γ t u A) :
    ConvTermUp Γ u t A :=
  symConvUpTerm (reflConEq (wfTermEq (soundnessConvUpTerm htu))) htu

/-!
## Transitivity of Algorithmic Equality (`Definition/Conversion/Transitivity.agda`)
-/

private abbrev TransNeUpMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {v B : Term}, CtxEq Γ Δ → ConvNeUp Δ u v B → ConvNeUp Γ t v A ∧ TypeEq Γ A B
private abbrev TransNeDownMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {v B : Term}, CtxEq Γ Δ → ConvNeDown Δ u v B → ConvNeDown Γ t v A ∧ TypeEq Γ A B
private abbrev TransTypeUpMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context} {C : Term}, CtxEq Γ Δ → ConvTypeUp Δ B C → ConvTypeUp Γ A C
private abbrev TransTypeDownMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context} {C : Term}, CtxEq Γ Δ → ConvTypeDown Δ B C → ConvTypeDown Γ A C
private abbrev TransTermUpMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {v B : Term}, CtxEq Γ Δ → TypeEq Γ A B → ConvTermUp Δ u v B → ConvTermUp Γ t v A
private abbrev TransTermDownMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {v B : Term}, CtxEq Γ Δ → TypeEq Γ A B → ConvTermDown Δ u v B → ConvTermDown Γ t v A

private theorem trans_var_case {Γ : Context} {x y : Nat} {A : Term}
    (hx : HasType Γ (.var x) A) (hxy : x = y) :
    TransNeUpMotive Γ (.var x) (.var y) A := by
  intro Δ v B hΓΔ huv
  generalize hy' : Term.var y = u₀ at huv
  cases huv with
  | @var _ y₀ z _ hy₀ hyz =>
      injection hy' with hy_eq
      subst hy_eq
      refine ⟨.var hx (hxy.trans hyz), ?_⟩
      have hy_Γ : HasType Γ (.var x) B := by
        rw [hxy]
        exact stabilityTerm (symConEq hΓΔ) hy₀
      exact neTypeEq (.var x) hx hy_Γ
  | app _ _ => cases hy'
  | natrec _ _ _ _ => cases hy'

private theorem trans_app_case {Γ : Context} {k l t v F G : Term}
    (_hkl : ConvNeDown Γ k l (.pi F G)) (htv : ConvTermUp Γ t v F)
    (ihkl : TransNeDownMotive Γ k l (.pi F G))
    (ihtv : TransTermUpMotive Γ t v F) :
    TransNeUpMotive Γ (.app k t) (.app l v) (subst0 G t) := by
  intro Δ w B hΓΔ hlw
  generalize hu' : Term.app l v = u₀ at hlw
  cases hlw with
  | var _ _ => cases hu'
  | @app _ l₀ m v₀ c F₁ G₁ hlm hvc =>
      injection hu' with hl_eq hv_eq
      subst hl_eq hv_eq
      rcases ihkl hΓΔ hlm with ⟨hkm, hPiEq⟩
      have ⟨hFF₁, hGG₁⟩ := injectivity hPiEq
      exact ⟨.app hkm (ihtv hΓΔ hFF₁ hvc),
        substTypeEq hGG₁ (soundnessConvUpTerm htv)⟩
  | natrec _ _ _ _ => cases hu'

private theorem trans_natrec_case {Γ : Context} {k l h g a₀ b₀ F G : Term}
    (hFG : ConvTypeUp (.nat :: Γ) F G)
    (_hab : ConvTermUp Γ a₀ b₀ (subst0 F .zero))
    (_hhg : ConvTermUp Γ h g (recStepType F))
    (hkl : ConvNeDown Γ k l .nat)
    (ihFG : TransTypeUpMotive (.nat :: Γ) F G)
    (ihab : TransTermUpMotive Γ a₀ b₀ (subst0 F .zero))
    (ihhg : TransTermUpMotive Γ h g (recStepType F))
    (ihkl : TransNeDownMotive Γ k l .nat) :
    TransNeUpMotive Γ (.natrec F a₀ h k) (.natrec G b₀ g l) (subst0 F k) := by
  intro Δ w B hΓΔ hlw
  generalize hu' : Term.natrec G b₀ g l = u₀ at hlw
  cases hlw with
  | var _ _ => cases hu'
  | app _ _ => cases hu'
  | @natrec _ l₀ m g₀ c b₁ c₀ G₀ H hGH hbc hgc hlm =>
      injection hu' with hG_eq hb_eq hg_eq hl_eq
      subst hG_eq hb_eq hg_eq hl_eq
      rcases contextConvSubst hΓΔ with ⟨wfΓ, _, _⟩
      have hFG_eq : TypeEq (.nat :: Γ) F G := soundnessConvUp hFG
      have hF0G0 : TypeEq Γ (subst0 F .zero) (subst0 G .zero) :=
        substTypeEq hFG_eq (.refl (.zero wfΓ))
      have hStepEq : TypeEq Γ (recStepType F) (recStepType G) := sucCong hFG_eq
      exact ⟨.natrec (ihFG (.cons hΓΔ (.refl (.nat wfΓ))) hGH)
          (ihab hΓΔ hF0G0 hbc) (ihhg hΓΔ hStepEq hgc) (ihkl hΓΔ hlm).1,
        substTypeEq hFG_eq (soundnessNeDown hkl)⟩

private theorem trans_neDown_case {Γ : Context} {k l A B : Term}
    (D : TypeStar Γ A B) (hw : Whnf B) (_hkl : ConvNeUp Γ k l A)
    (ihkl : TransNeUpMotive Γ k l A) :
    TransNeDownMotive Γ k l B := by
  intro Δ v B₂ hΓΔ hlv
  cases hlv with
  | mk D₁ _ hlv_up =>
      rcases ihkl hΓΔ hlv_up with ⟨hkv, hA₁A₂⟩
      exact ⟨.mk D hw hkv,
        .trans (.symm (subsetStar D))
          (.trans hA₁A₂ (subsetStar (stabilityRedStar (symConEq hΓΔ) D₁)))⟩

private theorem trans_typeUp_case {Γ : Context} {A B A' B' : Term}
    (DA : TypeStar Γ A A') (DB : TypeStar Γ B B')
    (hwA : Whnf A') (hwB : Whnf B')
    (_hAB : ConvTypeDown Γ A' B')
    (ihAB : TransTypeDownMotive Γ A' B') :
    TransTypeUpMotive Γ A B := by
  intro Δ C hΓΔ hBC
  cases hBC with
  | @mk _ _ _ A'' B'' D₁ D'' hwA'' hwB'' hA''B'' =>
      have hEq : A'' = B' :=
        whrDetStar ⟨D₁, hwA''⟩ ⟨stabilityRedStar hΓΔ DB, hwB⟩
      subst hEq
      exact .mk DA (stabilityRedStar (symConEq hΓΔ) D'') hwA hwB'' (ihAB hΓΔ hA''B'')

private theorem trans_typeDown_univ_case {Γ : Context} (hΓ : CtxWf Γ) :
    TransTypeDownMotive Γ .univ .univ := by
  intro Δ C _ hBC
  generalize hB : Term.univ = B₀ at hBC
  cases hBC with
  | univRefl _ => exact .univRefl hΓ
  | ne hne =>
      subst hB
      have ⟨_, neK, _⟩ := neConvNeDown hne
      cases neK
  | _ => cases hB

private theorem trans_typeDown_nat_case {Γ : Context} (hΓ : CtxWf Γ) :
    TransTypeDownMotive Γ .nat .nat := by
  intro Δ C _ hBC
  generalize hB : Term.nat = B₀ at hBC
  cases hBC with
  | natRefl _ => exact .natRefl hΓ
  | ne hne =>
      subst hB
      have ⟨_, neK, _⟩ := neConvNeDown hne
      cases neK
  | _ => cases hB

private theorem trans_typeDown_ne_case {Γ : Context} {K L : Term}
    (hKL : ConvNeDown Γ K L .univ) (ihKL : TransNeDownMotive Γ K L .univ) :
    TransTypeDownMotive Γ K L := by
  intro Δ C hΓΔ hLC
  have ⟨_, _, neL⟩ := neConvNeDown hKL
  cases hLC with
  | univRefl _ => cases neL
  | natRefl _ => cases neL
  | ne hLC_ne => exact .ne (ihKL hΓΔ hLC_ne).1
  | piCong _ _ _ => cases neL

private theorem trans_typeDown_pi_case {Γ : Context} {F G H E : Term}
    (hF : TypeWf Γ F) (hFH : ConvTypeUp Γ F H) (_hGE : ConvTypeUp (F :: Γ) G E)
    (ihFH : TransTypeUpMotive Γ F H) (ihGE : TransTypeUpMotive (F :: Γ) G E) :
    TransTypeDownMotive Γ (.pi F G) (.pi H E) := by
  intro Δ C hΓΔ hBC
  generalize hB : Term.pi H E = B₀ at hBC
  cases hBC with
  | ne hne =>
      subst hB
      have ⟨_, neK, _⟩ := neConvNeDown hne
      cases neK
  | piCong _ hHK hEK =>
      injection hB with hH_eq hE_eq
      subst hH_eq hE_eq
      exact .piCong hF (ihFH hΓΔ hHK) (ihGE (.cons hΓΔ (soundnessConvUp hFH)) hEK)
  | _ => cases hB

private theorem trans_termUp_case {Γ : Context} {t u A B₁ t' u' : Term}
    (DA : TypeStar Γ A B₁) (dt : Star Γ t t' B₁) (du : Star Γ u u' B₁)
    (hwB : Whnf B₁) (hwt : Whnf t') (hwu : Whnf u')
    (_htu : ConvTermDown Γ t' u' B₁)
    (ihtu : TransTermDownMotive Γ t' u' B₁) :
    TransTermUpMotive Γ t u A := by
  intro Δ v B hΓΔ hAB huv
  cases huv with
  | @mk _ _ _ _ B₂ t'' u'' D₁ d₁ d'' _ hwt'' hwu'' htu₁ =>
      have hB₁B₂ : TypeEq Γ B₁ B₂ :=
        .trans (.symm (subsetStar DA))
          (.trans hAB (subsetStar (stabilityRedStar (symConEq hΓΔ) D₁)))
      have d₁'' : Star Γ v u'' B₁ :=
        (stabilityRedStarTerm (symConEq hΓΔ) d'').conv (.symm hB₁B₂)
      have d₁' : Star Δ u u' B₂ :=
        stabilityRedStarTerm hΓΔ (du.conv hB₁B₂)
      have hEq : t'' = u' := whrDetStarTerm ⟨d₁, hwt''⟩ ⟨d₁', hwu⟩
      subst hEq
      exact .mk DA dt d₁'' hwB hwt hwu'' (ihtu hΓΔ hB₁B₂ htu₁)

private theorem trans_termDown_natIns_case {Γ : Context} {k l : Term}
    (hkl : ConvNeDown Γ k l .nat) (ihkl : TransNeDownMotive Γ k l .nat) :
    TransTermDownMotive Γ k l .nat := by
  intro Δ v B hΓΔ hAB hlv
  have ⟨_, _, neL⟩ := neConvNeDown hkl
  cases hlv with
  | natIns hlv_ne => exact .natIns (ihkl hΓΔ hlv_ne).1
  | neIns _ _ neB _ => exact False.elim (nat_ne_ne neB hAB)
  | univ _ _ _ => exact False.elim (U_ne_nat (.symm hAB))
  | zeroRefl _ => cases neL
  | succCong _ => cases neL
  | etaEq _ _ _ _ _ _ => exact False.elim (nat_ne_pi hAB)

private theorem trans_termDown_neIns_case {Γ : Context} {k l M N : Term}
    (hk : HasType Γ k N) (_hl : HasType Γ l N) (neN : Neutral N)
    (hkl : ConvNeDown Γ k l M) (ihkl : TransNeDownMotive Γ k l M) :
    TransTermDownMotive Γ k l N := by
  intro Δ v B hΓΔ hAB hlv
  have ⟨_, _, neL⟩ := neConvNeDown hkl
  cases hlv with
  | natIns _ => exact False.elim (nat_ne_ne neN (.symm hAB))
  | neIns _ hv _ hlv_ne =>
      exact .neIns hk (.conv (stabilityTerm (symConEq hΓΔ) hv) (.symm hAB))
        neN (ihkl hΓΔ hlv_ne).1
  | univ _ _ _ => exact False.elim (U_ne_ne neN (.symm hAB))
  | zeroRefl _ => cases neL
  | succCong _ => cases neL
  | etaEq _ _ _ _ _ _ => exact False.elim (pi_ne_ne neN (.symm hAB))

private theorem trans_termDown_univ_case {Γ : Context} {A B : Term}
    (hA : HasType Γ A .univ) (_hB : HasType Γ B .univ)
    (_hAB_down : ConvTypeDown Γ A B) (ihAB : TransTypeDownMotive Γ A B) :
    TransTermDownMotive Γ A B .univ := by
  intro Δ v C hΓΔ hUC hBv
  cases hBv with
  | natIns _ => exact False.elim (U_ne_nat hUC)
  | neIns _ _ neC _ => exact False.elim (U_ne_ne neC hUC)
  | univ _ hv hBv_down =>
      exact .univ hA (stabilityTerm (symConEq hΓΔ) hv) (ihAB hΓΔ hBv_down)
  | zeroRefl _ => exact False.elim (U_ne_nat hUC)
  | succCong _ => exact False.elim (U_ne_nat hUC)
  | etaEq _ _ _ _ _ _ => exact False.elim (U_ne_pi hUC)

private theorem trans_termDown_zero_case {Γ : Context} (hΓ : CtxWf Γ) :
    TransTermDownMotive Γ .zero .zero .nat := by
  intro Δ v B _ hAB hzv
  generalize hz : Term.zero = z₀ at hzv
  cases hzv with
  | natIns hne =>
      subst hz
      have ⟨_, neZ, _⟩ := neConvNeDown hne
      cases neZ
  | neIns _ _ _ hne =>
      subst hz
      have ⟨_, neZ, _⟩ := neConvNeDown hne
      cases neZ
  | univ _ _ _ => exact False.elim (U_ne_nat (.symm hAB))
  | zeroRefl _ => exact .zeroRefl hΓ
  | succCong _ => cases hz
  | etaEq _ _ _ _ _ _ => exact False.elim (nat_ne_pi hAB)

private theorem trans_termDown_succ_case {Γ : Context} {m n : Term}
    (_hmn : ConvTermUp Γ m n .nat) (ihmn : TransTermUpMotive Γ m n .nat) :
    TransTermDownMotive Γ (.succ m) (.succ n) .nat := by
  intro Δ v B hΓΔ hAB hnv
  generalize hs : Term.succ n = s₀ at hnv
  cases hnv with
  | natIns hne =>
      subst hs
      have ⟨_, neS, _⟩ := neConvNeDown hne
      cases neS
  | neIns _ _ _ hne =>
      subst hs
      have ⟨_, neS, _⟩ := neConvNeDown hne
      cases neS
  | univ _ _ _ => exact False.elim (U_ne_nat (.symm hAB))
  | zeroRefl _ => cases hs
  | succCong hnp =>
      injection hs with hn_eq
      subst hn_eq
      exact .succCong (ihmn hΓΔ hAB hnp)
  | etaEq _ _ _ _ _ _ => exact False.elim (nat_ne_pi hAB)

private theorem trans_termDown_eta_case {Γ : Context} {f g F G : Term}
    (hF : TypeWf Γ F) (hf : HasType Γ f (.pi F G)) (_hg : HasType Γ g (.pi F G))
    (hwf : Whnf f) (_hwg : Whnf g)
    (_hfg : ConvTermUp (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G)
    (ihfg : TransTermUpMotive (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G) :
    TransTermDownMotive Γ f g (.pi F G) := by
  intro Δ v B hΓΔ hAB hgv
  cases hgv with
  | natIns _ => exact False.elim (nat_ne_pi (.symm hAB))
  | neIns _ _ neB _ => exact False.elim (pi_ne_ne neB hAB)
  | univ _ _ _ => exact False.elim (U_ne_pi (.symm hAB))
  | zeroRefl _ => exact False.elim (nat_ne_pi (.symm hAB))
  | succCong _ => exact False.elim (nat_ne_pi (.symm hAB))
  | etaEq _ _ hv _ hwv hgv_up =>
      have ⟨hFF', hGG'⟩ := injectivity hAB
      exact .etaEq hF hf (.conv (stabilityTerm (symConEq hΓΔ) hv) (.symm hAB))
        hwf hwv (ihfg (.cons hΓΔ hFF') hGG' hgv_up)

/-- Transitivity of `ConvNeUp` (`trans~↑`). -/
theorem transNeUp {Γ Δ : Context} {t u v A B : Term}
    (hΓΔ : CtxEq Γ Δ) (d₁ : ConvNeUp Γ t u A) (d₂ : ConvNeUp Δ u v B) :
    ConvNeUp Γ t v A ∧ TypeEq Γ A B :=
  (@ConvNeUp.rec
    (fun Γ t u A _ ↦ TransNeUpMotive Γ t u A)
    (fun Γ t u A _ ↦ TransNeDownMotive Γ t u A)
    (fun Γ A B _ ↦ TransTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ TransTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ TransTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ TransTermDownMotive Γ t u A)
    (fun hx hxy ↦ trans_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ trans_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      trans_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ trans_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB hAB ihAB ↦ trans_typeUp_case DA DB hwA hwB hAB ihAB)
    (fun hΓ ↦ trans_typeDown_univ_case hΓ)
    (fun hΓ ↦ trans_typeDown_nat_case hΓ)
    (fun hKL ihKL ↦ trans_typeDown_ne_case hKL ihKL)
    (fun hF hFH hGE ihFH ihGE ↦ trans_typeDown_pi_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu htu ihtu ↦
      trans_termUp_case DA dt du hwB hwt hwu htu ihtu)
    (fun hkl ihkl ↦ trans_termDown_natIns_case hkl ihkl)
    (fun hk hl neN hkl ihkl ↦ trans_termDown_neIns_case hk hl neN hkl ihkl)
    (fun hA hB hAB ihAB ↦ trans_termDown_univ_case hA hB hAB ihAB)
    (fun hΓ ↦ trans_termDown_zero_case hΓ)
    (fun hmn ihmn ↦ trans_termDown_succ_case hmn ihmn)
    (fun hF hf hg hwf hwg hfg ihfg ↦
      trans_termDown_eta_case hF hf hg hwf hwg hfg ihfg)
    Γ t u A d₁) hΓΔ d₂

/-- Transitivity of `ConvNeDown` (`trans~↓`). -/
theorem transNeDown {Γ Δ : Context} {t u v A B : Term}
    (hΓΔ : CtxEq Γ Δ) (d₁ : ConvNeDown Γ t u A) (d₂ : ConvNeDown Δ u v B) :
    ConvNeDown Γ t v A ∧ TypeEq Γ A B :=
  match d₁ with
  | .mk D hw hkl => trans_neDown_case D hw hkl (fun hΓΔ' d₂' ↦ transNeUp hΓΔ' hkl d₂') hΓΔ d₂

/-- Transitivity of `ConvTypeDown` (`transConv↓`). -/
theorem transConvDown {Γ Δ : Context} {A B C : Term}
    (hΓΔ : CtxEq Γ Δ) (d₁ : ConvTypeDown Γ A B) (d₂ : ConvTypeDown Δ B C) :
    ConvTypeDown Γ A C :=
  (@ConvTypeDown.rec
    (fun Γ t u A _ ↦ TransNeUpMotive Γ t u A)
    (fun Γ t u A _ ↦ TransNeDownMotive Γ t u A)
    (fun Γ A B _ ↦ TransTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ TransTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ TransTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ TransTermDownMotive Γ t u A)
    (fun hx hxy ↦ trans_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ trans_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      trans_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ trans_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB hAB ihAB ↦ trans_typeUp_case DA DB hwA hwB hAB ihAB)
    (fun hΓ ↦ trans_typeDown_univ_case hΓ)
    (fun hΓ ↦ trans_typeDown_nat_case hΓ)
    (fun hKL ihKL ↦ trans_typeDown_ne_case hKL ihKL)
    (fun hF hFH hGE ihFH ihGE ↦ trans_typeDown_pi_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu htu ihtu ↦
      trans_termUp_case DA dt du hwB hwt hwu htu ihtu)
    (fun hkl ihkl ↦ trans_termDown_natIns_case hkl ihkl)
    (fun hk hl neN hkl ihkl ↦ trans_termDown_neIns_case hk hl neN hkl ihkl)
    (fun hA hB hAB ihAB ↦ trans_termDown_univ_case hA hB hAB ihAB)
    (fun hΓ ↦ trans_termDown_zero_case hΓ)
    (fun hmn ihmn ↦ trans_termDown_succ_case hmn ihmn)
    (fun hF hf hg hwf hwg hfg ihfg ↦
      trans_termDown_eta_case hF hf hg hwf hwg hfg ihfg)
    Γ A B d₁) hΓΔ d₂

/-- Transitivity of `ConvTypeUp` (`transConv↑`). -/
theorem transConvUp {Γ Δ : Context} {A B C : Term}
    (hΓΔ : CtxEq Γ Δ) (d₁ : ConvTypeUp Γ A B) (d₂ : ConvTypeUp Δ B C) :
    ConvTypeUp Γ A C :=
  match d₁ with
  | .mk DA DB hwA hwB hAB =>
      trans_typeUp_case DA DB hwA hwB hAB (fun hΓΔ' d₂' ↦ transConvDown hΓΔ' hAB d₂') hΓΔ d₂

/-- Transitivity of `ConvTermDown` (`transConv↓Term`). -/
theorem transConvDownTerm {Γ Δ : Context} {t u v A B : Term}
    (hΓΔ : CtxEq Γ Δ) (hAB : TypeEq Γ A B)
    (d₁ : ConvTermDown Γ t u A) (d₂ : ConvTermDown Δ u v B) :
    ConvTermDown Γ t v A :=
  (@ConvTermDown.rec
    (fun Γ t u A _ ↦ TransNeUpMotive Γ t u A)
    (fun Γ t u A _ ↦ TransNeDownMotive Γ t u A)
    (fun Γ A B _ ↦ TransTypeUpMotive Γ A B)
    (fun Γ A B _ ↦ TransTypeDownMotive Γ A B)
    (fun Γ t u A _ ↦ TransTermUpMotive Γ t u A)
    (fun Γ t u A _ ↦ TransTermDownMotive Γ t u A)
    (fun hx hxy ↦ trans_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ trans_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      trans_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ trans_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB hAB ihAB ↦ trans_typeUp_case DA DB hwA hwB hAB ihAB)
    (fun hΓ ↦ trans_typeDown_univ_case hΓ)
    (fun hΓ ↦ trans_typeDown_nat_case hΓ)
    (fun hKL ihKL ↦ trans_typeDown_ne_case hKL ihKL)
    (fun hF hFH hGE ihFH ihGE ↦ trans_typeDown_pi_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu htu ihtu ↦
      trans_termUp_case DA dt du hwB hwt hwu htu ihtu)
    (fun hkl ihkl ↦ trans_termDown_natIns_case hkl ihkl)
    (fun hk hl neN hkl ihkl ↦ trans_termDown_neIns_case hk hl neN hkl ihkl)
    (fun hA hB hAB ihAB ↦ trans_termDown_univ_case hA hB hAB ihAB)
    (fun hΓ ↦ trans_termDown_zero_case hΓ)
    (fun hmn ihmn ↦ trans_termDown_succ_case hmn ihmn)
    (fun hF hf hg hwf hwg hfg ihfg ↦
      trans_termDown_eta_case hF hf hg hwf hwg hfg ihfg)
    Γ t u A d₁) hΓΔ hAB d₂

/-- Transitivity of `ConvTermUp` (`transConv↑Term`). -/
theorem transConvUpTerm {Γ Δ : Context} {t u v A B : Term}
    (hΓΔ : CtxEq Γ Δ) (hAB : TypeEq Γ A B)
    (d₁ : ConvTermUp Γ t u A) (d₂ : ConvTermUp Δ u v B) :
    ConvTermUp Γ t v A :=
  match d₁ with
  | .mk DA dt du hwB hwt hwu htu =>
      trans_termUp_case DA dt du hwB hwt hwu htu
        (fun hΓΔ' hAB' d₂' ↦ transConvDownTerm hΓΔ' hAB' htu d₂') hΓΔ hAB d₂

/-- Transitivity of `ConvTypeUp` in the same context (`transConv`). -/
theorem transConv {Γ : Context} {A B C : Term}
    (hAB : ConvTypeUp Γ A B) (hBC : ConvTypeUp Γ B C) : ConvTypeUp Γ A C :=
  transConvUp (reflConEq (wfTypeEq (soundnessConvUp hAB))) hAB hBC

/-- Transitivity of `ConvTermUp` in the same context (`transConvTerm`). -/
theorem transConvTerm {Γ : Context} {t u v A : Term}
    (htu : ConvTermUp Γ t u A) (huv : ConvTermUp Γ u v A) : ConvTermUp Γ t v A :=
  let htu_eq := soundnessConvUpTerm htu
  transConvUpTerm (reflConEq (wfTermEq htu_eq)) (.refl (syntacticEqTerm htu_eq).1) htu huv

/-!
## Lifting of Algorithmic Equality (`Definition/Conversion/Lift.agda` & `Universe.agda`)
-/

/-- Lift `ConvTypeDown` to `ConvTypeUp` (`liftConv`). -/
theorem liftConv {Γ : Context} {A B : Term} (hAB : ConvTypeDown Γ A B) :
    ConvTypeUp Γ A B :=
  let ⟨wfA, wfB⟩ := syntacticEq (soundnessConvDown hAB)
  let ⟨hwA, hwB⟩ := whnfConvTypeDown hAB
  .mk (.refl wfA) (.refl wfB) hwA hwB hAB

/-- Lift `ConvTermDown` to `ConvTermUp` (`liftConvTerm`). -/
theorem liftConvTerm {Γ : Context} {t u A : Term} (htu : ConvTermDown Γ t u A) :
    ConvTermUp Γ t u A :=
  let ⟨wfA, wft, wfu⟩ := syntacticEqTerm (soundnessConvDownTerm htu)
  let ⟨hwA, hwt, hwu⟩ := whnfConvTermDown htu
  .mk (.refl wfA) (.refl wft) (.refl wfu) hwA hwt hwu htu

/-- Single-level step for lifting neutral equality to `ConvTermDown` and `ConvTermUp`
(`lift~toConv↓′` and `lift~toConv↑′`). -/
theorem liftNeToConv_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A' rel},
      logRelRec eqrel l l' hlt Γ A' rel →
      (∀ {t u A}, TypeStar Γ A' A → ConvNeDown Γ t u A → ConvTermDown Γ t u A) ∧
      (∀ {t u}, ConvNeUp Γ t u A' → ConvTermUp Γ t u A'))
    {Γ : Context} {A' : Term} {rel : RedRel}
    (hA' : LogRelAt eqrel l Γ A' rel) :
    (∀ {t u A}, TypeStar Γ A' A → ConvNeDown Γ t u A → ConvTermDown Γ t u A) ∧
    (∀ {t u}, ConvNeUp Γ t u A' → ConvTermUp Γ t u A') := by
  have toUp : ∀ {Δ B} (hB : TypeWf Δ B),
      (∀ {t u C}, TypeStar Δ B C → ConvNeDown Δ t u C → ConvTermDown Δ t u C) →
      ∀ {t u}, ConvNeUp Δ t u B → ConvTermUp Δ t u B := by
    intro Δ B wfB hDown t u htu
    rcases whNorm wfB with ⟨C, hwC, D⟩
    have htu_down : ConvNeDown Δ t u C := .mk D.reduction hwC htu
    have ⟨neT, neU⟩ := neConvNeUp htu
    have ⟨_, wft, wfu⟩ := syntacticEqTerm (soundnessNeDown htu_down)
    exact .mk D.reduction (.refl wft) (.refl wfu) hwC
      (.neutral neT) (.neutral neU) (hDown D.reduction htu_down)
  induction hA' with
  | @U Γ₀ _ hU =>
      have hDown : ∀ {t u A}, TypeStar Γ₀ .univ A → ConvNeDown Γ₀ t u A → ConvTermDown Γ₀ t u A := by
        intro t u A D hkl
        cases hkl with
        | mk D₁ _ k_l =>
            have hA : Term.univ = A := whnfRedStar D Whnf.univ
            subst hA
            have ⟨_, wft, wfu⟩ := syntacticEqTerm (.conv (soundnessNeUp k_l) (subsetStar D₁))
            exact .univ wft wfu (.ne (.mk D₁ Whnf.univ k_l))
      exact ⟨hDown, toUp (.univ hU.wf) hDown⟩
  | @nat Γ₀ A₀ D =>
      have hDown : ∀ {t u A}, TypeStar Γ₀ A₀ A → ConvNeDown Γ₀ t u A → ConvTermDown Γ₀ t u A := by
        intro t u A D₁ hkl
        cases hkl with
        | mk D₂ hwB k_l =>
            have hA : .nat = A := whrDetStar ⟨D.reduction, .nat⟩ ⟨D₁, hwB⟩
            subst hA
            exact .natIns (.mk D₂ .nat k_l)
      exact ⟨hDown, toUp D.source hDown⟩
  | @ne Γ₀ A₀ K neA =>
      have hDown : ∀ {t u A}, TypeStar Γ₀ A₀ A → ConvNeDown Γ₀ t u A → ConvTermDown Γ₀ t u A := by
        intro t u A D₁ hkl
        cases hkl with
        | mk D₂ hwB k_l =>
            have hA : K = A := whrDetStar ⟨neA.D.reduction, .neutral neA.neK⟩ ⟨D₁, hwB⟩
            subst hA
            have ⟨_, wft, wfu⟩ := syntacticEqTerm (soundnessNeUp k_l)
            have hAK := subsetStar D₂
            exact .neIns (.conv wft hAK) (.conv wfu hAK) neA.neK
              (.mk D₂ (.neutral neA.neK) k_l)
      exact ⟨hDown, toUp neA.D.source hDown⟩
  | @pi Γ A' F G D hF _ _ _ _ hF_ex derivF hG_ex derivG _ ihF ihG =>
      have hDown : ∀ {t u A}, TypeStar Γ A' A → ConvNeDown Γ t u A → ConvTermDown Γ t u A := by
        intro t u A D₁ hkl
        cases hkl with
        | mk D₂ hwB k_l =>
            have hA : Term.pi F G = A := whrDetStar ⟨D.reduction, .pi⟩ ⟨D₁, hwB⟩
            subst hA
            have hkl_pi : ConvNeDown Γ t u (.pi F G) := .mk D₂ .pi k_l
            have ⟨_, wft, wfu⟩ := syntacticEqTerm (soundnessNeDown hkl_pi)
            have ⟨neT, neU⟩ := neConvNeUp k_l
            have hΓ : CtxWf Γ := wfType hF
            have hΔ₁ : CtxWf (F :: Γ) := .cons hΓ hF
            have hρ₁ : WkCtx (.step .id) (F :: Γ) Γ := .step .id
            rcases hF_ex hρ₁ hΔ₁ with ⟨relF₁, hrF₁⟩
            have pF₁ : RedType eqrel l (F :: Γ) (wk (.step .id) F) :=
              ⟨relF₁, derivF hρ₁ hΔ₁ relF₁ hrF₁⟩
            have hVar0 : HasType (F :: Γ) (.var 0) (wk (.step .id) F) := .var hΔ₁ .here
            have var0_red : RedTerm pF₁ (.var 0) :=
              neuTerm pF₁ (.var 0) hVar0 (eqrel.varRefl hVar0)
            have var0_rel : RelFHasTerm _ (.step .id) (F :: Γ) (.var 0) :=
              ⟨relF₁, hrF₁, (RedTerm_of_LogRelAt (derivF hρ₁ hΔ₁ relF₁ hrF₁) pF₁).mp var0_red⟩
            rcases hG_ex hρ₁ hΔ₁ var0_rel with ⟨relG₁, hrG₁⟩
            have h00 : ConvTermUp (F :: Γ) (.var 0) (.var 0) (wk (.step .id) F) :=
              (ihF hρ₁ hΔ₁ relF₁ hrF₁).2 (.var hVar0 rfl)
            have hApp : ConvTermUp (F :: Γ)
                (.app (wk1 t) (.var 0)) (.app (wk1 u) (.var 0))
                (subst0 (wk (.lift (.step .id)) G) (.var 0)) :=
              (ihG hρ₁ hΔ₁ var0_rel relG₁ hrG₁).2
                (.app (wkConvNeDown hρ₁ hΔ₁ hkl_pi) h00)
            rw [wkSingleSubstId G] at hApp
            exact .etaEq hF wft wfu (.neutral neT) (.neutral neU) hApp
      exact ⟨hDown, toUp D.source hDown⟩
  | emb hlt hA₀ => exact ihRec _ hlt hA₀

theorem liftNeToConvAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A' : Term}
    (pA' : RedType eqrel l Γ A') :
    (∀ {t u A}, TypeStar Γ A' A → ConvNeDown Γ t u A → ConvTermDown Γ t u A) ∧
    (∀ {t u}, ConvNeUp Γ t u A' → ConvTermUp Γ t u A') := by
  rcases pA' with ⟨rel, hA'⟩
  have h0 : ∀ {Γ A' rel}, LogRelAt eqrel .zero Γ A' rel →
      (∀ {t u A}, TypeStar Γ A' A → ConvNeDown Γ t u A → ConvTermDown Γ t u A) ∧
      (∀ {t u}, ConvNeUp Γ t u A' → ConvTermUp Γ t u A') :=
    fun h ↦ liftNeToConv_step (l := .zero) (fun _ hlt ↦ nomatch hlt) h
  cases l with
  | zero => exact h0 hA'
  | one =>
      exact liftNeToConv_step (l := .one)
        (fun _ hlt _ _ _ h ↦ by cases hlt; exact h0 h) hA'

/-- Lift `ConvNeDown` to `ConvTermDown` (`lift~toConv↓`). -/
theorem liftNeToConvDown {Γ : Context} {t u A : Term} :
    ConvNeDown Γ t u A → ConvTermDown Γ t u A
  | .mk D hwB k_l =>
      (liftNeToConvAt (reducible (eqrel := synEqRel) (syntacticRed D).1)).1
        D (.mk D hwB k_l)

/-- Lift `ConvNeUp` to `ConvTermUp` (`lift~toConv↑`). -/
theorem liftNeToConvUp {Γ : Context} {t u A : Term} (htu : ConvNeUp Γ t u A) :
    ConvTermUp Γ t u A :=
  (liftNeToConvAt (reducible (eqrel := synEqRel) (syntacticEqTerm (soundnessNeUp htu)).1)).2 htu

/-- `ConvTermDown` at `U` yields `ConvTypeDown` (`univConv↓`). -/
theorem univConvDown {Γ : Context} {A B : Term} (h : ConvTermDown Γ A B .univ) :
    ConvTypeDown Γ A B := by
  generalize hU : Term.univ = U₀ at h
  cases h with
  | neIns _ _ neU _ =>
      subst hU
      cases neU
  | univ _ _ hAB => exact hAB
  | _ => cases hU

/-- `ConvTermUp` at `U` yields `ConvTypeUp` (`univConv↑`). -/
theorem univConvUp {Γ : Context} {A B : Term} :
    ConvTermUp Γ A B .univ → ConvTypeUp Γ A B
  | .mk D d d' _ hwt' hwu' htu => by
      have hB : Term.univ = _ := whnfRedStar D Whnf.univ
      subst hB
      exact reductionConvTypeUp (.fromUniv d) (.fromUniv d') hwt' hwu'
        (liftConv (univConvDown htu))

/-!
## Algorithmic Equality Instance of `EqRelSet` (`Definition/Conversion/EqRelInstance.agda`)
-/

/-- Algorithmic equality of neutrals with injected type conversion (`Γ ⊢ k ~ l ∷ A`). -/
inductive ConvNeEq (Γ : Context) (k l A : Term) : Prop where
  | mk {B : Term} : TypeEq Γ A B → ConvNeUp Γ k l B → ConvNeEq Γ k l A

theorem convNeEq_var {Γ : Context} {x : Nat} {A : Term} (hx : HasType Γ (.var x) A) :
    ConvNeEq Γ (.var x) (.var x) A :=
  ⟨.refl (syntacticTerm hx), .var hx rfl⟩

theorem convNeEq_app {Γ : Context} {f g a b F G : Term}
    (hfg : ConvNeEq Γ f g (.pi F G)) (hab : ConvTermUp Γ a b F) :
    ConvNeEq Γ (.app f a) (.app g b) (subst0 G a) := by
  rcases hfg with ⟨hAB, hfg_up⟩
  have ⟨_, wfB⟩ := syntacticEq hAB
  rcases whNorm wfB with ⟨B', hwB', D⟩
  have hPiB' : TypeEq Γ (.pi F G) B' := .trans hAB (subsetStar D.reduction)
  rcases pi_eq_A_whnf hPiB' hwB' with ⟨H, E, hB'_eq⟩
  subst hB'_eq
  have ⟨hFH, hGE⟩ := injectivity hPiB'
  have ⟨_, wfa, _⟩ := syntacticEqTerm (soundnessConvUpTerm hab)
  exact ⟨substTypeEq hGE (.refl wfa),
    .app (.mk D.reduction .pi hfg_up) (convConvTerm hab hFH)⟩

theorem convNeEq_natrec {Γ : Context} {z z' s s' n n' F F' : Term}
    (hFF' : ConvTypeUp (.nat :: Γ) F F')
    (hzz' : ConvTermUp Γ z z' (subst0 F .zero))
    (hss' : ConvTermUp Γ s s' (recStepType F))
    (hnn' : ConvNeEq Γ n n' .nat) :
    ConvNeEq Γ (.natrec F z s n) (.natrec F' z' s' n') (subst0 F n) := by
  rcases hnn' with ⟨hAB, hnn'_up⟩
  have ⟨_, wfB⟩ := syntacticEq hAB
  rcases whNorm wfB with ⟨B', hwB', D⟩
  have hNatB' : TypeEq Γ .nat B' := .trans hAB (subsetStar D.reduction)
  have hB'_eq : B' = .nat := nat_eq_A_whnf hNatB' hwB'
  subst hB'_eq
  have hnn'_down : ConvNeDown Γ n n' .nat := .mk D.reduction .nat hnn'_up
  have ⟨wfF, _⟩ := syntacticEq (soundnessConvUp hFF')
  have ⟨_, wfn, _⟩ := syntacticEqTerm (soundnessNeDown hnn'_down)
  exact ⟨.refl (substType wfF wfn), .natrec hFF' hzz' hss' hnn'_down⟩

theorem convNeEq_symm {Γ : Context} {k l A : Term} :
    ConvNeEq Γ k l A → ConvNeEq Γ l k A
  | ⟨hAB, hkl⟩ => by
      rcases symNeUp (reflConEq (wfTypeEq hAB)) hkl with ⟨B', hBB', hlk⟩
      exact ⟨.trans hAB hBB', hlk⟩

theorem convNeEq_trans {Γ : Context} {k l m A : Term} :
    ConvNeEq Γ k l A → ConvNeEq Γ l m A → ConvNeEq Γ k m A
  | ⟨hAB₁, hkl⟩, ⟨_, hlm⟩ =>
      ⟨hAB₁, (transNeUp (reflConEq (wfTypeEq hAB₁)) hkl hlm).1⟩

theorem convNeEq_wk {Γ Δ : Context} {k l A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) :
    ConvNeEq Γ k l A → ConvNeEq Δ (wk ρ k) (wk ρ l) (wk ρ A)
  | ⟨hAB, hkl⟩ => ⟨wkTypeEq hρ hΔ hAB, wkConvNeUp hρ hΔ hkl⟩

theorem convNeEq_conv {Γ : Context} {k l A B : Term} :
    ConvNeEq Γ k l A → TypeEq Γ A B → ConvNeEq Γ k l B
  | ⟨hAC, hkl⟩, hAB => ⟨.trans (.symm hAB) hAC, hkl⟩

theorem convNeEq_to_conv {Γ : Context} {k l A : Term} :
    ConvNeEq Γ k l A → ConvTermUp Γ k l A
  | ⟨hAB, hkl⟩ => convConvTerm (liftNeToConvUp hkl) (.symm hAB)

/-- Algorithmic equality instance of `EqRelSet` (`eqRelInstance`). -/
def convEqRel : EqRelSet where
  TypeEqRel := ConvTypeUp
  TermEqRel := ConvTermUp
  NeEqRel := ConvNeEq
  neToTerm := convNeEq_to_conv
  typeToEq := soundnessConvUp
  termToEq := soundnessConvUpTerm
  univ := univConvUp
  symmType := symConv
  symmTerm := symConvTerm
  symmNe := convNeEq_symm
  transType := transConv
  transTerm := transConvTerm
  transNe := convNeEq_trans
  convTerm := convConvTerm
  convNe := convNeEq_conv
  wkType := wkConvTypeUp
  wkTerm := wkConvTermUp
  wkNe := convNeEq_wk
  redType := reductionConvTypeUp
  redTerm := reductionConvTermUp
  univRefl hΓ := liftConv (.univRefl hΓ)
  natRefl hΓ := liftConv (.natRefl hΓ)
  natTermRefl hΓ := liftConvTerm (.univ (.nat hΓ) (.nat hΓ) (.natRefl hΓ))
  piCong hF hFH hGE := liftConv (.piCong hF hFH hGE)
  piTermCong hF hFH_u hGE_u := by
    have ⟨_, hFU, hHU⟩ := syntacticEqTerm (soundnessConvUpTerm hFH_u)
    have ⟨_, hGU, hEU⟩ := syntacticEqTerm (soundnessConvUpTerm hGE_u)
    have hFH := univConvUp hFH_u
    have hGE := univConvUp hGE_u
    have hEU' := stabilityTerm (.cons (reflConEq (wfTerm hFU)) (soundnessConvUp hFH)) hEU
    exact liftConvTerm (.univ (.pi hFU hGU) (.pi hHU hEU') (.piCong hF hFH hGE))
  zeroRefl hΓ := liftConvTerm (.zeroRefl hΓ)
  succCong hmn := liftConvTerm (.succCong hmn)
  etaEq hF hf hg hwf hwg hfg := liftConvTerm (.etaEq hF hf hg hwf hwg hfg)
  varRefl := convNeEq_var
  appCong := convNeEq_app
  natrecCong := convNeEq_natrec

/-!
## Completeness of Algorithmic Equality (`Definition/Conversion/Consequences/Completeness.agda`, Theorem 4.11)
-/

/-- Completeness of algorithmic type equality (`completeEq`, Theorem 4.11). -/
theorem completeEq {Γ : Context} {A B : Term} (hAB : TypeEq Γ A B) :
    ConvTypeUp Γ A B := by
  rcases fundamentalEq (eqrel := convEqRel) hAB with ⟨vΓ, vA, _vB, vAB⟩
  exact escapeValidEq vΓ vA vAB

/-- Completeness of algorithmic term equality (`completeEqTerm`, Theorem 4.11). -/
theorem completeEqTerm {Γ : Context} {t u A : Term} (htu : TermEq Γ t u A) :
    ConvTermUp Γ t u A := by
  rcases fundamentalTermEq (eqrel := convEqRel) htu with ⟨vΓ, vA, _vt, _vu, vtu⟩
  exact escapeValidEqTerm vΓ vA vtu

end Abel2018
