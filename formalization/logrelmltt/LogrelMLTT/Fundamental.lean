import LogrelMLTT.Substitution

namespace LogrelMLTT

/-!
# Lambda and Natrec Introductions, and the Fundamental Theorem

This module translates:
- `Definition/LogicalRelation/Substitution/Introductions/Lambda.agda`
- `Definition/LogicalRelation/Substitution/Introductions/Natrec.agda`
- `Definition/LogicalRelation/Fundamental.agda`
- `Definition/LogicalRelation/Fundamental/Reducibility.agda`
-/

/-!
## Lambda Introductions (`Definition/LogicalRelation/Substitution/Introductions/Lambda.agda`)
-/

theorem lamRedTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ Δ : Context} {F G t : Term} {σ : Subst}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (ht : ValidTerm hG t)
    (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ) :
    RedTerm ((piValid hF hG) hΔ hσ).red (subst σ (.lam t)) := by
  have hPiFG : ValidType eqrel l Γ (.pi F G) := piValid hF hG
  have pPi := (hPiFG hΔ hσ).red
  have hLiftσ := liftSubstS hΔ hF hσ
  have pσF := (hF hΔ hσ).red
  have wfF : TypeWf Δ (subst σ F) := escape pσF
  have wfΔF : CtxWf (subst σ F :: Δ) := .cons hΔ wfF
  have wfwk1F : TypeWf (subst σ F :: Δ) (wk (.step .id) (subst σ F)) :=
    wkTypeWf (.step .id) wfΔF wfF
  have pσG := (hG wfΔF hLiftσ).red
  have wfG : TypeWf (subst σ F :: Δ) (subst (liftSubst σ) G) := escape pσG
  have pσt := (ht wfΔF hLiftσ).term
  have wft : HasType (subst σ F :: Δ) (subst (liftSubst σ) t) (subst (liftSubst σ) G) :=
    escapeTerm pσG pσt
  have wk1t0 : RedTerm pσG (subst0 (wk (.lift (.step .id)) (subst (liftSubst σ) t)) (.var 0)) :=
    irrelevanceTerm'' rfl (wkSingleSubstId (subst (liftSubst σ) t)).symm pσG pσG pσt
  have hBetaRaw : Step (subst σ F :: Δ)
      (.app (.lam (wk (.lift (.step .id)) (subst (liftSubst σ) t))) (.var 0))
      (subst0 (wk (.lift (.step .id)) (subst (liftSubst σ) t)) (.var 0))
      (subst0 (wk (.lift (.step .id)) (subst (liftSubst σ) G)) (.var 0)) :=
    .beta wfwk1F
      (wkHasType (.lift (.step .id)) (.cons wfΔF wfwk1F) wft)
      (.var wfΔF .here)
  have hBeta : Step (subst σ F :: Δ)
      (.app (wk1 (.lam (subst (liftSubst σ) t))) (.var 0))
      (subst0 (wk (.lift (.step .id)) (subst (liftSubst σ) t)) (.var 0))
      (subst (liftSubst σ) G) := by
    have h := hBetaRaw
    rw [wkSingleSubstId (subst (liftSubst σ) G)] at h
    exact h
  have hEta : eqrel.TermEqRel Δ (.lam (subst (liftSubst σ) t)) (.lam (subst (liftSubst σ) t))
      (.pi (subst σ F) (subst (liftSubst σ) G)) :=
    eqrel.etaEq wfF (.lam wfF wft) (.lam wfF wft) .lam .lam
      (escapeTermEq pσG (reflEqTerm pσG (redSubstTerm hBeta pσG wk1t0).1))
  rcases elimPiAt' (.refl (escape pPi)) pPi with ⟨l₀, piA⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ₁ rel ↦ LogRelAt eqrel l₀ Δ₁ (wk ρ (subst σ F)) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ₁ a rel ↦ LogRelAt eqrel l₀ Δ₁ (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) a) rel
  have hAt : LogRelAt eqrel l₀ Δ (.pi (subst σ F) (subst (liftSubst σ) G))
      (RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀) :=
    .pi piA.D piA.hF piA.hG piA.AeqA relF₀ relG₀
      piA.redF (fun _ _ _ h ↦ h) piA.redG (fun _ _ _ _ h ↦ h) piA.Gext
  have pPi₀ : RedType eqrel l₀ Δ (.pi (subst σ F) (subst (liftSubst σ) G)) := ⟨_, hAt⟩
  have hPiTerm : RedPiTerm eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀
      (subst σ (.lam t)) := by
    refine .mk (.lam (subst (liftSubst σ) t)) (idRedTermWf (.lam wfF wft)) .lam hEta
      (fun {ρ Δ₁ a b} hρ hΔ₁ ha hb hab ↦ ?_)
      (fun {ρ Δ₁ a} hρ hΔ₁ ha ↦ ?_)
    · have hρσ := wkSubstS hρ hΔ₁ hσ
      have pF_ρ := piA.redF hρ hΔ₁
      have pF_ρσ := (hF hΔ₁ hρσ).red
      have ha' : RedTerm pF_ρσ a := irrelevanceTerm' (wk_subst F) pF_ρ pF_ρσ ha
      have hb' : RedTerm pF_ρσ b := irrelevanceTerm' (wk_subst F) pF_ρ pF_ρσ hb
      have hab' : RedTermEq pF_ρσ a b := irrelevanceEqTerm' (wk_subst F) pF_ρ pF_ρσ hab
      have wfF₁' : TypeWf Δ₁ (subst (wkSubst ρ σ) F) := escape pF_ρσ
      have wfF₁ : TypeWf Δ₁ (wk ρ (subst σ F)) := escape pF_ρ
      have hLiftρσ := liftSubstS hΔ₁ hF hρσ
      have pG₁ := (hG (.cons hΔ₁ wfF₁') hLiftρσ).red
      have hCtxEq : (subst (wkSubst ρ σ) F :: Δ₁) = (wk ρ (subst σ F) :: Δ₁) :=
        congrArg (fun x ↦ x :: Δ₁) (wk_subst F).symm
      have pG₁' : RedType eqrel l (wk ρ (subst σ F) :: Δ₁) (wk (.lift ρ) (subst (liftSubst σ) G)) :=
        irrelevanceΓ' hCtxEq (wk_subst_lift G).symm pG₁
      have pt₁' : RedTerm pG₁' (wk (.lift ρ) (subst (liftSubst σ) t)) :=
        irrelevanceTermΓ'' hCtxEq (wk_subst_lift G).symm (wk_subst_lift t).symm
          pG₁ pG₁' (ht (.cons hΔ₁ wfF₁') hLiftρσ).term
      have wfa : HasType Δ₁ a (wk ρ (subst σ F)) := escapeTerm pF_ρ ha
      have wfb : HasType Δ₁ b (wk ρ (subst σ F)) := escapeTerm pF_ρ hb
      have wft₁ : HasType (wk ρ (subst σ F) :: Δ₁)
          (wk (.lift ρ) (subst (liftSubst σ) t))
          (wk (.lift ρ) (subst (liftSubst σ) G)) :=
        escapeTerm pG₁' pt₁'
      have hρσa := consSubstS hΔ₁ hρσ hF ha'
      have hρσb := consSubstS hΔ₁ hρσ hF hb'
      have pGa' := (hG hΔ₁ hρσa).red
      have pGa := piA.redG hρ hΔ₁ ha
      have pta : RedTerm pGa (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) a) :=
        irrelevanceTerm'' (singleSubstWkComp a σ G).symm (singleSubstWkComp a σ t).symm
          pGa' pGa (ht hΔ₁ hρσa).term
      have pGb' := (hG hΔ₁ hρσb).red
      have pGb := piA.redG hρ hΔ₁ hb
      have ptb : RedTerm pGb (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) b) :=
        irrelevanceTerm'' (singleSubstWkComp b σ G).symm (singleSubstWkComp b σ t).symm
          pGb' pGb (ht hΔ₁ hρσb).term
      have hlam_a : RedTermEq pGa (.app (wk ρ (.lam (subst (liftSubst σ) t))) a)
          (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) a) :=
        (redSubstTerm (.beta wfF₁ wft₁ wfa) pGa pta).2
      have hGa_Gb : RedEq pGa (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) b) :=
        piA.Gext hρ hΔ₁ ha hb hab
      have hρσab : ValidSubstEq eqrel Δ₁ (consSubst (wkSubst ρ σ) a) (consSubst (wkSubst ρ σ) b) (F :: Γ) :=
        ValidSubstEq.cons (reflSubst hρσ) pF_ρσ hab'
      have hta_tb : RedTermEq pGa
          (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) a)
          (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) b) :=
        irrelevanceEqTerm'' (singleSubstWkComp a σ t).symm (singleSubstWkComp b σ t).symm
          (singleSubstWkComp a σ G).symm pGa' pGa ((ht hΔ₁ hρσa).eq hρσb hρσab)
      have htb_lam_b : RedTermEq pGa
          (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) b)
          (.app (wk ρ (.lam (subst (liftSubst σ) t))) b) :=
        convEqTerm₂ pGa pGb hGa_Gb
          (symEqTerm pGb (redSubstTerm (.beta wfF₁ wft₁ wfb) pGb ptb).2)
      exact transEqTerm pGa hlam_a (transEqTerm pGa hta_tb htb_lam_b)
    · have hρσ := wkSubstS hρ hΔ₁ hσ
      have pF_ρ := piA.redF hρ hΔ₁
      have pF_ρσ := (hF hΔ₁ hρσ).red
      have ha' : RedTerm pF_ρσ a := irrelevanceTerm' (wk_subst F) pF_ρ pF_ρσ ha
      have wfF₁' : TypeWf Δ₁ (subst (wkSubst ρ σ) F) := escape pF_ρσ
      have wfF₁ : TypeWf Δ₁ (wk ρ (subst σ F)) := escape pF_ρ
      have hLiftρσ := liftSubstS hΔ₁ hF hρσ
      have pG₁ := (hG (.cons hΔ₁ wfF₁') hLiftρσ).red
      have hCtxEq : (subst (wkSubst ρ σ) F :: Δ₁) = (wk ρ (subst σ F) :: Δ₁) :=
        congrArg (fun x ↦ x :: Δ₁) (wk_subst F).symm
      have pG₁' : RedType eqrel l (wk ρ (subst σ F) :: Δ₁) (wk (.lift ρ) (subst (liftSubst σ) G)) :=
        irrelevanceΓ' hCtxEq (wk_subst_lift G).symm pG₁
      have pt₁' : RedTerm pG₁' (wk (.lift ρ) (subst (liftSubst σ) t)) :=
        irrelevanceTermΓ'' hCtxEq (wk_subst_lift G).symm (wk_subst_lift t).symm
          pG₁ pG₁' (ht (.cons hΔ₁ wfF₁') hLiftρσ).term
      have wfa : HasType Δ₁ a (wk ρ (subst σ F)) := escapeTerm pF_ρ ha
      have wft₁ : HasType (wk ρ (subst σ F) :: Δ₁)
          (wk (.lift ρ) (subst (liftSubst σ) t))
          (wk (.lift ρ) (subst (liftSubst σ) G)) :=
        escapeTerm pG₁' pt₁'
      have hρσa := consSubstS hΔ₁ hρσ hF ha'
      have pGa' := (hG hΔ₁ hρσa).red
      have pGa := piA.redG hρ hΔ₁ ha
      have pta : RedTerm pGa (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) a) :=
        irrelevanceTerm'' (singleSubstWkComp a σ G).symm (singleSubstWkComp a σ t).symm
          pGa' pGa (ht hΔ₁ hρσa).term
      exact (redSubstTerm (.beta wfF₁ wft₁ wfa) pGa pta).1
  exact irrelevanceTerm pPi₀ pPi ⟨_, hAt, hPiTerm⟩

/-- Valid lambda term construction (`lamᵛ`). -/
theorem lamValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (ht : ValidTerm hG t) :
    ValidTerm (piValid hF hG) (.lam t) := by
  intro Δ σ hΔ hσ
  have hPiFG : ValidType eqrel l Γ (.pi F G) := piValid hF hG
  have pPi := (hPiFG hΔ hσ).red
  refine ⟨lamRedTerm hF hG ht hΔ hσ, fun {σ'} hσ' hσσ' ↦ ?_⟩
  have pPi' := (hPiFG hΔ hσ').red
  have pPiEq := (hPiFG hΔ hσ).eq hσ' hσσ'
  have wfF : TypeWf Δ (subst σ F) := escape (hF hΔ hσ).red
  have wfF' : TypeWf Δ (subst σ' F) := escape (hF hΔ hσ').red
  have wfΔF : CtxWf (subst σ F :: Δ) := .cons hΔ wfF
  have wfΔF' : CtxWf (subst σ' F :: Δ) := .cons hΔ wfF'
  have hLiftσ := liftSubstS hΔ hF hσ
  have hLiftσ' := liftSubstS hΔ hF hσ'
  have pG₁ := (hG wfΔF hLiftσ).red
  have pG₁' := (hG wfΔF' hLiftσ').red
  have wft : HasType (subst σ F :: Δ) (subst (liftSubst σ) t) (subst (liftSubst σ) G) :=
    escapeTerm pG₁ (ht wfΔF hLiftσ).term
  have wft' : HasType (subst σ' F :: Δ) (subst (liftSubst σ') t) (subst (liftSubst σ') G) :=
    escapeTerm pG₁' (ht wfΔF' hLiftσ').term
  rcases elimPiAt' (.refl (escape pPi)) pPi with ⟨l₀, piA⟩
  rcases elimPiAt' (.refl (escape pPi')) pPi' with ⟨l₀', piA'⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ₁ rel ↦ LogRelAt eqrel l₀ Δ₁ (wk ρ (subst σ F)) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ₁ a rel ↦ LogRelAt eqrel l₀ Δ₁ (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) a) rel
  have hAt : LogRelAt eqrel l₀ Δ (.pi (subst σ F) (subst (liftSubst σ) G))
      (RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀) :=
    .pi piA.D piA.hF piA.hG piA.AeqA relF₀ relG₀
      piA.redF (fun _ _ _ h ↦ h) piA.redG (fun _ _ _ _ h ↦ h) piA.Gext
  have pPi₀ : RedType eqrel l₀ Δ (.pi (subst σ F) (subst (liftSubst σ) G)) := ⟨_, hAt⟩
  have hAppEq : ∀ {ρ Δ₁ a} (hρ : WkCtx ρ Δ₁ Δ) (hΔ₁ : CtxWf Δ₁)
      (ha : RedTerm (piA.redF hρ hΔ₁) a),
      RedTermEq (piA.redG hρ hΔ₁ ha)
        (.app (wk ρ (subst σ (.lam t))) a)
        (.app (wk ρ (subst σ' (.lam t))) a) := by
    intro ρ Δ₁ a hρ hΔ₁ ha
    have hρσ := wkSubstS hρ hΔ₁ hσ
    have hρσ' := wkSubstS hρ hΔ₁ hσ'
    have hρσσ' := wkSubstSEq hρ hΔ₁ hσσ'
    have pF_ρ := piA.redF hρ hΔ₁
    have pF'_ρ := piA'.redF hρ hΔ₁
    have pF_ρσ := (hF hΔ₁ hρσ).red
    have pF_ρσ' := (hF hΔ₁ hρσ').red
    have wfF₁' : TypeWf Δ₁ (subst (wkSubst ρ σ) F) := escape pF_ρσ
    have wfF₁ : TypeWf Δ₁ (wk ρ (subst σ F)) := escape pF_ρ
    have wfF₂' : TypeWf Δ₁ (subst (wkSubst ρ σ') F) := escape pF_ρσ'
    have wfF₂ : TypeWf Δ₁ (wk ρ (subst σ' F)) := escape pF'_ρ
    have hFF'_ρσ := (hF hΔ₁ hρσ).eq hρσ' hρσσ'
    have ha' : RedTerm pF_ρσ a := irrelevanceTerm' (wk_subst F) pF_ρ pF_ρσ ha
    have ha'' : RedTerm pF_ρσ' a := convTerm₁ pF_ρσ pF_ρσ' hFF'_ρσ ha'
    have ha''' : RedTerm pF'_ρ a := irrelevanceTerm' (wk_subst F).symm pF_ρσ' pF'_ρ ha''
    have wfa : HasType Δ₁ a (wk ρ (subst σ F)) := escapeTerm pF_ρ ha
    have wfa' : HasType Δ₁ a (wk ρ (subst σ' F)) := escapeTerm pF'_ρ ha'''
    have hρσa := consSubstS hΔ₁ hρσ hF ha'
    have hρσ'a := consSubstS hΔ₁ hρσ' hF ha''
    have hρσa_eq := consSubstSEq hΔ₁ hρσ hρσσ' hF ha'
    have pGa' := (hG hΔ₁ hρσa).red
    have pGa₁' := (hG hΔ₁ hρσ'a).red
    have pGa := piA.redG hρ hΔ₁ ha
    have pGa'' := piA'.redG hρ hΔ₁ ha'''
    have hGa_eq : RedEq pGa (subst0 (wk (.lift ρ) (subst (liftSubst σ') G)) a) :=
      irrelevanceEq'' (singleSubstWkComp a σ G).symm (singleSubstWkComp a σ' G).symm
        pGa' pGa ((hG hΔ₁ hρσa).eq hρσ'a hρσa_eq)
    have hLiftρσ := liftSubstS hΔ₁ hF hρσ
    have hLiftρσ' := liftSubstS hΔ₁ hF hρσ'
    have pG₁_ρ := (hG (.cons hΔ₁ wfF₁') hLiftρσ).red
    have hCtxEq₁ : (subst (wkSubst ρ σ) F :: Δ₁) = (wk ρ (subst σ F) :: Δ₁) :=
      congrArg (fun x ↦ x :: Δ₁) (wk_subst F).symm
    have pG₁'_ρ : RedType eqrel l (wk ρ (subst σ F) :: Δ₁) (wk (.lift ρ) (subst (liftSubst σ) G)) :=
      irrelevanceΓ' hCtxEq₁ (wk_subst_lift G).symm pG₁_ρ
    have pG₂_ρ := (hG (.cons hΔ₁ wfF₂') hLiftρσ').red
    have hCtxEq₂ : (subst (wkSubst ρ σ') F :: Δ₁) = (wk ρ (subst σ' F) :: Δ₁) :=
      congrArg (fun x ↦ x :: Δ₁) (wk_subst F).symm
    have pG₂'_ρ : RedType eqrel l (wk ρ (subst σ' F) :: Δ₁) (wk (.lift ρ) (subst (liftSubst σ') G)) :=
      irrelevanceΓ' hCtxEq₂ (wk_subst_lift G).symm pG₂_ρ
    have pt₁' : RedTerm pG₁'_ρ (wk (.lift ρ) (subst (liftSubst σ) t)) :=
      irrelevanceTermΓ'' hCtxEq₁ (wk_subst_lift G).symm (wk_subst_lift t).symm
        pG₁_ρ pG₁'_ρ (ht (.cons hΔ₁ wfF₁') hLiftρσ).term
    have pt₂' : RedTerm pG₂'_ρ (wk (.lift ρ) (subst (liftSubst σ') t)) :=
      irrelevanceTermΓ'' hCtxEq₂ (wk_subst_lift G).symm (wk_subst_lift t).symm
        pG₂_ρ pG₂'_ρ (ht (.cons hΔ₁ wfF₂') hLiftρσ').term
    have wft₁ : HasType (wk ρ (subst σ F) :: Δ₁)
        (wk (.lift ρ) (subst (liftSubst σ) t))
        (wk (.lift ρ) (subst (liftSubst σ) G)) :=
      escapeTerm pG₁'_ρ pt₁'
    have wft₂ : HasType (wk ρ (subst σ' F) :: Δ₁)
        (wk (.lift ρ) (subst (liftSubst σ') t))
        (wk (.lift ρ) (subst (liftSubst σ') G)) :=
      escapeTerm pG₂'_ρ pt₂'
    have pta : RedTerm pGa (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) a) :=
      irrelevanceTerm'' (singleSubstWkComp a σ G).symm (singleSubstWkComp a σ t).symm
        pGa' pGa (ht hΔ₁ hρσa).term
    have pta' : RedTerm pGa'' (subst0 (wk (.lift ρ) (subst (liftSubst σ') t)) a) :=
      irrelevanceTerm'' (singleSubstWkComp a σ' G).symm (singleSubstWkComp a σ' t).symm
        pGa₁' pGa'' (ht hΔ₁ hρσ'a).term
    have hlam_ta : RedTermEq pGa (.app (wk ρ (subst σ (.lam t))) a)
        (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) a) :=
      (redSubstTerm (.beta wfF₁ wft₁ wfa) pGa pta).2
    have hta'_lam' : RedTermEq pGa
        (subst0 (wk (.lift ρ) (subst (liftSubst σ') t)) a)
        (.app (wk ρ (subst σ' (.lam t))) a) :=
      convEqTerm₂ pGa pGa'' hGa_eq
        (symEqTerm pGa'' (redSubstTerm (.beta wfF₂ wft₂ wfa') pGa'' pta').2)
    have hta_ta' : RedTermEq pGa
        (subst0 (wk (.lift ρ) (subst (liftSubst σ) t)) a)
        (subst0 (wk (.lift ρ) (subst (liftSubst σ') t)) a) :=
      irrelevanceEqTerm'' (singleSubstWkComp a σ t).symm (singleSubstWkComp a σ' t).symm
        (singleSubstWkComp a σ G).symm pGa' pGa ((ht hΔ₁ hρσa).eq hρσ'a hρσa_eq)
    exact transEqTerm pGa hlam_ta (transEqTerm pGa hta_ta' hta'_lam')
  have var0_wf : HasType (subst σ F :: Δ) (.var 0) (wk (.step .id) (subst σ F)) :=
    .var wfΔF .here
  have neuVar0 : RedTerm (piA.redF (.step .id) wfΔF) (.var 0) :=
    neuTerm (piA.redF (.step .id) wfΔF) (.var 0) var0_wf (eqrel.varRefl var0_wf)
  have hEtaEq_σ_σ' : eqrel.TermEqRel Δ (.lam (subst (liftSubst σ) t)) (.lam (subst (liftSubst σ') t))
      (.pi (subst σ F) (subst (liftSubst σ) G)) :=
    eqrel.etaEq wfF (.lam wfF wft)
      (.conv (.lam wfF' wft') (.symm (eqrel.typeToEq (escapeEq pPi pPiEq))))
      .lam .lam
      (escapeTermEq pG₁
        (irrelevanceEqTerm' (idWkLiftSubstLemma σ G)
          (piA.redG (.step .id) wfΔF neuVar0) pG₁
          (hAppEq (.step .id) wfΔF neuVar0)))
  have ht_σ_0 : RedPiTerm eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀
      (subst σ (.lam t)) :=
    (RedTerm_of_LogRelAt hAt pPi₀).mp
      (irrelevanceTerm pPi pPi₀ (lamRedTerm hF hG ht hΔ hσ))
  have ht_σ'_0 : RedPiTerm eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀
      (subst σ' (.lam t)) :=
    (RedTerm_of_LogRelAt hAt pPi₀).mp
      (irrelevanceTerm pPi pPi₀
        (convTerm₂ pPi pPi' pPiEq (lamRedTerm hF hG ht hΔ hσ')))
  have hPiEqTerm : RedPiTermEq eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀
      (subst σ (.lam t)) (subst σ' (.lam t)) :=
    .mk (.lam (subst (liftSubst σ) t)) (.lam (subst (liftSubst σ') t))
      (idRedTermWf (.lam wfF wft))
      (idRedTermWf (.conv (.lam wfF' wft') (.symm (eqrel.typeToEq (escapeEq pPi pPiEq)))))
      .lam .lam hEtaEq_σ_σ' ht_σ_0 ht_σ'_0 hAppEq
  exact irrelevanceEqTerm pPi₀ pPi ⟨_, hAt, hPiEqTerm⟩

/-- Reducibility of η-equality under a valid substitution (`η-eqEqTerm`). -/
theorem etaEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ Δ : Context} {f g F G : Term} {σ : Subst}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (hf0g0 : ValidTermEq hG (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)))
    (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ)
    (hf : RedTerm ((piValid hF hG) hΔ hσ).red (subst σ f))
    (hg : RedTerm ((piValid hF hG) hΔ hσ).red (subst σ g)) :
    RedTermEq ((piValid hF hG) hΔ hσ).red (subst σ f) (subst σ g) := by
  have hPiFG : ValidType eqrel l Γ (.pi F G) := piValid hF hG
  have pPi := (hPiFG hΔ hσ).red
  rcases elimPiAt' (.refl (escape pPi)) pPi with ⟨l₀, piA⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ₁ rel ↦ LogRelAt eqrel l₀ Δ₁ (wk ρ (subst σ F)) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ₁ a rel ↦ LogRelAt eqrel l₀ Δ₁ (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) a) rel
  have hAt : LogRelAt eqrel l₀ Δ (.pi (subst σ F) (subst (liftSubst σ) G))
      (RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀) :=
    .pi piA.D piA.hF piA.hG piA.AeqA relF₀ relG₀
      piA.redF (fun _ _ _ h ↦ h) piA.redG (fun _ _ _ _ h ↦ h) piA.Gext
  have pPi₀ : RedType eqrel l₀ Δ (.pi (subst σ F) (subst (liftSubst σ) G)) := ⟨_, hAt⟩
  have hfPi : RedPiTerm eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀ (subst σ f) :=
    (RedTerm_of_LogRelAt hAt pPi₀).mp (irrelevanceTerm pPi pPi₀ hf)
  have hgPi : RedPiTerm eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀ (subst σ g) :=
    (RedTerm_of_LogRelAt hAt pPi₀).mp (irrelevanceTerm pPi pPi₀ hg)
  rcases hfPi with ⟨f₁, df, funcF, feqf, appEq_f, appTerm_f⟩
  rcases hgPi with ⟨g₁, dg, funcG, geqg, appEq_g, appTerm_g⟩
  have wfF : TypeWf Δ (subst σ F) := piA.hF
  have wfΔF : CtxWf (subst σ F :: Δ) := .cons hΔ wfF
  have pσF := (hF hΔ hσ).red
  have pwk1F : RedType eqrel l (subst σ F :: Δ) (wk (.step .id) (subst σ F)) :=
    wkRed (.step .id) wfΔF pσF
  have var0' : HasType (subst σ F :: Δ) (.var 0) (wk (.step .id) (subst σ F)) :=
    .var wfΔF .here
  have var0 : RedTerm pwk1F (.var 0) :=
    neuTerm pwk1F (.var 0) var0' (eqrel.varRefl var0')
  have var0_eq : RedTermEq pwk1F (.var 0) (.var 0) :=
    neuEqTerm pwk1F (.var 0) (.var 0) var0' var0' (eqrel.varRefl var0')
  have var0_0 : RedTerm (piA.redF (.step .id) wfΔF) (.var 0) :=
    irrelevanceTerm pwk1F (piA.redF (.step .id) wfΔF) var0
  have pσG' := piA.redG (.step .id) wfΔF var0_0
  have hLiftσ := liftSubstS hΔ hF hσ
  have pσG := (hG wfΔF hLiftσ).red
  have σf0_eq_σg0_raw : eqrel.TermEqRel (subst σ F :: Δ)
      (subst (liftSubst σ) (.app (wk1 f) (.var 0)))
      (subst (liftSubst σ) (.app (wk1 g) (.var 0)))
      (subst (liftSubst σ) G) :=
    escapeTermEq pσG (hf0g0 wfΔF hLiftσ)
  have hf_wk_eq : subst (liftSubst σ) (.app (wk1 f) (.var 0)) =
      .app (wk1 (subst σ f)) (.var 0) := by
    change Term.app (subst (liftSubst σ) (wk (.step .id) f)) (.var 0) =
      Term.app (wk (.step .id) (subst σ f)) (.var 0)
    exact congrArg (fun x ↦ Term.app x (.var 0))
      ((subst_wk (ρ := .step .id) f).trans (wk_subst (ρ := .step .id) f).symm)
  have hg_wk_eq : subst (liftSubst σ) (.app (wk1 g) (.var 0)) =
      .app (wk1 (subst σ g)) (.var 0) := by
    change Term.app (subst (liftSubst σ) (wk (.step .id) g)) (.var 0) =
      Term.app (wk (.step .id) (subst σ g)) (.var 0)
    exact congrArg (fun x ↦ Term.app x (.var 0))
      ((subst_wk (ρ := .step .id) g).trans (wk_subst (ρ := .step .id) g).symm)
  have σf0_eq_σg0' : eqrel.TermEqRel (subst σ F :: Δ)
      (.app (wk1 (subst σ f)) (.var 0))
      (.app (wk1 (subst σ g)) (.var 0))
      (subst (liftSubst σ) G) := by
    rwa [hf_wk_eq, hg_wk_eq] at σf0_eq_σg0_raw
  have hf₁_term : RedTerm pPi f₁ :=
    irrelevanceTerm pPi₀ pPi ⟨_, hAt, .mk f₁ (idRedTermWf df.target) funcF feqf appEq_f appTerm_f⟩
  have hg₁_term : RedTerm pPi g₁ :=
    irrelevanceTerm pPi₀ pPi ⟨_, hAt, .mk g₁ (idRedTermWf dg.target) funcG geqg appEq_g appTerm_g⟩
  have f_eq_f₁ : RedTermEq pPi (subst σ f) f₁ :=
    (redSubstStarTerm df.reduction pPi hf₁_term).2
  have g_eq_g₁ : RedTermEq pPi (subst σ g) g₁ :=
    (redSubstStarTerm dg.reduction pPi hg₁_term).2
  have pwk1Pi : RedType eqrel l (subst σ F :: Δ) (wk (.step .id) (.pi (subst σ F) (subst (liftSubst σ) G))) :=
    wkRed (.step .id) wfΔF pPi
  have pσG'_l : RedType eqrel l (subst σ F :: Δ)
      (subst0 (wk (.lift (.step .id)) (subst (liftSubst σ) G)) (.var 0)) :=
    irrelevance' (cons0wkLift1_id σ G).symm pσG
  have eq'_red : RedTermEq pσG
      (.app (wk (.step .id) (subst σ f)) (.var 0))
      (.app (wk (.step .id) f₁) (.var 0)) :=
    irrelevanceEqTerm' (cons0wkLift1_id σ G) pσG'_l pσG
      (appCongTerm pwk1F pσG'_l pwk1Pi
        (wkRedTermEq (.step .id) wfΔF pPi f_eq_f₁) var0 var0 var0_eq)
  have eq₁'_red : RedTermEq pσG
      (.app (wk (.step .id) (subst σ g)) (.var 0))
      (.app (wk (.step .id) g₁) (.var 0)) :=
    irrelevanceEqTerm' (cons0wkLift1_id σ G) pσG'_l pσG
      (appCongTerm pwk1F pσG'_l pwk1Pi
        (wkRedTermEq (.step .id) wfΔF pPi g_eq_g₁) var0 var0 var0_eq)
  have eq_syn := escapeTermEq pσG eq'_red
  have eq₁_syn := escapeTermEq pσG eq₁'_red
  have hEta_f₁_g₁ : eqrel.TermEqRel Δ f₁ g₁ (.pi (subst σ F) (subst (liftSubst σ) G)) :=
    eqrel.etaEq wfF df.target dg.target funcF.toWhnf funcG.toWhnf
      (eqrel.transTerm (eqrel.symmTerm eq_syn) (eqrel.transTerm σf0_eq_σg0' eq₁_syn))
  have hPiEqTerm : RedPiTermEq eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀
      (subst σ f) (subst σ g) := by
    refine .mk f₁ g₁ df dg funcF funcG hEta_f₁_g₁
      (.mk f₁ df funcF feqf appEq_f appTerm_f)
      (.mk g₁ dg funcG geqg appEq_g appTerm_g)
      (fun {ρ Δ₁ a} hρ hΔ₁ ha ↦ ?_)
    have hρσ := wkSubstS hρ hΔ₁ hσ
    have pF'' := (hF hΔ₁ hρσ).red
    have ha' : RedTerm pF'' a :=
      irrelevanceTerm' (wk_subst F) (piA.redF hρ hΔ₁) pF'' ha
    have hρσa := consSubstS hΔ₁ hρσ hF ha'
    have fEq : subst (consSubst (wkSubst ρ σ) a) (.app (wk1 f) (.var 0)) =
        .app (wk ρ (subst σ f)) a := by
      change Term.app (subst (consSubst (wkSubst ρ σ) a) (wk (.step .id) f)) a =
        Term.app (wk ρ (subst σ f)) a
      exact congrArg (fun x ↦ Term.app x a)
        ((subst_wk (ρ := .step .id) f).trans (wk_subst (ρ := ρ) f).symm)
    have gEq : subst (consSubst (wkSubst ρ σ) a) (.app (wk1 g) (.var 0)) =
        .app (wk ρ (subst σ g)) a := by
      change Term.app (subst (consSubst (wkSubst ρ σ) a) (wk (.step .id) g)) a =
        Term.app (wk ρ (subst σ g)) a
      exact congrArg (fun x ↦ Term.app x a)
        ((subst_wk (ρ := .step .id) g).trans (wk_subst (ρ := ρ) g).symm)
    have GEq : subst (consSubst (wkSubst ρ σ) a) G =
        subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) a :=
      (singleSubstWkComp a σ G).symm
    have pGa := piA.redG hρ hΔ₁ ha
    have hf_eq_g : RedTermEq pGa (.app (wk ρ (subst σ f)) a) (.app (wk ρ (subst σ g)) a) :=
      irrelevanceEqTerm'' fEq gEq GEq (hG hΔ₁ hρσa).red pGa (hf0g0 hΔ₁ hρσa)
    have pρPi := wkRed hρ hΔ₁ pPi
    have hf₁_ρ : RedTerm pρPi (wk ρ f₁) := wkRedTerm hρ hΔ₁ pPi hf₁_term
    have hg₁_ρ : RedTerm pρPi (wk ρ g₁) := wkRedTerm hρ hΔ₁ pPi hg₁_term
    have hf₁a : RedTerm pGa (.app (wk ρ f₁) a) :=
      appTerm (piA.redF hρ hΔ₁) pGa pρPi hf₁_ρ ha
    have hg₁a : RedTerm pGa (.app (wk ρ g₁) a) :=
      appTerm (piA.redF hρ hΔ₁) pGa pρPi hg₁_ρ ha
    have wfa : HasType Δ₁ a (wk ρ (subst σ F)) := escapeTerm (piA.redF hρ hΔ₁) ha
    have hfa_f₁a : RedTermEq pGa (.app (wk ρ (subst σ f)) a) (.app (wk ρ f₁) a) :=
      (redSubstStarTerm ((wkStar hρ hΔ₁ df.reduction).app wfa) pGa hf₁a).2
    have hga_g₁a : RedTermEq pGa (.app (wk ρ (subst σ g)) a) (.app (wk ρ g₁) a) :=
      (redSubstStarTerm ((wkStar hρ hΔ₁ dg.reduction).app wfa) pGa hg₁a).2
    exact transEqTerm pGa (symEqTerm pGa hfa_f₁a)
      (transEqTerm pGa hf_eq_g hga_g₁a)
  exact irrelevanceEqTerm pPi₀ pPi ⟨_, hAt, hPiEqTerm⟩

/-- Validity of η-equality (`η-eqᵛ`). -/
theorem etaEqValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {f g F G : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (hf : ValidTerm (piValid hF hG) f)
    (hg : ValidTerm (piValid hF hG) g)
    (hf0g0 : ValidTermEq hG (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0))) :
    ValidTermEq (piValid hF hG) f g :=
  fun hΔ hσ ↦ etaEqTerm hF hG hf0g0 hΔ hσ (hf hΔ hσ).term (hg hΔ hσ).term

/-!
## Natural Recursion Introductions (`Definition/LogicalRelation/Substitution/Introductions/Natrec.agda`)
-/

/-- Natural recursion closure reduction (`natrec-subst*`). -/
theorem natrecSubstStar {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context}
    {C c g n n' : Term}
    (hC : TypeWf (.nat :: Γ) C)
    (hc : HasType Γ c (subst0 C .zero))
    (hg : HasType Γ g (recStepType C))
    (dnn' : Star Γ n n' .nat)
    (pNat : RedType eqrel l Γ .nat)
    (hn' : RedTerm pNat n')
    (prop : ∀ {t t'}, RedTerm pNat t → RedTerm pNat t' → RedTermEq pNat t t' →
      TypeEq Γ (subst0 C t) (subst0 C t')) :
    Star Γ (.natrec C c g n) (.natrec C c g n') (subst0 C n) := by
  generalize hNatEq : Term.nat = N₀ at dnn'
  induction dnn' with
  | refl hn =>
      subst hNatEq
      exact .refl (.natrec hC hc hg hn)
  | @step _ n n₁ n' hStep hRest ih =>
      subst hNatEq
      rcases redSubstStarTerm hRest pNat hn' with ⟨hn₁, _⟩
      rcases redSubstTerm hStep pNat hn₁ with ⟨hn, hnn₁⟩
      have hRestNatrec : Star Γ (.natrec C c g n₁) (.natrec C c g n') (subst0 C n₁) :=
        ih hn' rfl
      exact .step (.natrec hC hc hg hStep)
        (hRestNatrec.conv (prop hn₁ hn (symEqTerm pNat hnn₁)))

theorem consSubstSEqNat {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context}
    {σ σ' : Subst} {t t' : Term} {Γ : Context}
    (hTailEq : ValidSubstEq eqrel Δ σ σ' Γ)
    (pNat : RedType eqrel l Δ .nat)
    (hHeadEq : RedTermEq pNat t t') :
    ValidSubstEq eqrel Δ (consSubst σ t) (consSubst σ' t') (.nat :: Γ) :=
  ⟨hTailEq, l, pNat, hHeadEq⟩

theorem sucCase₃ {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context}
    (hNat : ValidType eqrel l Γ .nat) :
    ValidTerm (wk1Valid (F := .nat) hNat) (.succ (.var 0)) := by
  have hVar0 : ValidTerm (wk1Valid (F := .nat) hNat) (.var 0) := by
    intro Δ σ hΔ hσ
    have pwk1Nat := ((wk1Valid (F := .nat) hNat) hΔ hσ).red
    have pTailNat := (hNat hΔ hσ.tail).red
    refine ⟨irrelevanceTerm pTailNat pwk1Nat (hσ.head hNat hΔ),
      fun {σ'} hσ' hσσ' ↦ irrelevanceEqTerm pTailNat pwk1Nat (hσσ'.head hNat hΔ hσ)⟩
  intro Δ σ hΔ hσ
  exact sucValid (wk1Valid (F := .nat) hNat) hVar0 hΔ hσ

theorem sucCase₂ {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F : Term}
    (hNat : ValidType eqrel l Γ .nat)
    (hF : ValidType eqrel l (.nat :: Γ) F) :
    ValidType eqrel l (.nat :: Γ) (substKeep F (.succ (.var 0))) :=
  substUpS hNat hF (sucCase₃ hNat)

theorem sucCase₁ {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F : Term}
    (hNat : ValidType eqrel l Γ .nat)
    (hF : ValidType eqrel l (.nat :: Γ) F) :
    ValidType eqrel l (.nat :: Γ) (arr F (substKeep F (.succ (.var 0)))) :=
  arrValid hF (sucCase₂ hNat hF)

/-- Construct a valid type for the successor case of `natrec` (`sucCase`). -/
theorem sucCase {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F : Term}
    (hNat : ValidType eqrel l Γ .nat)
    (hF : ValidType eqrel l (.nat :: Γ) F) :
    ValidType eqrel l Γ (recStepType F) :=
  piValid hNat (sucCase₁ hNat hF)

/-- Construct a valid type equality for the successor case of `natrec` (`sucCaseCong`). -/
theorem sucCaseCong {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F F' : Term}
    (hNat : ValidType eqrel l Γ .nat)
    (hF : ValidType eqrel l (.nat :: Γ) F)
    (hF' : ValidType eqrel l (.nat :: Γ) F')
    (hFF' : ValidTypeEq hF F') :
    ValidTypeEq (sucCase hNat hF) (recStepType F') :=
  piCongValid hNat (sucCase₁ hNat hF) hNat (sucCase₁ hNat hF')
    (reflValid hNat)
    (arrCongValid hF hF' hFF' (sucCase₂ hNat hF) (sucCase₂ hNat hF')
      (substUpSEq hNat hF hF' hFF' (sucCase₃ hNat) (sucCase₃ hNat)
        (reflValidTerm (wk1Valid (F := .nat) hNat) (sucCase₃ hNat))))

theorem redTerm_of_RedNatTerm {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} {n : Term}
    (hΔ : CtxWf Δ) (hn : RedNatTerm eqrel Δ n) :
    RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) n :=
  ⟨RedNatRel eqrel Δ, .nat (idRedWf (.nat hΔ)), hn⟩

theorem redNatTerm_of_RedTerm {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} {n : Term}
    (hΔ : CtxWf Δ) (hn : RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) n) :
    RedNatTerm eqrel Δ n :=
  (RedTerm_of_LogRelAt (.nat (idRedWf (.nat hΔ))) (redNat hΔ)).mp hn

theorem redNatTermEq_of_RedTermEq {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} {n m : Term}
    (hΔ : CtxWf Δ) (hnm : RedTermEq (redNat (eqrel := eqrel) (l := l) hΔ) n m) :
    RedNatTermEq eqrel Δ n m :=
  (RedTermEq_of_LogRelAt (.nat (idRedWf (.nat hΔ))) (redNat hΔ)).mp hnm

theorem invRedNatTerm_suc {eqrel : EqRelSet} {Δ : Context} {n n' : Term}
    (hn : RedNatTerm eqrel Δ n) (d : Star Δ n (.succ n') .nat) :
    eqrel.TermEqRel Δ (.succ n') (.succ n') .nat ∧ RedNatTerm eqrel Δ n' := by
  cases hn with
  | mk _ k d₀ keqk prop₀ =>
      have hk : k = .succ n' :=
        whrDetStarTerm ⟨d₀.reduction, (natural_of_NaturalProp prop₀).toWhnf⟩ ⟨d, .succ⟩
      subst hk
      cases prop₀ with
      | suc hn' => exact ⟨keqk, hn'⟩
      | ne nf => cases nf.neK

theorem invRedNatTerm_zero {eqrel : EqRelSet} {Δ : Context} {n : Term}
    (hn : RedNatTerm eqrel Δ n) (d : Star Δ n .zero .nat) :
    eqrel.TermEqRel Δ .zero .zero .nat := by
  cases hn with
  | mk _ k d₀ keqk prop₀ =>
      have hk : k = .zero :=
        whrDetStarTerm ⟨d₀.reduction, (natural_of_NaturalProp prop₀).toWhnf⟩ ⟨d, .zero⟩
      subst hk
      exact keqk

theorem invRedNatTerm_ne {eqrel : EqRelSet} {Δ : Context} {n n' : Term}
    (hn : RedNatTerm eqrel Δ n) (d : Star Δ n n' .nat) (neN' : Neutral n') :
    eqrel.TermEqRel Δ n' n' .nat ∧ RedNeNf eqrel Δ n' .nat := by
  cases hn with
  | mk _ k d₀ keqk prop₀ =>
      have hk : k = n' :=
        whrDetStarTerm ⟨d₀.reduction, (natural_of_NaturalProp prop₀).toWhnf⟩
          ⟨d, .neutral neN'⟩
      subst hk
      cases prop₀ with
      | suc _ => cases neN'
      | zero => cases neN'
      | ne nf => exact ⟨keqk, nf⟩

/-- Reducibility of natural recursion under a valid substitution (`natrecTerm`). -/
theorem natrecTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ Δ : Context}
    {F z s n : Term} {σ : Subst}
    (hF : ValidType eqrel l (.nat :: Γ) F)
    (hF0 : ValidType eqrel l Γ (subst0 F .zero))
    (hFStep : ValidType eqrel l Γ (recStepType F))
    (hz : ValidTerm hF0 z)
    (hs : ValidTerm hFStep s)
    (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ)
    (hn : RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) n) :
    RedTerm (irrelevance' (singleSubstComp n σ F).symm
      (hF hΔ (consSubstS hΔ hσ (natValid (l := l)) hn)).red)
      (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) n) := by
  have hNat : ValidType eqrel l Γ .nat := natValid (l := l)
  have pσNat : RedType eqrel l Δ .nat := (hNat hΔ hσ).red
  have wfNat : TypeWf Δ .nat := escape pσNat
  have hLiftσ := liftSubstS hΔ hNat hσ
  have pσF := (hF (.cons hΔ wfNat) hLiftσ).red
  have wfF : TypeWf (.nat :: Δ) (subst (liftSubst σ) F) := escape pσF
  have wfz : HasType Δ (subst σ z) (subst0 (subst (liftSubst σ) F) .zero) := by
    have h := escapeTerm (hF0 hΔ hσ).red (hz hΔ hσ).term
    rwa [singleSubstLift F .zero] at h
  have wfs : HasType Δ (subst σ s) (recStepType (subst (liftSubst σ) F)) := by
    have h := escapeTerm (hFStep hΔ hσ).red (hs hΔ hσ).term
    rwa [natrecSucCase σ F] at h
  have hPropF : ∀ {t t'}, RedTerm pσNat t → RedTerm pσNat t' → RedTermEq pσNat t t' →
      TypeEq Δ (subst0 (subst (liftSubst σ) F) t) (subst0 (subst (liftSubst σ) F) t') := by
    intro t t' ht ht' htt'
    have hσt := consSubstS hΔ hσ hNat ht
    have hσt' := consSubstS hΔ hσ hNat ht'
    have hσσt := consSubstSEqNat (reflSubst hσ) pσNat htt'
    have hEq := eqrel.typeToEq (escapeEq (hF hΔ hσt).red ((hF hΔ hσt).eq hσt' hσσt))
    rwa [← singleSubstComp t σ F, ← singleSubstComp t' σ F] at hEq
  have hn_nat : RedNatTerm eqrel Δ n := redNatTerm_of_RedTerm hΔ hn
  exact @RedNatTerm.rec eqrel Δ
    (fun n hn_nat ↦
      RedTerm (irrelevance' (singleSubstComp n σ F).symm
        (hF hΔ (consSubstS hΔ hσ hNat (redTerm_of_RedNatTerm hΔ hn_nat))).red)
        (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) n))
    (fun k _ ↦
      ∀ {m}, k = .succ m → ∀ (hm : RedNatTerm eqrel Δ m),
        RedTerm (irrelevance' (singleSubstComp m σ F).symm
          (hF hΔ (consSubstS hΔ hσ hNat (redTerm_of_RedNatTerm hΔ hm))).red)
          (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m))
    (fun n k d n_eq_n prop ih_prop ↦ by
      have hn_red : RedTerm pσNat n :=
        redTerm_of_RedNatTerm hΔ (.mk n k d n_eq_n prop)
      have pσFn' := (hF hΔ (consSubstS hΔ hσ hNat hn_red)).red
      have pσFn := irrelevance' (singleSubstComp n σ F).symm pσFn'
      cases prop with
      | @suc m hm_nat =>
          have hm : RedTerm pσNat m := redTerm_of_RedNatTerm hΔ hm_nat
          have wfm : HasType Δ m .nat := escapeTerm pσNat hm
          have hσsm : RedTerm pσNat (.succ m) :=
            redTerm_of_RedNatTerm hΔ
              (.mk (.succ m) (.succ m) (idRedTermWf (.succ wfm)) n_eq_n (.suc hm_nat))
          rcases redSubstStarTerm d.reduction pσNat hσsm with ⟨_, hσn_eq_σsm⟩
          have pσFsm := irrelevance' (singleSubstComp (.succ m) σ F).symm
            (hF hΔ (consSubstS hΔ hσ hNat hσsm)).red
          have hFn_eq_Fsm : RedEq pσFn (subst0 (subst (liftSubst σ) F) (.succ m)) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (singleSubstComp (.succ m) σ F).symm
              pσFn' pσFn
              ((hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
                (consSubstS hΔ hσ hNat hσsm)
                (consSubstSEqNat (reflSubst hσ) pσNat hσn_eq_σsm))
          have pσFm := irrelevance' (singleSubstComp m σ F).symm
            (hF hΔ (consSubstS hΔ hσ hNat hm)).red
          have pσFsm' := irrelevance' (natrecIrrelevantSubst F z s m σ)
            (hF hΔ (consSubstS hΔ hσ hNat hσsm)).red
          have pσFStep : RedType eqrel l Δ (subst σ (recStepType F)) :=
            (hFStep hΔ hσ).red
          have hs_term : RedTerm pσFStep (subst σ s) :=
            (hs hΔ hσ).term
          have pσFStep_m : RedType eqrel l Δ
              (.pi (subst0 (subst (liftSubst σ) F) m)
                (subst (liftSubst (sgSubst m))
                  (subst (liftSubst (liftSubst σ))
                    (wk1 (substKeep F (.succ (.var 0))))))) :=
            substSPi₁ pσFStep pσNat hm
          have ih_m := ih_prop rfl hm_nat
          have natrecM := appTerm pσFm pσFsm' pσFStep_m
            (appTerm pσNat pσFStep_m pσFStep hs_term hm) ih_m
          have natrecM' : RedTerm pσFsm
              (.app (.app (subst σ s) m) (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m)) :=
            irrelevanceTerm'
              ((natrecIrrelevantSubst F z s m σ).symm.trans (singleSubstComp (.succ m) σ F).symm)
              pσFsm' pσFsm natrecM
          have hRed1 := natrecSubstStar wfF wfz wfs d.reduction pσNat hσsm hPropF
          have hRed2 : Star Δ
              (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) (.succ m))
              (.app (.app (subst σ s) m) (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) m))
              (subst0 (subst (liftSubst σ) F) n) :=
            (Star.step (.natrecSucc wfm wfF wfz wfs)
              (.refl (escapeTerm pσFsm natrecM'))).conv
              (.symm (eqrel.typeToEq (escapeEq pσFn hFn_eq_Fsm)))
          exact (redSubstStarTerm (hRed1.trans hRed2) pσFn
            (convTerm₂ pσFn pσFsm hFn_eq_Fsm natrecM')).1
      | zero =>
          have hσ0 : RedTerm pσNat .zero :=
            redTerm_of_RedNatTerm hΔ (.mk .zero .zero (idRedTermWf (.zero hΔ)) n_eq_n .zero)
          rcases redSubstStarTerm d.reduction pσNat hσ0 with ⟨_, hσn_eq_σ0⟩
          have hFn_eq_F0_raw :=
            (hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
              (consSubstS hΔ hσ hNat hσ0)
              (consSubstSEqNat (reflSubst hσ) pσNat hσn_eq_σ0)
          have hFn_eq_F0 : RedEq pσFn (subst σ (subst0 F .zero)) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (substConsId F)
              pσFn' pσFn hFn_eq_F0_raw
          have hFn_eq_F0'' : RedEq pσFn (subst0 (subst (liftSubst σ) F) .zero) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (singleSubstComp .zero σ F).symm
              pσFn' pσFn hFn_eq_F0_raw
          have hRed1 := natrecSubstStar wfF wfz wfs d.reduction pσNat hσ0 hPropF
          have hRed2 : Star Δ
              (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) .zero)
              (subst σ z)
              (subst0 (subst (liftSubst σ) F) n) :=
            (Star.step (.natrecZero wfF wfz wfs) (.refl wfz)).conv
              (.symm (eqrel.typeToEq (escapeEq pσFn hFn_eq_F0'')))
          exact (redSubstStarTerm (hRed1.trans hRed2) pσFn
            (convTerm₂ pσFn (hF0 hΔ hσ).red hFn_eq_F0 (hz hΔ hσ).term)).1
      | ne nf =>
          have hσm : RedTerm pσNat k :=
            neuTerm pσNat nf.neK nf.hk nf.keqk
          rcases redSubstStarTerm d.reduction pσNat hσm with ⟨_, hσn_eq_σm⟩
          have pσFm := irrelevance' (singleSubstComp k σ F).symm
            (hF hΔ (consSubstS hΔ hσ hNat hσm)).red
          have hFn_eq_Fm : RedEq pσFn (subst0 (subst (liftSubst σ) F) k) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (singleSubstComp k σ F).symm
              pσFn' pσFn
              ((hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
                (consSubstS hΔ hσ hNat hσm)
                (consSubstSEqNat (reflSubst hσ) pσNat hσn_eq_σm))
          have wfFF : eqrel.TypeEqRel (.nat :: Δ) (subst (liftSubst σ) F) (subst (liftSubst σ) F) :=
            escapeEq pσF (reflEq pσF)
          have wfzz : eqrel.TermEqRel Δ (subst σ z) (subst σ z) (subst0 (subst (liftSubst σ) F) .zero) := by
            have h := escapeTermEq (hF0 hΔ hσ).red (reflEqTerm (hF0 hΔ hσ).red (hz hΔ hσ).term)
            rwa [singleSubstLift F .zero] at h
          have wfss : eqrel.TermEqRel Δ (subst σ s) (subst σ s) (recStepType (subst (liftSubst σ) F)) := by
            have h := escapeTermEq (hFStep hΔ hσ).red (reflEqTerm (hFStep hΔ hσ).red (hs hΔ hσ).term)
            rwa [natrecSucCase σ F] at h
          have natrecM : RedTerm pσFm (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) k) :=
            neuTerm pσFm (.natrec nf.neK) (.natrec wfF wfz wfs nf.hk)
              (eqrel.natrecCong wfFF wfzz wfss nf.keqk)
          have hRed := natrecSubstStar wfF wfz wfs d.reduction pσNat hσm hPropF
          exact (redSubstStarTerm hRed pσFn (convTerm₂ pσFn pσFm hFn_eq_Fm natrecM)).1)
    (fun {_} _ ih {m'} heq _ ↦ by injection heq with h; subst h; exact ih)
    (fun {m'} heq ↦ by cases heq)
    (fun {_} nf {m'} heq ↦ by subst heq; cases nf.neK)
    n hn_nat
/-- Reducibility of natural recursion congruence under a valid substitution equality
(`natrec-congTerm`). -/
theorem natrecCongTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ Δ : Context}
    {F F' z z' s s' n m : Term} {σ σ' : Subst}
    (hF : ValidType eqrel l (.nat :: Γ) F)
    (hF' : ValidType eqrel l (.nat :: Γ) F')
    (hFF' : ValidTypeEq hF F')
    (hF0 : ValidType eqrel l Γ (subst0 F .zero))
    (hF'0 : ValidType eqrel l Γ (subst0 F' .zero))
    (_hF0F'0 : ValidTypeEq hF0 (subst0 F' .zero))
    (hFStep : ValidType eqrel l Γ (recStepType F))
    (hF'Step : ValidType eqrel l Γ (recStepType F'))
    (_hFStepEq : ValidTypeEq hFStep (recStepType F'))
    (hz : ValidTerm hF0 z)
    (hz' : ValidTerm hF'0 z')
    (hzz' : ValidTermEq hF0 z z')
    (hs : ValidTerm hFStep s)
    (hs' : ValidTerm hF'Step s')
    (hss' : ValidTermEq hFStep s s')
    (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ)
    (hσ' : ValidSubst eqrel Δ σ' Γ)
    (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ)
    (hn : RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) n)
    (hm : RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) m)
    (hnm : RedTermEq (redNat (eqrel := eqrel) (l := l) hΔ) n m) :
    RedTermEq (irrelevance' (singleSubstComp n σ F).symm
      (hF hΔ (consSubstS hΔ hσ (natValid (l := l)) hn)).red)
      (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) n)
      (.natrec (subst (liftSubst σ') F') (subst σ' z') (subst σ' s') m) := by
  have hNat : ValidType eqrel l Γ .nat := natValid (l := l)
  have pσNat : RedType eqrel l Δ .nat := (hNat hΔ hσ).red
  have pσ'Nat : RedType eqrel l Δ .nat := (hNat hΔ hσ').red
  have wfNat : TypeWf Δ .nat := escape pσNat
  have wfNat' : TypeWf Δ .nat := escape pσ'Nat
  have hLiftσ := liftSubstS hΔ hNat hσ
  have hLiftσ' := liftSubstS hΔ hNat hσ'
  have pσF := (hF (.cons hΔ wfNat) hLiftσ).red
  have pσ'F := (hF (.cons hΔ wfNat) hLiftσ').red
  have pσ'F' := (hF' (.cons hΔ wfNat') hLiftσ').red
  have wfF : TypeWf (.nat :: Δ) (subst (liftSubst σ) F) := escape pσF
  have wfF' : TypeWf (.nat :: Δ) (subst (liftSubst σ') F') := escape pσ'F'
  have wfz : HasType Δ (subst σ z) (subst0 (subst (liftSubst σ) F) .zero) := by
    have h := escapeTerm (hF0 hΔ hσ).red (hz hΔ hσ).term
    rwa [singleSubstLift F .zero] at h
  have wfs : HasType Δ (subst σ s) (recStepType (subst (liftSubst σ) F)) := by
    have h := escapeTerm (hFStep hΔ hσ).red (hs hΔ hσ).term
    rwa [natrecSucCase σ F] at h
  have wfz' : HasType Δ (subst σ' z') (subst0 (subst (liftSubst σ') F') .zero) := by
    have h := escapeTerm (hF'0 hΔ hσ').red (hz' hΔ hσ').term
    rwa [singleSubstLift F' .zero] at h
  have wfs' : HasType Δ (subst σ' s') (recStepType (subst (liftSubst σ') F')) := by
    have h := escapeTerm (hF'Step hΔ hσ').red (hs' hΔ hσ').term
    rwa [natrecSucCase σ' F'] at h
  have hPropF : ∀ {t t'}, RedTerm pσNat t → RedTerm pσNat t' → RedTermEq pσNat t t' →
      TypeEq Δ (subst0 (subst (liftSubst σ) F) t) (subst0 (subst (liftSubst σ) F) t') := by
    intro t t' ht ht' htt'
    have hEq := eqrel.typeToEq (escapeEq (hF hΔ (consSubstS hΔ hσ hNat ht)).red
      ((hF hΔ (consSubstS hΔ hσ hNat ht)).eq
        (consSubstS hΔ hσ hNat ht')
        (consSubstSEqNat (reflSubst hσ) pσNat htt')))
    rwa [← singleSubstComp t σ F, ← singleSubstComp t' σ F] at hEq
  have hPropF' : ∀ {t t'}, RedTerm pσ'Nat t → RedTerm pσ'Nat t' → RedTermEq pσ'Nat t t' →
      TypeEq Δ (subst0 (subst (liftSubst σ') F') t) (subst0 (subst (liftSubst σ') F') t') := by
    intro t t' ht ht' htt'
    have hEq := eqrel.typeToEq (escapeEq (hF' hΔ (consSubstS hΔ hσ' hNat ht)).red
      ((hF' hΔ (consSubstS hΔ hσ' hNat ht)).eq
        (consSubstS hΔ hσ' hNat ht')
        (consSubstSEqNat (reflSubst hσ') pσ'Nat htt')))
    rwa [← singleSubstComp t σ' F', ← singleSubstComp t' σ' F'] at hEq
  have hn_nat := redNatTerm_of_RedTerm hΔ hn
  have hm_nat := redNatTerm_of_RedTerm hΔ hm
  have hnm_nat := redNatTermEq_of_RedTermEq hΔ hnm
  exact @RedNatTermEq.rec eqrel Δ
    (fun n m _ ↦
      ∀ (hn_nat : RedNatTerm eqrel Δ n) (hm_nat : RedNatTerm eqrel Δ m),
        RedTermEq (irrelevance' (singleSubstComp n σ F).symm
          (hF hΔ (consSubstS hΔ hσ hNat (redTerm_of_RedNatTerm hΔ hn_nat))).red)
          (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) n)
          (.natrec (subst (liftSubst σ') F') (subst σ' z') (subst σ' s') m))
    (fun k k' _ ↦
      ∀ {n' m'}, k = .succ n' → k' = .succ m' →
        ∀ (hn'_nat : RedNatTerm eqrel Δ n') (hm'_nat : RedNatTerm eqrel Δ m'),
          RedTermEq (irrelevance' (singleSubstComp n' σ F).symm
            (hF hΔ (consSubstS hΔ hσ hNat (redTerm_of_RedNatTerm hΔ hn'_nat))).red)
            (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) n')
            (.natrec (subst (liftSubst σ') F') (subst σ' z') (subst σ' s') m'))
    (fun n m k k' d d' keqk' prop ih_prop hn_nat hm_nat ↦ by
      have hn_red : RedTerm pσNat n := redTerm_of_RedNatTerm hΔ hn_nat
      have hm_red : RedTerm pσ'Nat m := redTerm_of_RedNatTerm hΔ hm_nat
      have hnm_red : RedTermEq pσNat n m :=
        ⟨RedNatRel eqrel Δ, .nat (idRedWf (.nat hΔ)), .mk n m k k' d d' keqk' prop⟩
      have pσFn' := (hF hΔ (consSubstS hΔ hσ hNat hn_red)).red
      have pσFn := irrelevance' (singleSubstComp n σ F).symm pσFn'
      have pσ'F'm' := (hF' hΔ (consSubstS hΔ hσ' hNat hm_red)).red
      have pσ'F'm := irrelevance' (singleSubstComp m σ' F').symm pσ'F'm'
      have pσ'Fm' := (hF hΔ (consSubstS hΔ hσ' hNat hm_red)).red
      have pσ'Fm := irrelevance' (singleSubstComp m σ' F).symm pσ'Fm'
      have hσFn_eq_σ'Fm : RedEq pσFn (subst0 (subst (liftSubst σ') F) m) :=
        irrelevanceEq'' (singleSubstComp n σ F).symm (singleSubstComp m σ' F).symm
          pσFn' pσFn
          ((hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
            (consSubstS hΔ hσ' hNat hm_red)
            (consSubstSEqNat hσσ' pσNat hnm_red))
      have hσ'Fm_eq_σ'F'm : RedEq pσ'Fm (subst0 (subst (liftSubst σ') F') m) :=
        irrelevanceEq'' (singleSubstComp m σ' F).symm (singleSubstComp m σ' F').symm
          pσ'Fm' pσ'Fm (hFF' hΔ (consSubstS hΔ hσ' hNat hm_red))
      have hσFn_eq_σ'F'm : RedEq pσFn (subst0 (subst (liftSubst σ') F') m) :=
        transEq pσFn pσ'Fm pσ'F'm hσFn_eq_σ'Fm hσ'Fm_eq_σ'F'm
      cases prop with
      | @suc n' m' hnm'_nat =>
          rcases invRedNatTerm_suc hn_nat d.reduction with ⟨sn'_eq, hn'_nat⟩
          rcases invRedNatTerm_suc hm_nat d'.reduction with ⟨sm'_eq, hm'_nat⟩
          have hn'_red : RedTerm pσNat n' := redTerm_of_RedNatTerm hΔ hn'_nat
          have hm'_red : RedTerm pσ'Nat m' := redTerm_of_RedNatTerm hΔ hm'_nat
          have hn'm'_red : RedTermEq pσNat n' m' :=
            ⟨RedNatRel eqrel Δ, .nat (idRedWf (.nat hΔ)), hnm'_nat⟩
          have wfn' : HasType Δ n' .nat := escapeTerm pσNat hn'_red
          have wfm' : HasType Δ m' .nat := escapeTerm pσ'Nat hm'_red
          have hσsn' : RedTerm pσNat (.succ n') :=
            redTerm_of_RedNatTerm hΔ
              (.mk (.succ n') (.succ n') (idRedTermWf (.succ wfn')) sn'_eq (.suc hn'_nat))
          have hσ'sm' : RedTerm pσ'Nat (.succ m') :=
            redTerm_of_RedNatTerm hΔ
              (.mk (.succ m') (.succ m') (idRedTermWf (.succ wfm')) sm'_eq (.suc hm'_nat))
          rcases redSubstStarTerm d.reduction pσNat hσsn' with ⟨_, hσn_eq_σsn'⟩
          rcases redSubstStarTerm d'.reduction pσ'Nat hσ'sm' with ⟨_, hσ'm_eq_σ'sm'⟩
          have pσFsn' := irrelevance' (singleSubstComp (.succ n') σ F).symm
            (hF hΔ (consSubstS hΔ hσ hNat hσsn')).red
          have hFn_eq_Fsn' : RedEq pσFn (subst0 (subst (liftSubst σ) F) (.succ n')) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (singleSubstComp (.succ n') σ F).symm
              pσFn' pσFn
              ((hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
                (consSubstS hΔ hσ hNat hσsn')
                (consSubstSEqNat (reflSubst hσ) pσNat hσn_eq_σsn'))
          have hFn_eq_Fsn'' :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (natrecIrrelevantSubst F z s n' σ)
              pσFn' pσFn
              ((hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
                (consSubstS hΔ hσ hNat hσsn')
                (consSubstSEqNat (reflSubst hσ) pσNat hσn_eq_σsn'))
          have pσFn'_step := irrelevance' (singleSubstComp n' σ F).symm
            (hF hΔ (consSubstS hΔ hσ hNat hn'_red)).red
          have pσFsn'' := irrelevance' (natrecIrrelevantSubst F z s n' σ)
            (hF hΔ (consSubstS hΔ hσ hNat hσsn')).red
          have pσFStep_red : RedType eqrel l Δ (subst σ (recStepType F)) := (hFStep hΔ hσ).red
          have pσFStep_n' : RedType eqrel l Δ
              (.pi (subst0 (subst (liftSubst σ) F) n')
                (subst (liftSubst (sgSubst n'))
                  (subst (liftSubst (liftSubst σ))
                    (wk1 (substKeep F (.succ (.var 0))))))) :=
            substSPi₁ pσFStep_red pσNat hn'_red
          have pσ'F'sm' := irrelevance' (singleSubstComp (.succ m') σ' F').symm
            (hF' hΔ (consSubstS hΔ hσ' hNat hσ'sm')).red
          have hF'm_eq_F'sm' : RedEq pσ'F'm (subst0 (subst (liftSubst σ') F') (.succ m')) :=
            irrelevanceEq'' (singleSubstComp m σ' F').symm (singleSubstComp (.succ m') σ' F').symm
              pσ'F'm' pσ'F'm
              ((hF' hΔ (consSubstS hΔ hσ' hNat hm_red)).eq
                (consSubstS hΔ hσ' hNat hσ'sm')
                (consSubstSEqNat (reflSubst hσ') pσ'Nat hσ'm_eq_σ'sm'))
          have pσ'Fm'_step := irrelevance' (singleSubstComp m' σ' F).symm
            (hF hΔ (consSubstS hΔ hσ' hNat hm'_red)).red
          have pσ'F'm'_step := irrelevance' (singleSubstComp m' σ' F').symm
            (hF' hΔ (consSubstS hΔ hσ' hNat hm'_red)).red
          have pσ'F'sm'' := irrelevance' (natrecIrrelevantSubst F' z' s' m' σ')
            (hF' hΔ (consSubstS hΔ hσ' hNat hσ'sm')).red
          have pσ'F'Step_red : RedType eqrel l Δ (subst σ' (recStepType F')) := (hF'Step hΔ hσ').red
          have pσ'F'Step_m' : RedType eqrel l Δ
              (.pi (subst0 (subst (liftSubst σ') F') m')
                (subst (liftSubst (sgSubst m'))
                  (subst (liftSubst (liftSubst σ'))
                    (wk1 (substKeep F' (.succ (.var 0))))))) :=
            substSPi₁ pσ'F'Step_red pσ'Nat hm'_red
          have hσFn'_eq_σ'Fm' : RedEq pσFn'_step (subst0 (subst (liftSubst σ') F) m') :=
            irrelevanceEq'' (singleSubstComp n' σ F).symm (singleSubstComp m' σ' F).symm
              (hF hΔ (consSubstS hΔ hσ hNat hn'_red)).red pσFn'_step
              ((hF hΔ (consSubstS hΔ hσ hNat hn'_red)).eq
                (consSubstS hΔ hσ' hNat hm'_red)
                (consSubstSEqNat hσσ' pσNat hn'm'_red))
          have hσ'Fm'_eq_σ'F'm' : RedEq pσ'Fm'_step (subst0 (subst (liftSubst σ') F') m') :=
            irrelevanceEq'' (singleSubstComp m' σ' F).symm (singleSubstComp m' σ' F').symm
              (hF hΔ (consSubstS hΔ hσ' hNat hm'_red)).red pσ'Fm'_step
              (hFF' hΔ (consSubstS hΔ hσ' hNat hm'_red))
          have hσFn'_eq_σ'F'm' : RedEq pσFn'_step (subst0 (subst (liftSubst σ') F') m') :=
            transEq pσFn'_step pσ'Fm'_step pσ'F'm'_step hσFn'_eq_σ'Fm' hσ'Fm'_eq_σ'F'm'
          have hs_term : RedTerm pσFStep_red (subst σ s) := (hs hΔ hσ).term
          have hs'_term : RedTerm pσ'F'Step_red (subst σ' s') := (hs' hΔ hσ').term
          have natrec_n' := natrecTerm hF hF0 hFStep hz hs hΔ hσ hn'_red
          have natrec_m' := natrecTerm hF' hF'0 hF'Step hz' hs' hΔ hσ' hm'_red
          have natrecN := appTerm pσFn'_step pσFsn'' pσFStep_n'
            (appTerm pσNat pσFStep_n' pσFStep_red hs_term hn'_red) natrec_n'
          have natrecN' : RedTerm pσFsn'
              (.app (.app (subst σ s) n') (.natrec (subst (liftSubst σ) F) (subst σ z) (subst σ s) n')) :=
            irrelevanceTerm'
              ((natrecIrrelevantSubst F z s n' σ).symm.trans (singleSubstComp (.succ n') σ F).symm)
              pσFsn'' pσFsn' natrecN
          have natrecM := appTerm pσ'F'm'_step pσ'F'sm'' pσ'F'Step_m'
            (appTerm pσ'Nat pσ'F'Step_m' pσ'F'Step_red hs'_term hm'_red) natrec_m'
          have natrecM' : RedTerm pσ'F'sm'
              (.app (.app (subst σ' s') m') (.natrec (subst (liftSubst σ') F') (subst σ' z') (subst σ' s') m')) :=
            irrelevanceTerm'
              ((natrecIrrelevantSubst F' z' s' m' σ').symm.trans (singleSubstComp (.succ m') σ' F').symm)
              pσ'F'sm'' pσ'F'sm' natrecM
          have hσs_eq_σ's := (hs hΔ hσ).eq hσ' hσσ'
          have hσ's_eq_σ's' := convEqTerm₂ (hFStep hΔ hσ).red (hFStep hΔ hσ').red
            ((hFStep hΔ hσ).eq hσ' hσσ') (hss' hΔ hσ')
          have hσs_eq_σ's' : RedTermEq pσFStep_red (subst σ s) (subst σ' s') :=
            transEqTerm pσFStep_red hσs_eq_σ's hσ's_eq_σ's'
          have ih_n'm' := ih_prop rfl rfl hn'_nat hm'_nat
          have appEq := convEqTerm₂ pσFn pσFsn'' hFn_eq_Fsn''
            (appCongTerm pσFn'_step pσFsn'' pσFStep_n'
              (appCongTerm (G := subst (liftSubst σ) (.pi F (wk1 (substKeep F (.succ (.var 0)))))) (u := n')
                pσNat pσFStep_n' pσFStep_red hσs_eq_σ's' hn'_red hm'_red hn'm'_red)
              natrec_n'
              (convTerm₂ pσFn'_step pσ'F'm'_step hσFn'_eq_σ'F'm' natrec_m')
              ih_n'm')
          have hRed1 := (natrecSubstStar wfF wfz wfs d.reduction pσNat hσsn' hPropF).trans
            ((Star.step (.natrecSucc wfn' wfF wfz wfs)
              (.refl (escapeTerm pσFsn' natrecN'))).conv
              (.symm (eqrel.typeToEq (escapeEq pσFn hFn_eq_Fsn'))))
          have hRed2 := (natrecSubstStar wfF' wfz' wfs' d'.reduction pσ'Nat hσ'sm' hPropF').trans
            ((Star.step (.natrecSucc wfm' wfF' wfz' wfs')
              (.refl (escapeTerm pσ'F'sm' natrecM'))).conv
              (.symm (eqrel.typeToEq (escapeEq pσ'F'm hF'm_eq_F'sm'))))
          have eq₁ := (redSubstStarTerm hRed1 pσFn (convTerm₂ pσFn pσFsn' hFn_eq_Fsn' natrecN')).2
          have eq₂ := (redSubstStarTerm hRed2 pσ'F'm (convTerm₂ pσ'F'm pσ'F'sm' hF'm_eq_F'sm' natrecM')).2
          exact transEqTerm pσFn eq₁
            (transEqTerm pσFn appEq
              (convEqTerm₂ pσFn pσ'F'm hσFn_eq_σ'F'm (symEqTerm pσ'F'm eq₂)))
      | zero =>
          have z_eq := invRedNatTerm_zero hn_nat d.reduction
          have z'_eq := invRedNatTerm_zero hm_nat d'.reduction
          have hσ0 : RedTerm pσNat .zero :=
            redTerm_of_RedNatTerm hΔ (.mk .zero .zero (idRedTermWf (.zero hΔ)) z_eq .zero)
          have hσ'0 : RedTerm pσ'Nat .zero :=
            redTerm_of_RedNatTerm hΔ (.mk .zero .zero (idRedTermWf (.zero hΔ)) z'_eq .zero)
          rcases redSubstStarTerm d.reduction pσNat hσ0 with ⟨_, hσn_eq_σ0⟩
          rcases redSubstStarTerm d'.reduction pσ'Nat hσ'0 with ⟨_, hσ'm_eq_σ'0⟩
          have hσn_eq_σ'0 : RedTermEq pσNat n .zero :=
            transEqTerm pσNat hnm_red hσ'm_eq_σ'0
          have hFn_eq_F0_raw :=
            (hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
              (consSubstS hΔ hσ hNat hσ0)
              (consSubstSEqNat (reflSubst hσ) pσNat hσn_eq_σ0)
          have hFn_eq_F0 : RedEq pσFn (subst σ (subst0 F .zero)) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (substConsId F) pσFn' pσFn hFn_eq_F0_raw
          have hFn_eq_F0'' : RedEq pσFn (subst0 (subst (liftSubst σ) F) .zero) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (singleSubstComp .zero σ F).symm
              pσFn' pσFn hFn_eq_F0_raw
          have hσFn_eq_σ'F0_raw :=
            (hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
              (consSubstS hΔ hσ' hNat hσ'0)
              (consSubstSEqNat hσσ' pσNat hσn_eq_σ'0)
          have hσFn_eq_σ'F0 : RedEq pσFn (subst σ' (subst0 F .zero)) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (substConsId F) pσFn' pσFn hσFn_eq_σ'F0_raw
          have hF'm_eq_F'0_raw :=
            (hF' hΔ (consSubstS hΔ hσ' hNat hm_red)).eq
              (consSubstS hΔ hσ' hNat hσ'0)
              (consSubstSEqNat (reflSubst hσ') pσ'Nat hσ'm_eq_σ'0)
          have hF'm_eq_F'0 : RedEq pσ'F'm (subst σ' (subst0 F' .zero)) :=
            irrelevanceEq'' (singleSubstComp m σ' F').symm (substConsId F') pσ'F'm' pσ'F'm hF'm_eq_F'0_raw
          have hF'm_eq_F'0'' : RedEq pσ'F'm (subst0 (subst (liftSubst σ') F') .zero) :=
            irrelevanceEq'' (singleSubstComp m σ' F').symm (singleSubstComp .zero σ' F').symm
              pσ'F'm' pσ'F'm hF'm_eq_F'0_raw
          have hσz_eq_σ'z := convEqTerm₂ pσFn (hF0 hΔ hσ).red hFn_eq_F0 ((hz hΔ hσ).eq hσ' hσσ')
          have hσ'z_eq_σ'z' := convEqTerm₂ pσFn (hF0 hΔ hσ').red hσFn_eq_σ'F0 (hzz' hΔ hσ')
          have hσz_eq_σ'z' := transEqTerm pσFn hσz_eq_σ'z hσ'z_eq_σ'z'
          have hRed1 := (natrecSubstStar wfF wfz wfs d.reduction pσNat hσ0 hPropF).trans
            ((Star.step (.natrecZero wfF wfz wfs) (.refl wfz)).conv
              (.symm (eqrel.typeToEq (escapeEq pσFn hFn_eq_F0''))))
          have hRed2 := (natrecSubstStar wfF' wfz' wfs' d'.reduction pσ'Nat hσ'0 hPropF').trans
            ((Star.step (.natrecZero wfF' wfz' wfs') (.refl wfz')).conv
              (.symm (eqrel.typeToEq (escapeEq pσ'F'm hF'm_eq_F'0''))))
          have eq₁ := (redSubstStarTerm hRed1 pσFn (convTerm₂ pσFn (hF0 hΔ hσ).red hFn_eq_F0 (hz hΔ hσ).term)).2
          have eq₂ := (redSubstStarTerm hRed2 pσ'F'm (convTerm₂ pσ'F'm (hF'0 hΔ hσ').red hF'm_eq_F'0 (hz' hΔ hσ').term)).2
          exact transEqTerm pσFn eq₁
            (transEqTerm pσFn hσz_eq_σ'z'
              (convEqTerm₂ pσFn pσ'F'm hσFn_eq_σ'F'm (symEqTerm pσ'F'm eq₂)))
      | ne nf =>
          rcases invRedNatTerm_ne hn_nat d.reduction nf.neK with ⟨_, nfN⟩
          rcases invRedNatTerm_ne hm_nat d'.reduction nf.neM with ⟨_, nfM⟩
          have hσn' : RedTerm pσNat k := neuTerm pσNat nfN.neK nfN.hk nfN.keqk
          have hσ'm' : RedTerm pσ'Nat k' := neuTerm pσ'Nat nfM.neK nfM.hk nfM.keqk
          rcases redSubstStarTerm d.reduction pσNat hσn' with ⟨_, hσn_eq_σn'⟩
          rcases redSubstStarTerm d'.reduction pσ'Nat hσ'm' with ⟨_, hσ'm_eq_σ'm'⟩
          have pσFn'_ne := irrelevance' (singleSubstComp k σ F).symm
            (hF hΔ (consSubstS hΔ hσ hNat hσn')).red
          have hFn_eq_Fn' : RedEq pσFn (subst0 (subst (liftSubst σ) F) k) :=
            irrelevanceEq'' (singleSubstComp n σ F).symm (singleSubstComp k σ F).symm
              pσFn' pσFn
              ((hF hΔ (consSubstS hΔ hσ hNat hn_red)).eq
                (consSubstS hΔ hσ hNat hσn')
                (consSubstSEqNat (reflSubst hσ) pσNat hσn_eq_σn'))
          have pσ'F'm'_ne := irrelevance' (singleSubstComp k' σ' F').symm
            (hF' hΔ (consSubstS hΔ hσ' hNat hσ'm')).red
          have hF'm_eq_F'm' : RedEq pσ'F'm (subst0 (subst (liftSubst σ') F') k') :=
            irrelevanceEq'' (singleSubstComp m σ' F').symm (singleSubstComp k' σ' F').symm
              pσ'F'm' pσ'F'm
              ((hF' hΔ (consSubstS hΔ hσ' hNat hm_red)).eq
                (consSubstS hΔ hσ' hNat hσ'm')
                (consSubstSEqNat (reflSubst hσ') pσ'Nat hσ'm_eq_σ'm'))
          have hσFn'_eq_σ'Fm'_ne : RedEq pσFn'_ne (subst0 (subst (liftSubst σ') F') k') :=
            transEq pσFn'_ne pσFn pσ'F'm'_ne (symEq pσFn pσFn'_ne hFn_eq_Fn')
              (transEq pσFn pσ'F'm pσ'F'm'_ne hσFn_eq_σ'F'm hF'm_eq_F'm')
          have wfFF := escapeEq pσF (reflEq pσF)
          have wfzz : eqrel.TermEqRel Δ (subst σ z) (subst σ z) (subst0 (subst (liftSubst σ) F) .zero) := by
            have h := escapeTermEq (hF0 hΔ hσ).red (reflEqTerm (hF0 hΔ hσ).red (hz hΔ hσ).term)
            rwa [singleSubstLift F .zero] at h
          have wfss : eqrel.TermEqRel Δ (subst σ s) (subst σ s) (recStepType (subst (liftSubst σ) F)) := by
            have h := escapeTermEq (hFStep hΔ hσ).red (reflEqTerm (hFStep hΔ hσ).red (hs hΔ hσ).term)
            rwa [natrecSucCase σ F] at h
          have wfF'F' := escapeEq pσ'F' (reflEq pσ'F')
          have wfz'z' : eqrel.TermEqRel Δ (subst σ' z') (subst σ' z') (subst0 (subst (liftSubst σ') F') .zero) := by
            have h := escapeTermEq (hF'0 hΔ hσ').red (reflEqTerm (hF'0 hΔ hσ').red (hz' hΔ hσ').term)
            rwa [singleSubstLift F' .zero] at h
          have wfs's' : eqrel.TermEqRel Δ (subst σ' s') (subst σ' s') (recStepType (subst (liftSubst σ') F')) := by
            have h := escapeTermEq (hF'Step hΔ hσ').red (reflEqTerm (hF'Step hΔ hσ').red (hs' hΔ hσ').term)
            rwa [natrecSucCase σ' F'] at h
          have hσF_eq_σ'F : eqrel.TypeEqRel (.nat :: Δ) (subst (liftSubst σ) F) (subst (liftSubst σ') F) :=
            escapeEq pσF ((hF (.cons hΔ wfNat) hLiftσ).eq hLiftσ' (liftSubstSEq hΔ hNat hσ hσσ'))
          have hσ'F_eq_σ'F' : eqrel.TypeEqRel (.nat :: Δ) (subst (liftSubst σ') F) (subst (liftSubst σ') F') :=
            escapeEq pσ'F (hFF' (.cons hΔ wfNat) hLiftσ')
          have hFF'_syn : eqrel.TypeEqRel (.nat :: Δ) (subst (liftSubst σ) F) (subst (liftSubst σ') F') :=
            eqrel.transType hσF_eq_σ'F hσ'F_eq_σ'F'
          have hσz_eq_σ'z : eqrel.TermEqRel Δ (subst σ z) (subst σ' z) (subst0 (subst (liftSubst σ) F) .zero) := by
            have h := escapeTermEq (hF0 hΔ hσ).red ((hz hΔ hσ).eq hσ' hσσ')
            rwa [singleSubstLift F .zero] at h
          have hσ'z_eq_σ'z' : eqrel.TermEqRel Δ (subst σ' z) (subst σ' z') (subst0 (subst (liftSubst σ) F) .zero) := by
            have h := eqrel.convTerm (escapeTermEq (hF0 hΔ hσ').red (hzz' hΔ hσ'))
              (.symm (eqrel.typeToEq (escapeEq (hF0 hΔ hσ).red ((hF0 hΔ hσ).eq hσ' hσσ'))))
            rwa [singleSubstLift F .zero] at h
          have hzz'_syn : eqrel.TermEqRel Δ (subst σ z) (subst σ' z') (subst0 (subst (liftSubst σ) F) .zero) :=
            eqrel.transTerm hσz_eq_σ'z hσ'z_eq_σ'z'
          have hσs_eq_σ's : eqrel.TermEqRel Δ (subst σ s) (subst σ' s) (recStepType (subst (liftSubst σ) F)) := by
            have h := escapeTermEq (hFStep hΔ hσ).red ((hs hΔ hσ).eq hσ' hσσ')
            rwa [natrecSucCase σ F] at h
          have hσ's_eq_σ's' : eqrel.TermEqRel Δ (subst σ' s) (subst σ' s') (recStepType (subst (liftSubst σ) F)) := by
            have h := eqrel.convTerm (escapeTermEq (hFStep hΔ hσ').red (hss' hΔ hσ'))
              (.symm (eqrel.typeToEq (escapeEq (hFStep hΔ hσ).red ((hFStep hΔ hσ).eq hσ' hσσ'))))
            rwa [natrecSucCase σ F] at h
          have hss'_syn : eqrel.TermEqRel Δ (subst σ s) (subst σ' s') (recStepType (subst (liftSubst σ) F)) :=
            eqrel.transTerm hσs_eq_σ's hσ's_eq_σ's'
          have natrecN := neuTerm pσFn'_ne (.natrec nfN.neK) (.natrec wfF wfz wfs nfN.hk)
            (eqrel.natrecCong wfFF wfzz wfss nfN.keqk)
          have natrecM := neuTerm pσ'F'm'_ne (.natrec nfM.neK) (.natrec wfF' wfz' wfs' nfM.hk)
            (eqrel.natrecCong wfF'F' wfz'z' wfs's' nfM.keqk)
          have natrecN_eq_M := convEqTerm₂ pσFn pσFn'_ne hFn_eq_Fn'
            (neuEqTerm pσFn'_ne (.natrec nfN.neK) (.natrec nfM.neK)
              (.natrec wfF wfz wfs nfN.hk)
              (.conv (.natrec wfF' wfz' wfs' nfM.hk)
                (.symm (eqrel.typeToEq (escapeEq pσFn'_ne hσFn'_eq_σ'Fm'_ne))))
              (eqrel.natrecCong hFF'_syn hzz'_syn hss'_syn nf.keqm))
          have hRed1 := natrecSubstStar wfF wfz wfs d.reduction pσNat hσn' hPropF
          have hRed2 := natrecSubstStar wfF' wfz' wfs' d'.reduction pσ'Nat hσ'm' hPropF'
          have eq₁ := (redSubstStarTerm hRed1 pσFn (convTerm₂ pσFn pσFn'_ne hFn_eq_Fn' natrecN)).2
          have eq₂ := (redSubstStarTerm hRed2 pσ'F'm (convTerm₂ pσ'F'm pσ'F'm'_ne hF'm_eq_F'm' natrecM)).2
          exact transEqTerm pσFn eq₁
            (transEqTerm pσFn natrecN_eq_M
              (convEqTerm₂ pσFn pσ'F'm hσFn_eq_σ'F'm (symEqTerm pσ'F'm eq₂))))
    (fun {_ _} _ ih {n' m'} hk hk' hn' hm' ↦ by
      injection hk with h₁
      injection hk' with h₂
      subst h₁ h₂
      exact ih hn' hm')
    (fun {n' m'} hk ↦ by cases hk)
    (fun {_ _} nf {n' m'} hk ↦ by subst hk; cases nf.neK)
    n m hnm_nat hn_nat hm_nat

/-- Validity of natural recursion (`natrecᵛ`). -/
theorem natrecValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context}
    {F z s n : Term}
    (hNat : ValidType eqrel l Γ .nat)
    (hF : ValidType eqrel l (.nat :: Γ) F)
    (hF0 : ValidType eqrel l Γ (subst0 F .zero))
    (hFStep : ValidType eqrel l Γ (recStepType F))
    (hFn : ValidType eqrel l Γ (subst0 F n))
    (hz : ValidTerm hF0 z)
    (hs : ValidTerm hFStep s)
    (hn : ValidTerm hNat n) :
    ValidTerm hFn (.natrec F z s n) := by
  intro Δ σ hΔ hσ
  have hσn' : RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) (subst σ n) :=
    irrelevanceTerm (hNat hΔ hσ).red (redNat hΔ) (hn hΔ hσ).term
  have eqPrf : subst0 (subst (liftSubst σ) F) (subst σ n) = subst σ (subst0 F n) :=
    (singleSubstLift F n).symm
  have pFn_raw := irrelevance' (singleSubstComp (subst σ n) σ F).symm
    (hF hΔ (consSubstS hΔ hσ (natValid (l := l)) hσn')).red
  refine ⟨irrelevanceTerm' eqPrf pFn_raw (hFn hΔ hσ).red
      (natrecTerm hF hF0 hFStep hz hs hΔ hσ hσn'),
    fun {σ'} hσ' hσσ' ↦ ?_⟩
  have hσ'n' : RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) (subst σ' n) :=
    irrelevanceTerm (hNat hΔ hσ').red (redNat hΔ) (hn hΔ hσ').term
  have hσn_eq_σ'n : RedTermEq (redNat (eqrel := eqrel) (l := l) hΔ) (subst σ n) (subst σ' n) :=
    irrelevanceEqTerm (hNat hΔ hσ).red (redNat hΔ) ((hn hΔ hσ).eq hσ' hσσ')
  exact irrelevanceEqTerm' eqPrf pFn_raw (hFn hΔ hσ).red
    (natrecCongTerm hF hF (reflValid hF)
      hF0 hF0 (reflValid hF0)
      hFStep hFStep (reflValid hFStep)
      hz hz (reflValidTerm hF0 hz)
      hs hs (reflValidTerm hFStep hs)
      hΔ hσ hσ' hσσ' hσn' hσ'n' hσn_eq_σ'n)

/-- Validity of natural recursion congruence (`natrec-congᵛ`). -/
theorem natrecCongValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context}
    {F F' z z' s s' n n' : Term}
    (hNat : ValidType eqrel l Γ .nat)
    (hF : ValidType eqrel l (.nat :: Γ) F)
    (hF' : ValidType eqrel l (.nat :: Γ) F')
    (hFF' : ValidTypeEq hF F')
    (hF0 : ValidType eqrel l Γ (subst0 F .zero))
    (hF'0 : ValidType eqrel l Γ (subst0 F' .zero))
    (hF0F'0 : ValidTypeEq hF0 (subst0 F' .zero))
    (hFStep : ValidType eqrel l Γ (recStepType F))
    (hF'Step : ValidType eqrel l Γ (recStepType F'))
    (hFStepEq : ValidTypeEq hFStep (recStepType F'))
    (hFn : ValidType eqrel l Γ (subst0 F n))
    (hz : ValidTerm hF0 z)
    (hz' : ValidTerm hF'0 z')
    (hzz' : ValidTermEq hF0 z z')
    (hs : ValidTerm hFStep s)
    (hs' : ValidTerm hF'Step s')
    (hss' : ValidTermEq hFStep s s')
    (hn : ValidTerm hNat n)
    (hn' : ValidTerm hNat n')
    (hnn' : ValidTermEq hNat n n') :
    ValidTermEq hFn (.natrec F z s n) (.natrec F' z' s' n') := by
  intro Δ σ hΔ hσ
  have hσn' : RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) (subst σ n) :=
    irrelevanceTerm (hNat hΔ hσ).red (redNat hΔ) (hn hΔ hσ).term
  have hσn'' : RedTerm (redNat (eqrel := eqrel) (l := l) hΔ) (subst σ n') :=
    irrelevanceTerm (hNat hΔ hσ).red (redNat hΔ) (hn' hΔ hσ).term
  have hσn_eq_σn' : RedTermEq (redNat (eqrel := eqrel) (l := l) hΔ) (subst σ n) (subst σ n') :=
    irrelevanceEqTerm (hNat hΔ hσ).red (redNat hΔ) (hnn' hΔ hσ)
  have pFn_raw := irrelevance' (singleSubstComp (subst σ n) σ F).symm
    (hF hΔ (consSubstS hΔ hσ (natValid (l := l)) hσn')).red
  exact irrelevanceEqTerm' (singleSubstLift F n).symm pFn_raw (hFn hΔ hσ).red
    (natrecCongTerm hF hF' hFF'
      hF0 hF'0 hF0F'0
      hFStep hF'Step hFStepEq
      hz hz' hzz'
      hs hs' hss'
      hΔ hσ hσ (reflSubst hσ)
      hσn' hσn'' hσn_eq_σn')
/-!
## Fundamental Theorem (`Definition/LogicalRelation/Fundamental.agda`, Theorem 3.21 & Theorem 3.23)
-/

/-- Fundamental theorem for variables (`fundamentalVar`). -/
theorem fundamentalVar {eqrel : EqRelSet} {Γ : Context} {A : Term} {x : Nat}
    (hMem : Member x A Γ) (hΓ : ValidCtx eqrel Γ) :
    ∃ (hA : ValidType eqrel .one Γ A), ValidTerm hA (.var x) := by
  induction hMem with
  | @here Γ A₀ =>
      cases hΓ with
      | @cons _ _ l hΓ₀ hA₀ =>
          have hA : ValidType eqrel .one (A₀ :: Γ) (wk1 A₀) :=
            maybeEmbValid (wk1Valid (F := A₀) hA₀)
          refine ⟨hA, fun {Δ σ} hΔ hσ ↦ ?_⟩
          have pA₀ : RedType eqrel l Δ (subst (tailSubst σ) A₀) := (hA₀ hΔ hσ.tail).red
          have pA' : RedType eqrel .one Δ (subst σ (wk1 A₀)) := (hA hΔ hσ).red
          refine ⟨irrelevanceTerm' (subst_wk A₀).symm pA₀ pA' (hσ.head hA₀ hΔ),
            fun {σ'} hσ' hσσ' ↦
              irrelevanceEqTerm' (subst_wk A₀).symm pA₀ pA' (hσσ'.head hA₀ hΔ hσ)⟩
  | @there Γ A₀ B x hMem ih =>
      cases hΓ with
      | cons hΓ₀ _ =>
          rcases ih hΓ₀ with ⟨hA₀, hVar₀⟩
          have hA : ValidType eqrel .one (B :: Γ) (wk1 A₀) := wk1Valid (F := B) hA₀
          refine ⟨hA, fun {Δ σ} hΔ hσ ↦ ?_⟩
          have pA₀ : RedType eqrel .one Δ (subst (tailSubst σ) A₀) := (hA₀ hΔ hσ.tail).red
          have pA' : RedType eqrel .one Δ (subst σ (wk1 A₀)) := (hA hΔ hσ).red
          refine ⟨irrelevanceTerm' (subst_wk A₀).symm pA₀ pA' (hVar₀ hΔ hσ.tail).term,
            fun {σ'} hσ' hσσ' ↦
              irrelevanceEqTerm' (subst_wk A₀).symm pA₀ pA'
                ((hVar₀ hΔ hσ.tail).eq hσ'.tail hσσ'.tail)⟩

abbrev FundCtxMotive (eqrel : EqRelSet) (Γ : Context) : Prop :=
  ValidCtx eqrel Γ

abbrev FundTypeMotive (eqrel : EqRelSet) (Γ : Context) (A : Term) : Prop :=
  ValidCtx eqrel Γ ∧ ValidType eqrel .one Γ A

abbrev FundTermMotive (eqrel : EqRelSet) (Γ : Context) (t A : Term) : Prop :=
  ValidCtx eqrel Γ ∧ ∃ (hA : ValidType eqrel .one Γ A), ValidTerm hA t

abbrev FundTypeEqMotive (eqrel : EqRelSet) (Γ : Context) (A B : Term) : Prop :=
  ValidCtx eqrel Γ ∧
  ∃ (hA : ValidType eqrel .one Γ A), ValidType eqrel .one Γ B ∧ ValidTypeEq hA B

abbrev FundTermEqMotive (eqrel : EqRelSet) (Γ : Context) (t u A : Term) : Prop :=
  ValidCtx eqrel Γ ∧ ModelsTermEq eqrel .one Γ t u A

theorem fund_type_fromUniv {eqrel : EqRelSet} {Γ : Context} {A : Term}
    (ihA : FundTermMotive eqrel Γ A .univ) :
    FundTypeMotive eqrel Γ A := by
  rcases ihA with ⟨hΓ, hU, hAt⟩
  exact ⟨hΓ, univValid (l' := .one) hU hAt⟩

theorem fund_term_pi {eqrel : EqRelSet} {Γ : Context} {F G : Term}
    (ihF : FundTermMotive eqrel Γ F .univ)
    (ihG : FundTermMotive eqrel (F :: Γ) G .univ) :
    FundTermMotive eqrel Γ (.pi F G) .univ := by
  rcases ihF with ⟨hΓ, hU, hFt⟩
  rcases ihG with ⟨_, hU₁, hGt⟩
  have hF : ValidType eqrel .one Γ F := univValid (l' := .one) hU hFt
  have hU₀ : ValidType eqrel .one Γ .univ := UValid
  have hU' : ValidType eqrel .one (F :: Γ) .univ := UValid
  have hFt' : ValidTerm hU₀ F := irrelevanceValidTerm hU hU₀ hFt
  have hGt' : ValidTerm hU' G := irrelevanceValidTerm hU₁ hU' hGt
  exact ⟨hΓ, hU, irrelevanceValidTerm hU₀ hU (piTermValid hF hU' hFt' hGt')⟩

theorem fund_term_lam {eqrel : EqRelSet} {Γ : Context} {F G t : Term}
    (ihF : FundTypeMotive eqrel Γ F)
    (iht : FundTermMotive eqrel (F :: Γ) t G) :
    FundTermMotive eqrel Γ (.lam t) (.pi F G) := by
  rcases ihF with ⟨hΓ, hF⟩
  rcases iht with ⟨_, hG, ht⟩
  exact ⟨hΓ, piValid hF hG, lamValid hF hG ht⟩

theorem fund_term_app {eqrel : EqRelSet} {Γ : Context} {g a F G : Term}
    (ihg : FundTermMotive eqrel Γ g (.pi F G))
    (iha : FundTermMotive eqrel Γ a F) :
    FundTermMotive eqrel Γ (.app g a) (subst0 G a) := by
  rcases ihg with ⟨_, hPiFG, hg⟩
  rcases iha with ⟨hΓ₁, hF, ha⟩
  exact ⟨hΓ₁, substSPi hF hPiFG ha, appValid hF hPiFG hg ha⟩

theorem fund_term_suc {eqrel : EqRelSet} {Γ : Context} {n : Term}
    (ihn : FundTermMotive eqrel Γ n .nat) :
    FundTermMotive eqrel Γ (.succ n) .nat := by
  rcases ihn with ⟨hΓ, hNat, hn⟩
  exact ⟨hΓ, hNat, sucValid hNat hn⟩

theorem fund_term_natrec {eqrel : EqRelSet} {Γ : Context} {G z s n : Term}
    (ihG : FundTypeMotive eqrel (.nat :: Γ) G)
    (ihz : FundTermMotive eqrel Γ z (subst0 G .zero))
    (ihs : FundTermMotive eqrel Γ s (recStepType G))
    (ihn : FundTermMotive eqrel Γ n .nat) :
    FundTermMotive eqrel Γ (.natrec G z s n) (subst0 G n) := by
  rcases ihG with ⟨_, hG⟩
  rcases ihz with ⟨_, hG0, hz⟩
  rcases ihs with ⟨_, hGStep, hs⟩
  rcases ihn with ⟨hΓ₃, hNat, hn⟩
  have hGn : ValidType eqrel .one Γ (subst0 G n) := substS hNat hG hn
  exact ⟨hΓ₃, hGn, natrecValid hNat hG hG0 hGStep hGn hz hs hn⟩

theorem fund_term_conv {eqrel : EqRelSet} {Γ : Context} {t A A' : Term}
    (iht : FundTermMotive eqrel Γ t A')
    (ihEq : FundTypeEqMotive eqrel Γ A' A) :
    FundTermMotive eqrel Γ t A := by
  rcases iht with ⟨_, hA', ht⟩
  rcases ihEq with ⟨hΓ₁, hA'₁, hA, hA'A⟩
  have ht' : ValidTerm hA'₁ t := irrelevanceValidTerm hA' hA'₁ ht
  exact ⟨hΓ₁, hA, convValid hA'₁ hA hA'A ht'⟩

theorem fund_term_sigma {eqrel : EqRelSet} {Γ : Context} {F G : Term}
    (ihF : FundTermMotive eqrel Γ F .univ)
    (ihG : FundTermMotive eqrel (F :: Γ) G .univ) :
    FundTermMotive eqrel Γ (.sigma F G) .univ := by
  rcases ihF with ⟨hΓ, hU, hFt⟩
  rcases ihG with ⟨_, hU₁, hGt⟩
  have hF : ValidType eqrel .one Γ F := univValid (l' := .one) hU hFt
  have hU₀ : ValidType eqrel .one Γ .univ := UValid
  have hU' : ValidType eqrel .one (F :: Γ) .univ := UValid
  have hFt' : ValidTerm hU₀ F := irrelevanceValidTerm hU hU₀ hFt
  have hGt' : ValidTerm hU' G := irrelevanceValidTerm hU₁ hU' hGt
  exact ⟨hΓ, hU, irrelevanceValidTerm hU₀ hU (sigmaTermValid hF hU' hFt' hGt')⟩

theorem fund_term_prod {eqrel : EqRelSet} {Γ : Context} {F G t u : Term}
    (ihF : FundTypeMotive eqrel Γ F)
    (ihG : FundTypeMotive eqrel (F :: Γ) G)
    (iht : FundTermMotive eqrel Γ t F)
    (ihu : FundTermMotive eqrel Γ u (subst0 G t)) :
    FundTermMotive eqrel Γ (.prod t u) (.sigma F G) := by
  rcases ihF with ⟨hΓ, hF⟩
  rcases ihG with ⟨_, hG⟩
  rcases iht with ⟨_, hF₁, ht₁⟩
  rcases ihu with ⟨_, hGt₁, hu₁⟩
  have ht : ValidTerm hF t := irrelevanceValidTerm hF₁ hF ht₁
  have hGt : ValidType eqrel .one Γ (subst0 G t) := substS hF hG ht
  have hu : ValidTerm hGt u := irrelevanceValidTerm hGt₁ hGt hu₁
  exact ⟨hΓ, sigmaValid hF hG, prodValid hF hG ht hu⟩

theorem fund_term_fst {eqrel : EqRelSet} {Γ : Context} {F G t : Term}
    (ihF : FundTypeMotive eqrel Γ F)
    (ihG : FundTypeMotive eqrel (F :: Γ) G)
    (iht : FundTermMotive eqrel Γ t (.sigma F G)) :
    FundTermMotive eqrel Γ (.fst t) F := by
  rcases ihF with ⟨hΓ, hF⟩
  rcases ihG with ⟨_, hG⟩
  rcases iht with ⟨_, hSigma₁, ht₁⟩
  have hSigma : ValidType eqrel .one Γ (.sigma F G) := sigmaValid hF hG
  have ht : ValidTerm hSigma t := irrelevanceValidTerm hSigma₁ hSigma ht₁
  exact ⟨hΓ, hF, fstValid hF hG ht⟩

theorem fund_term_snd {eqrel : EqRelSet} {Γ : Context} {F G t : Term}
    (ihF : FundTypeMotive eqrel Γ F)
    (ihG : FundTypeMotive eqrel (F :: Γ) G)
    (iht : FundTermMotive eqrel Γ t (.sigma F G)) :
    FundTermMotive eqrel Γ (.snd t) (subst0 G (.fst t)) := by
  rcases ihF with ⟨hΓ, hF⟩
  rcases ihG with ⟨_, hG⟩
  rcases iht with ⟨_, hSigma₁, ht₁⟩
  have hSigma : ValidType eqrel .one Γ (.sigma F G) := sigmaValid hF hG
  have ht : ValidTerm hSigma t := irrelevanceValidTerm hSigma₁ hSigma ht₁
  have hFst : ValidTerm hF (.fst t) := fstValid hF hG ht
  exact ⟨hΓ, substS hF hG hFst, sndValid hF hG ht⟩

theorem fund_term_emptyrec {eqrel : EqRelSet} {Γ : Context} {A e : Term}
    (ihA : FundTypeMotive eqrel Γ A)
    (ihe : FundTermMotive eqrel Γ e .empty) :
    FundTermMotive eqrel Γ (.emptyrec A e) A := by
  rcases ihA with ⟨hΓ, hA⟩
  rcases ihe with ⟨_, hEmpty, he⟩
  exact ⟨hΓ, hA, emptyrecValid hEmpty hA he⟩

theorem fund_typeEq_fromUniv {eqrel : EqRelSet} {Γ : Context} {A B : Term}
    (ihEq : FundTermEqMotive eqrel Γ A B .univ) :
    FundTypeEqMotive eqrel Γ A B := by
  rcases ihEq with ⟨hΓ, hU, hAt, hBt, hABt⟩
  have hA : ValidType eqrel .one Γ A := univValid (l' := .one) hU hAt
  have hB : ValidType eqrel .one Γ B := univValid (l' := .one) hU hBt
  exact ⟨hΓ, hA, hB, fun {Δ σ} hΔ hσ ↦ univEqEq (hU hΔ hσ).red (hA hΔ hσ).red (hABt hΔ hσ)⟩

theorem fund_typeEq_refl {eqrel : EqRelSet} {Γ : Context} {A : Term}
    (ihA : FundTypeMotive eqrel Γ A) :
    FundTypeEqMotive eqrel Γ A A :=
  ⟨ihA.1, ihA.2, ihA.2, fun {_ _} hΔ hσ ↦ reflEq (ihA.2 hΔ hσ).red⟩

theorem fund_typeEq_symm {eqrel : EqRelSet} {Γ : Context} {A B : Term}
    (ihEq : FundTypeEqMotive eqrel Γ B A) :
    FundTypeEqMotive eqrel Γ A B := by
  rcases ihEq with ⟨hΓ, hB, hA, hBA⟩
  exact ⟨hΓ, hA, hB, fun {Δ σ} hΔ hσ ↦ symEq (hB hΔ hσ).red (hA hΔ hσ).red (hBA hΔ hσ)⟩

theorem fund_typeEq_trans {eqrel : EqRelSet} {Γ : Context} {A B₁ B : Term}
    (ih₁ : FundTypeEqMotive eqrel Γ A B₁)
    (ih₂ : FundTypeEqMotive eqrel Γ B₁ B) :
    FundTypeEqMotive eqrel Γ A B := by
  rcases ih₁ with ⟨hΓ, hA, hB₁, hAB₁⟩
  rcases ih₂ with ⟨_, hB₁', hB, hB₁B⟩
  exact ⟨hΓ, hA, hB, fun {Δ σ} hΔ hσ ↦
    transEq (hA hΔ hσ).red (hB₁ hΔ hσ).red (hB hΔ hσ).red
      (hAB₁ hΔ hσ)
      (irrelevanceEq (hB₁' hΔ hσ).red (hB₁ hΔ hσ).red (hB₁B hΔ hσ))⟩

theorem fund_typeEq_pi {eqrel : EqRelSet} {Γ : Context} {F H G E : Term}
    (ihFH : FundTypeEqMotive eqrel Γ F H)
    (ihGE : FundTypeEqMotive eqrel (F :: Γ) G E) :
    FundTypeEqMotive eqrel Γ (.pi F G) (.pi H E) := by
  rcases ihFH with ⟨hΓ, hF, hH, hFH⟩
  rcases ihGE with ⟨_, hG, hE, hGE⟩
  have hE' : ValidType eqrel .one (H :: Γ) E := irrelevanceLift hF hH hFH hE
  exact ⟨hΓ, piValid hF hG, piValid hH hE', piCongValid hF hG hH hE' hFH hGE⟩

theorem fund_typeEq_sigma {eqrel : EqRelSet} {Γ : Context} {F H G E : Term}
    (ihFH : FundTypeEqMotive eqrel Γ F H)
    (ihGE : FundTypeEqMotive eqrel (F :: Γ) G E) :
    FundTypeEqMotive eqrel Γ (.sigma F G) (.sigma H E) := by
  rcases ihFH with ⟨hΓ, hF, hH, hFH⟩
  rcases ihGE with ⟨_, hG, hE, hGE⟩
  have hE' : ValidType eqrel .one (H :: Γ) E := irrelevanceLift hF hH hFH hE
  exact ⟨hΓ, sigmaValid hF hG, sigmaValid hH hE', sigmaCongValid hF hG hH hE' hFH hGE⟩

theorem fund_termEq_refl {eqrel : EqRelSet} {Γ : Context} {t A : Term}
    (iht : FundTermMotive eqrel Γ t A) :
    FundTermEqMotive eqrel Γ t t A := by
  rcases iht with ⟨hΓ, hA, ht⟩
  exact ⟨hΓ, hA, ht, ht, fun {Δ σ} hΔ hσ ↦ reflEqTerm (hA hΔ hσ).red (ht hΔ hσ).term⟩

theorem fund_termEq_symm {eqrel : EqRelSet} {Γ : Context} {t t' A : Term}
    (ihEq : FundTermEqMotive eqrel Γ t' t A) :
    FundTermEqMotive eqrel Γ t t' A := by
  rcases ihEq with ⟨hΓ, hA, ht', ht, ht't⟩
  exact ⟨hΓ, hA, ht, ht', fun {Δ σ} hΔ hσ ↦ symEqTerm (hA hΔ hσ).red (ht't hΔ hσ)⟩

theorem fund_termEq_trans {eqrel : EqRelSet} {Γ : Context} {t u r A : Term}
    (ih₁ : FundTermEqMotive eqrel Γ t u A)
    (ih₂ : FundTermEqMotive eqrel Γ u r A) :
    FundTermEqMotive eqrel Γ t r A := by
  rcases ih₁ with ⟨hΓ, hA, ht, _, htu⟩
  rcases ih₂ with ⟨_, hA₁, _, hr, hur⟩
  have hr' : ValidTerm hA r := irrelevanceValidTerm hA₁ hA hr
  exact ⟨hΓ, hA, ht, hr', fun {Δ σ} hΔ hσ ↦
    transEqTerm (hA hΔ hσ).red (htu hΔ hσ)
      (irrelevanceEqTerm (hA₁ hΔ hσ).red (hA hΔ hσ).red (hur hΔ hσ))⟩

theorem fund_termEq_conv {eqrel : EqRelSet} {Γ : Context} {t u A' A : Term}
    (ihEq : FundTermEqMotive eqrel Γ t u A')
    (ihAB : FundTypeEqMotive eqrel Γ A' A) :
    FundTermEqMotive eqrel Γ t u A := by
  rcases ihEq with ⟨_, hA', ht, hu, htu⟩
  rcases ihAB with ⟨hΓ₁, hA'₁, hA, hA'A⟩
  have ht' : ValidTerm hA t := convValid hA'₁ hA hA'A (irrelevanceValidTerm hA' hA'₁ ht)
  have hu' : ValidTerm hA u := convValid hA'₁ hA hA'A (irrelevanceValidTerm hA' hA'₁ hu)
  exact ⟨hΓ₁, hA, ht', hu', fun {Δ σ} hΔ hσ ↦
    convEqTerm₁ (hA'₁ hΔ hσ).red (hA hΔ hσ).red (hA'A hΔ hσ)
      (irrelevanceEqTerm (hA' hΔ hσ).red (hA'₁ hΔ hσ).red (htu hΔ hσ))⟩

theorem fund_termEq_pi {eqrel : EqRelSet} {Γ : Context} {E F G H : Term}
    (ihF : FundTypeMotive eqrel Γ F)
    (ihFH : FundTermEqMotive eqrel Γ F H .univ)
    (ihGE : FundTermEqMotive eqrel (F :: Γ) G E .univ) :
    FundTermEqMotive eqrel Γ (.pi F G) (.pi H E) .univ := by
  rcases ihF with ⟨hΓ, hF⟩
  rcases ihFH with ⟨_, hU₀, hFt, hHt, hFHt⟩
  rcases ihGE with ⟨_, hU₁, hGt, hEt, hGEt⟩
  have hU' : ValidType eqrel .one Γ .univ := UValid
  have hFt' : ValidTerm hU' F := irrelevanceValidTerm hU₀ hU' hFt
  have hHt' : ValidTerm hU' H := irrelevanceValidTerm hU₀ hU' hHt
  have hH : ValidType eqrel .one Γ H := univValid hU' hHt'
  have hFH : ValidTypeEq hF H := univEqValid hU₀ hF hFHt
  have hU₁' : ValidType eqrel .one (F :: Γ) .univ := UValid
  have hU₂' : ValidType eqrel .one (H :: Γ) .univ := UValid
  have hGt' : ValidTerm hU₁' G := irrelevanceValidTerm hU₁ hU₁' hGt
  have hEt_F : ValidTerm hU₁' E := irrelevanceValidTerm hU₁ hU₁' hEt
  have hEt' : ValidTerm hU₂' E :=
    irrelevanceValidTerm (irrelevanceLift hF hH hFH hU₁') hU₂'
      (irrelevanceTermLift hF hH hFH hU₁' hEt_F)
  have hFHt' : ValidTermEq hU' F H := irrelevanceValidEqTerm hU₀ hU' hFHt
  have hGEt' : ValidTermEq hU₁' G E := irrelevanceValidEqTerm hU₁ hU₁' hGEt
  exact ⟨hΓ, hU',
    piTermValid hF hU₁' hFt' hGt',
    piTermValid hH hU₂' hHt' hEt',
    piCongTermValid hF hH hU₁' hU₂' hFt' hGt' hHt' hEt' hFHt' hGEt'⟩

theorem fund_termEq_app {eqrel : EqRelSet} {Γ : Context} {f g a b F G : Term}
    (ihfg : FundTermEqMotive eqrel Γ f g (.pi F G))
    (ihab : FundTermEqMotive eqrel Γ a b F) :
    FundTermEqMotive eqrel Γ (.app f a) (.app g b) (subst0 G a) := by
  rcases ihfg with ⟨_, hPiFG, hf, hg, hfg⟩
  rcases ihab with ⟨hΓ₁, hF, ha, hb, hab⟩
  have hGa : ValidType eqrel .one Γ (subst0 G a) := substSPi hF hPiFG ha
  have hGb : ValidType eqrel .one Γ (subst0 G b) := substSPi hF hPiFG hb
  have hGaGb : ValidTypeEq hGa (subst0 G b) :=
    substSPiEq hF hF hPiFG hPiFG (reflValid hPiFG) ha hb hab
  exact ⟨hΓ₁, hGa,
    appValid hF hPiFG hf ha,
    conv2Valid hGa hGb hGaGb (appValid hF hPiFG hg hb),
    appCongValid hF hPiFG hfg ha hb hab⟩

theorem fund_termEq_beta {eqrel : EqRelSet} {Γ : Context} {a b F G : Term}
    (ihb : FundTermMotive eqrel (F :: Γ) b G)
    (iha : FundTermMotive eqrel Γ a F) :
    FundTermEqMotive eqrel Γ (.app (.lam b) a) (subst0 b a) (subst0 G a) := by
  rcases ihb with ⟨_, hG, hb⟩
  rcases iha with ⟨hΓ, hF₁, ha⟩
  have hGa : ValidType eqrel .one Γ (subst0 G a) := substS hF₁ hG ha
  have hba : ValidTerm hGa (subst0 b a) := substSTerm hF₁ hG hb ha
  have hRed : ValidRedTerm eqrel Γ (.app (.lam b) a) (subst0 b a) (subst0 G a) := by
    intro Δ σ hΔ hσ
    have hLiftσ := liftSubstS hΔ hF₁ hσ
    have wfσF : TypeWf Δ (subst σ F) := escape (hF₁ hΔ hσ).red
    have wfσb : HasType (subst σ F :: Δ) (subst (liftSubst σ) b) (subst (liftSubst σ) G) :=
      escapeTerm (hG (.cons hΔ wfσF) hLiftσ).red (hb (.cons hΔ wfσF) hLiftσ).term
    have wfσa : HasType Δ (subst σ a) (subst σ F) :=
      escapeTerm (hF₁ hΔ hσ).red (ha hΔ hσ).term
    have hBeta := Step.beta wfσF wfσb wfσa
    rwa [← singleSubstLift b a, ← singleSubstLift G a] at hBeta
  rcases redSubstTermValid hRed hGa hba with ⟨hLam, hEq⟩
  exact ⟨hΓ, hGa, hLam, hba, hEq⟩

theorem fund_termEq_eta {eqrel : EqRelSet} {Γ : Context} {f g F G : Term}
    (ihF : FundTypeMotive eqrel Γ F)
    (ihf : FundTermMotive eqrel Γ f (.pi F G))
    (ihg : FundTermMotive eqrel Γ g (.pi F G))
    (ihfg : FundTermEqMotive eqrel (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G) :
    FundTermEqMotive eqrel Γ f g (.pi F G) := by
  rcases ihF with ⟨_, hF⟩
  rcases ihf with ⟨hΓ₁, hPiFG, hf⟩
  rcases ihg with ⟨_, hPiFG₁, hg⟩
  rcases ihfg with ⟨_, hG, _, _, hf0g0⟩
  have hg' : ValidTerm hPiFG g := irrelevanceValidTerm hPiFG₁ hPiFG hg
  have hPiFG'' : ValidType eqrel .one Γ (.pi F G) := piValid hF hG
  have hf'' : ValidTerm hPiFG'' f := irrelevanceValidTerm hPiFG hPiFG'' hf
  have hg'' : ValidTerm hPiFG'' g := irrelevanceValidTerm hPiFG₁ hPiFG'' hg
  have hfg : ValidTermEq hPiFG'' f g := etaEqValid hF hG hf'' hg'' hf0g0
  have hfg' : ValidTermEq hPiFG f g := irrelevanceValidEqTerm hPiFG'' hPiFG hfg
  exact ⟨hΓ₁, hPiFG, hf, hg', hfg'⟩

theorem fund_termEq_suc {eqrel : EqRelSet} {Γ : Context} {m n : Term}
    (ihmn : FundTermEqMotive eqrel Γ m n .nat) :
    FundTermEqMotive eqrel Γ (.succ m) (.succ n) .nat := by
  rcases ihmn with ⟨hΓ, hA, hm, hn, hmn⟩
  exact ⟨hΓ, hA, sucValid hA hm, sucValid hA hn,
    fun {Δ σ} hΔ hσ ↦ sucEqTerm (hA hΔ hσ).red (hmn hΔ hσ)⟩

theorem fund_termEq_natrec {eqrel : EqRelSet} {Γ : Context}
    {z z' s s' n n' F F' : Term}
    (ihFF' : FundTypeEqMotive eqrel (.nat :: Γ) F F')
    (ihzz' : FundTermEqMotive eqrel Γ z z' (subst0 F .zero))
    (ihss' : FundTermEqMotive eqrel Γ s s' (recStepType F))
    (ihnn' : FundTermEqMotive eqrel Γ n n' .nat) :
    FundTermEqMotive eqrel Γ (.natrec F z s n) (.natrec F' z' s' n') (subst0 F n) := by
  rcases ihFF' with ⟨_, hF, hF', hFF'⟩
  rcases ihzz' with ⟨_, hF0, hz, hz', hzz'⟩
  rcases ihss' with ⟨_, hFStep, hs, hs', hss'⟩
  rcases ihnn' with ⟨hΓ₃, hNat, hn, hn', hnn'⟩
  have h0 : ValidTerm hNat .zero :=
    irrelevanceValidTerm (natValid (l := .one)) hNat (zeroValid (l := .one))
  have hFn : ValidType eqrel .one Γ (subst0 F n) := substS hNat hF hn
  have hF0'' : ValidType eqrel .one Γ (subst0 F .zero) := substS hNat hF h0
  have hF'0 : ValidType eqrel .one Γ (subst0 F' .zero) := substS hNat hF' h0
  have hF'Step : ValidType eqrel .one Γ (recStepType F') := sucCase hNat hF'
  have hF'n' : ValidType eqrel .one Γ (subst0 F' n') := substS hNat hF' hn'
  have hNatRefl : ValidTypeEq hNat .nat := reflValid hNat
  have h0Refl : ValidTermEq hNat .zero .zero := reflValidTerm hNat h0
  have hF0F'0_raw : ValidTypeEq hF0'' (subst0 F' .zero) :=
    substSEq hNat hNat hNatRefl hF hF' hFF' h0 h0 h0Refl
  have hF0F'0 : ValidTypeEq hF0 (subst0 F' .zero) :=
    irrelevanceValidEq hF0'' hF0 hF0F'0_raw
  have hFStepEq_raw : ValidTypeEq (sucCase hNat hF) (recStepType F') :=
    sucCaseCong hNat hF hF' hFF'
  have hFStepEq : ValidTypeEq hFStep (recStepType F') :=
    irrelevanceValidEq (sucCase hNat hF) hFStep hFStepEq_raw
  have hFnF'n' : ValidTypeEq hFn (subst0 F' n') :=
    substSEq hNat hNat hNatRefl hF hF' hFF' hn hn' hnn'
  have hz'_conv : ValidTerm hF'0 z' := convValid hF0 hF'0 hF0F'0 hz'
  have hs'_conv : ValidTerm hF'Step s' := convValid hFStep hF'Step hFStepEq hs'
  exact ⟨hΓ₃, hFn,
    natrecValid hNat hF hF0 hFStep hFn hz hs hn,
    conv2Valid hFn hF'n' hFnF'n'
      (natrecValid hNat hF' hF'0 hF'Step hF'n' hz'_conv hs'_conv hn'),
    natrecCongValid hNat hF hF' hFF' hF0 hF'0 hF0F'0
      hFStep hF'Step hFStepEq hFn hz hz'_conv hzz' hs hs'_conv hss' hn hn' hnn'⟩

theorem fund_termEq_natrecZero {eqrel : EqRelSet} {Γ : Context} {z s F : Term}
    (ihF : FundTypeMotive eqrel (.nat :: Γ) F)
    (ihz : FundTermMotive eqrel Γ z (subst0 F .zero))
    (ihs : FundTermMotive eqrel Γ s (recStepType F)) :
    FundTermEqMotive eqrel Γ (.natrec F z s .zero) z (subst0 F .zero) := by
  rcases ihF with ⟨_, hF⟩
  rcases ihz with ⟨hΓ₁, hF0, hz⟩
  rcases ihs with ⟨_, hFStep, hs⟩
  have hNat : ValidType eqrel .one Γ .nat := natValid (l := .one)
  have hRed : ValidRedTerm eqrel Γ (.natrec F z s .zero) z (subst0 F .zero) := by
    intro Δ σ hΔ hσ
    have wfNat : TypeWf Δ .nat := escape (hNat hΔ hσ).red
    have wfF : TypeWf (.nat :: Δ) (subst (liftSubst σ) F) :=
      escape (hF (.cons hΔ wfNat) (liftSubstS hΔ hNat hσ)).red
    have wfz : HasType Δ (subst σ z) (subst0 (subst (liftSubst σ) F) .zero) := by
      have h := escapeTerm (hF0 hΔ hσ).red (hz hΔ hσ).term
      rwa [singleSubstLift F .zero] at h
    have wfs : HasType Δ (subst σ s) (recStepType (subst (liftSubst σ) F)) := by
      have h := escapeTerm (hFStep hΔ hσ).red (hs hΔ hσ).term
      rwa [natrecSucCase σ F] at h
    have hStep := Step.natrecZero wfF wfz wfs
    rw [singleSubstLift F .zero]
    exact hStep
  rcases redSubstTermValid hRed hF0 hz with ⟨hd, hr⟩
  exact ⟨hΓ₁, hF0, hd, hz, hr⟩

theorem fund_termEq_natrecSucc {eqrel : EqRelSet} {Γ : Context} {n z s F : Term}
    (ihn : FundTermMotive eqrel Γ n .nat)
    (ihF : FundTypeMotive eqrel (.nat :: Γ) F)
    (ihz : FundTermMotive eqrel Γ z (subst0 F .zero))
    (ihs : FundTermMotive eqrel Γ s (recStepType F)) :
    FundTermEqMotive eqrel Γ (.natrec F z s (.succ n))
      (.app (.app s n) (.natrec F z s n)) (subst0 F (.succ n)) := by
  rcases ihn with ⟨_, hNat, hn⟩
  rcases ihF with ⟨_, hF⟩
  rcases ihz with ⟨_, hF0, hz⟩
  rcases ihs with ⟨hΓ₃, hFStep, hs⟩
  have hSucn : ValidTerm hNat (.succ n) := sucValid hNat hn
  have hFsucn : ValidType eqrel .one Γ (subst0 F (.succ n)) := substS hNat hF hSucn
  have hFn : ValidType eqrel .one Γ (subst0 F n) := substS hNat hF hn
  have hNatrec_n : ValidTerm hFn (.natrec F z s n) :=
    natrecValid hNat hF hF0 hFStep hFn hz hs hn
  let t := Term.app (.app s n) (.natrec F z s n)
  let q := subst (liftSubst (sgSubst n)) (wk1 (substKeep F (.succ (.var 0))))
  have hStep_n : ValidType eqrel .one Γ (.pi (subst0 F n) q) :=
    substSPi hNat hFStep hn
  have hApp1 : ValidTerm hStep_n (.app s n) := appValid hNat hFStep hs hn
  have hApp2 : ValidTerm (substSPi hFn hStep_n hNatrec_n) t :=
    appValid hFn hStep_n hApp1 hNatrec_n
  have hy : ValidTerm hFsucn t :=
    irrelevanceValidTerm' (natrecIrrelevantSubst' F z s n)
      (substSPi hFn hStep_n hNatrec_n) hFsucn hApp2
  have hRed : ValidRedTerm eqrel Γ (.natrec F z s (.succ n)) t (subst0 F (.succ n)) := by
    intro Δ σ hΔ hσ
    have wfn : HasType Δ (subst σ n) .nat :=
      escapeTerm (hNat hΔ hσ).red (hn hΔ hσ).term
    have wfNat : TypeWf Δ .nat := escape (hNat hΔ hσ).red
    have wfF : TypeWf (.nat :: Δ) (subst (liftSubst σ) F) :=
      escape (hF (.cons hΔ wfNat) (liftSubstS hΔ hNat hσ)).red
    have wfz : HasType Δ (subst σ z) (subst0 (subst (liftSubst σ) F) .zero) := by
      have h := escapeTerm (hF0 hΔ hσ).red (hz hΔ hσ).term
      rwa [singleSubstLift F .zero] at h
    have wfs : HasType Δ (subst σ s) (recStepType (subst (liftSubst σ) F)) := by
      have h := escapeTerm (hFStep hΔ hσ).red (hs hΔ hσ).term
      rwa [natrecSucCase σ F] at h
    have hStep := Step.natrecSucc wfn wfF wfz wfs
    rw [singleSubstLift F (.succ n)]
    exact hStep
  rcases redSubstTermValid hRed hFsucn hy with ⟨hd, hr⟩
  exact ⟨hΓ₃, hFsucn, hd, hy, hr⟩

theorem fund_termEq_sigma {eqrel : EqRelSet} {Γ : Context} {E F G H : Term}
    (ihF : FundTypeMotive eqrel Γ F)
    (ihFH : FundTermEqMotive eqrel Γ F H .univ)
    (ihGE : FundTermEqMotive eqrel (F :: Γ) G E .univ) :
    FundTermEqMotive eqrel Γ (.sigma F G) (.sigma H E) .univ := by
  rcases ihF with ⟨hΓ, hF⟩
  rcases ihFH with ⟨_, hU₀, hFt, hHt, hFHt⟩
  rcases ihGE with ⟨_, hU₁, hGt, hEt, hGEt⟩
  have hU' : ValidType eqrel .one Γ .univ := UValid
  have hFt' : ValidTerm hU' F := irrelevanceValidTerm hU₀ hU' hFt
  have hHt' : ValidTerm hU' H := irrelevanceValidTerm hU₀ hU' hHt
  have hH : ValidType eqrel .one Γ H := univValid hU' hHt'
  have hFH : ValidTypeEq hF H := univEqValid hU₀ hF hFHt
  have hU₁' : ValidType eqrel .one (F :: Γ) .univ := UValid
  have hU₂' : ValidType eqrel .one (H :: Γ) .univ := UValid
  have hGt' : ValidTerm hU₁' G := irrelevanceValidTerm hU₁ hU₁' hGt
  have hEt_F : ValidTerm hU₁' E := irrelevanceValidTerm hU₁ hU₁' hEt
  have hEt' : ValidTerm hU₂' E :=
    irrelevanceValidTerm (irrelevanceLift hF hH hFH hU₁') hU₂'
      (irrelevanceTermLift hF hH hFH hU₁' hEt_F)
  have hFHt' : ValidTermEq hU' F H := irrelevanceValidEqTerm hU₀ hU' hFHt
  have hGEt' : ValidTermEq hU₁' G E := irrelevanceValidEqTerm hU₁ hU₁' hGEt
  exact ⟨hΓ, hU',
    sigmaTermValid hF hU₁' hFt' hGt',
    sigmaTermValid hH hU₂' hHt' hEt',
    sigmaCongTermValid hF hH hU₁' hU₂' hFt' hGt' hHt' hEt' hFHt' hGEt'⟩

theorem fund_termEq_fst {eqrel : EqRelSet} {Γ : Context} {t t' F G : Term}
    (ihF : FundTypeMotive eqrel Γ F)
    (ihG : FundTypeMotive eqrel (F :: Γ) G)
    (ih : FundTermEqMotive eqrel Γ t t' (.sigma F G)) :
    FundTermEqMotive eqrel Γ (.fst t) (.fst t') F := by
  rcases ihF with ⟨hΓ, hF⟩
  rcases ihG with ⟨_, hG⟩
  rcases ih with ⟨_, hSigma, ht, ht', htt'⟩
  have hSigma' : ValidType eqrel .one Γ (.sigma F G) := sigmaValid hF hG
  have ht₁ : ValidTerm hSigma' t := irrelevanceValidTerm hSigma hSigma' ht
  have ht'₁ : ValidTerm hSigma' t' := irrelevanceValidTerm hSigma hSigma' ht'
  have htt'₁ : ValidTermEq hSigma' t t' := irrelevanceValidEqTerm hSigma hSigma' htt'
  exact ⟨hΓ, hF, fstValid hF hG ht₁, fstValid hF hG ht'₁, fstCongValid hF hG ht₁ ht'₁ htt'₁⟩

theorem fund_termEq_snd {eqrel : EqRelSet} {Γ : Context} {t t' F G : Term}
    (ihF : FundTypeMotive eqrel Γ F)
    (ihG : FundTypeMotive eqrel (F :: Γ) G)
    (ih : FundTermEqMotive eqrel Γ t t' (.sigma F G)) :
    FundTermEqMotive eqrel Γ (.snd t) (.snd t') (subst0 G (.fst t)) := by
  rcases ihF with ⟨hΓ, hF⟩
  rcases ihG with ⟨_, hG⟩
  rcases ih with ⟨_, hSigma, ht, ht', htt'⟩
  have hSigma' : ValidType eqrel .one Γ (.sigma F G) := sigmaValid hF hG
  have ht₁ : ValidTerm hSigma' t := irrelevanceValidTerm hSigma hSigma' ht
  have ht'₁ : ValidTerm hSigma' t' := irrelevanceValidTerm hSigma hSigma' ht'
  have htt'₁ : ValidTermEq hSigma' t t' := irrelevanceValidEqTerm hSigma hSigma' htt'
  have hFstT : ValidTerm hF (.fst t) := fstValid hF hG ht₁
  have hFstT' : ValidTerm hF (.fst t') := fstValid hF hG ht'₁
  have hFstEq : ValidTermEq hF (.fst t) (.fst t') := fstCongValid hF hG ht₁ ht'₁ htt'₁
  have hGfstT : ValidType eqrel .one Γ (subst0 G (.fst t)) := substS hF hG hFstT
  have hGfstT' : ValidType eqrel .one Γ (subst0 G (.fst t')) := substS hF hG hFstT'
  have hGfstEq : ValidTypeEq hGfstT (subst0 G (.fst t')) :=
    substSEq hF hF (reflValid hF) hG hG (reflValid hG) hFstT hFstT' hFstEq
  exact ⟨hΓ, hGfstT,
    sndValid hF hG ht₁,
    conv2Valid hGfstT hGfstT' hGfstEq (sndValid hF hG ht'₁),
    sndCongValid hF hG ht₁ ht'₁ htt'₁⟩

theorem fund_termEq_sigmaBeta1 {eqrel : EqRelSet} {Γ : Context} {F G t u : Term}
    (ihF : FundTypeMotive eqrel Γ F)
    (ihG : FundTypeMotive eqrel (F :: Γ) G)
    (iht : FundTermMotive eqrel Γ t F)
    (ihu : FundTermMotive eqrel Γ u (subst0 G t)) :
    FundTermEqMotive eqrel Γ (.fst (.prod t u)) t F := by
  rcases ihF with ⟨hΓ, hF⟩
  rcases ihG with ⟨_, hG⟩
  rcases iht with ⟨_, hF', ht⟩
  rcases ihu with ⟨_, hGt, hu⟩
  have ht' : ValidTerm hF t := irrelevanceValidTerm hF' hF ht
  have hGt' : ValidType eqrel .one Γ (subst0 G t) := substS hF hG ht'
  have hu' : ValidTerm hGt' u := irrelevanceValidTerm hGt hGt' hu
  exact ⟨hΓ, hF, fstValid hF hG (prodValid hF hG ht' hu'), ht', sigmaBeta1Valid hF hG ht' hu'⟩

theorem fund_termEq_sigmaBeta2 {eqrel : EqRelSet} {Γ : Context} {F G t u : Term}
    (ihF : FundTypeMotive eqrel Γ F)
    (ihG : FundTypeMotive eqrel (F :: Γ) G)
    (iht : FundTermMotive eqrel Γ t F)
    (ihu : FundTermMotive eqrel Γ u (subst0 G t)) :
    FundTermEqMotive eqrel Γ (.snd (.prod t u)) u (subst0 G (.fst (.prod t u))) := by
  rcases ihF with ⟨hΓ, hF⟩
  rcases ihG with ⟨_, hG⟩
  rcases iht with ⟨_, hF', ht⟩
  rcases ihu with ⟨_, hGt, hu⟩
  have ht' : ValidTerm hF t := irrelevanceValidTerm hF' hF ht
  have hGt' : ValidType eqrel .one Γ (subst0 G t) := substS hF hG ht'
  have hu' : ValidTerm hGt' u := irrelevanceValidTerm hGt hGt' hu
  have hProd : ValidTerm (sigmaValid hF hG) (.prod t u) := prodValid hF hG ht' hu'
  have hFstProd : ValidTerm hF (.fst (.prod t u)) := fstValid hF hG hProd
  have hGFstProd : ValidType eqrel .one Γ (subst0 G (.fst (.prod t u))) := substS hF hG hFstProd
  have hFstEq : ValidTermEq hF (.fst (.prod t u)) t := sigmaBeta1Valid hF hG ht' hu'
  have hGEq : ValidTypeEq hGFstProd (subst0 G t) :=
    substSEq hF hF (reflValid hF) hG hG (reflValid hG) hFstProd ht' hFstEq
  exact ⟨hΓ, hGFstProd,
    sndValid hF hG hProd,
    conv2Valid hGFstProd hGt' hGEq hu',
    sigmaBeta2Valid hF hG ht' hu'⟩

theorem fund_termEq_sigmaEta {eqrel : EqRelSet} {Γ : Context} {p r F G : Term}
    (ihF : FundTypeMotive eqrel Γ F)
    (ihG : FundTypeMotive eqrel (F :: Γ) G)
    (ihp : FundTermMotive eqrel Γ p (.sigma F G))
    (ihr : FundTermMotive eqrel Γ r (.sigma F G))
    (ihFst : FundTermEqMotive eqrel Γ (.fst p) (.fst r) F)
    (ihSnd : FundTermEqMotive eqrel Γ (.snd p) (.snd r) (subst0 G (.fst p))) :
    FundTermEqMotive eqrel Γ p r (.sigma F G) := by
  rcases ihF with ⟨hΓ, hF⟩
  rcases ihG with ⟨_, hG⟩
  rcases ihp with ⟨_, hSigma₁, hp⟩
  rcases ihr with ⟨_, hSigma₂, hr⟩
  rcases ihFst with ⟨_, hF', _, _, hFstEq⟩
  rcases ihSnd with ⟨_, hGFstP, _, _, hSndEq⟩
  have hSigma : ValidType eqrel .one Γ (.sigma F G) := sigmaValid hF hG
  have hp' : ValidTerm hSigma p := irrelevanceValidTerm hSigma₁ hSigma hp
  have hr' : ValidTerm hSigma r := irrelevanceValidTerm hSigma₂ hSigma hr
  have hFstEq' : ValidTermEq hF (.fst p) (.fst r) := irrelevanceValidEqTerm hF' hF hFstEq
  have hGFstP' : ValidType eqrel .one Γ (subst0 G (.fst p)) := substS hF hG (fstValid hF hG hp')
  have hSndEq' : ValidTermEq hGFstP' (.snd p) (.snd r) := irrelevanceValidEqTerm hGFstP hGFstP' hSndEq
  exact ⟨hΓ, hSigma, hp', hr', sigmaEtaValid hF hG hp' hr' hFstEq' hSndEq'⟩

theorem fund_termEq_emptyrec {eqrel : EqRelSet} {Γ : Context} {A A' e e' : Term}
    (ihA : FundTypeEqMotive eqrel Γ A A')
    (ihe : FundTermEqMotive eqrel Γ e e' .empty) :
    FundTermEqMotive eqrel Γ (.emptyrec A e) (.emptyrec A' e') A := by
  rcases ihA with ⟨hΓ, hA, hA', hAA'⟩
  rcases ihe with ⟨_, hEmpty, he, he', hee'⟩
  exact ⟨hΓ, hA,
    emptyrecValid hEmpty hA he,
    conv2Valid hA hA' hAA' (emptyrecValid hEmpty hA' he'),
    emptyrecCongValid hEmpty hA hA' hAA' hee'⟩

theorem fund_termEq_etaUnit {eqrel : EqRelSet} {Γ : Context} {e e' : Term}
    (ihe : FundTermMotive eqrel Γ e .unit)
    (ihe' : FundTermMotive eqrel Γ e' .unit) :
    FundTermEqMotive eqrel Γ e e' .unit := by
  rcases ihe with ⟨hΓ, hUnit₁, he⟩
  rcases ihe' with ⟨_, hUnit₂, he'⟩
  have he'₁ : ValidTerm hUnit₁ e' := irrelevanceValidTerm hUnit₂ hUnit₁ he'
  exact ⟨hΓ, hUnit₁, he, he'₁, etaUnitValid hUnit₁ he he'₁⟩

/-- Fundamental theorem for contexts (`valid`, Theorem 3.21). -/
theorem valid {eqrel : EqRelSet} {Γ : Context} (d : CtxWf Γ) : ValidCtx eqrel Γ :=
  @CtxWf.rec
    (fun Γ _ ↦ FundCtxMotive eqrel Γ)
    (fun Γ A _ ↦ FundTypeMotive eqrel Γ A)
    (fun Γ t A _ ↦ FundTermMotive eqrel Γ t A)
    (fun Γ A B _ ↦ FundTypeEqMotive eqrel Γ A B)
    (fun Γ t u A _ ↦ FundTermEqMotive eqrel Γ t u A)
    .nil
    (fun _ _ _ ihA ↦ .cons ihA.1 ihA.2)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid⟩)
    (fun _ _ ihF ihG ↦ ⟨ihF.1, piValid ihF.2 ihG.2⟩)
    (fun _ ihA ↦ fund_type_fromUniv ihA)
    (fun _ ihΓ ↦ ⟨ihΓ, emptyValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, unitValid⟩)
    (fun _ _ ihF ihG ↦ ⟨ihF.1, sigmaValid ihF.2 ihG.2⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, natTermValid⟩)
    (fun _ _ ihF ihG ↦ fund_term_pi ihF ihG)
    (fun _ hm ihΓ ↦ ⟨ihΓ, fundamentalVar hm ihΓ⟩)
    (fun _ _ ihF iht ↦ fund_term_lam ihF iht)
    (fun _ _ ihg iha ↦ fund_term_app ihg iha)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid, zeroValid⟩)
    (fun _ ihn ↦ fund_term_suc ihn)
    (fun _ _ _ _ ihG ihz ihs ihn ↦ fund_term_natrec ihG ihz ihs ihn)
    (fun _ _ iht ihEq ↦ fund_term_conv iht ihEq)
    (fun _ _ ihF ihG ↦ fund_term_sigma ihF ihG)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, emptyTermValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, unitTermValid⟩)
    (fun _ _ _ _ ihF ihG iht ihu ↦ fund_term_prod ihF ihG iht ihu)
    (fun _ _ _ ihF ihG iht ↦ fund_term_fst ihF ihG iht)
    (fun _ _ _ ihF ihG iht ↦ fund_term_snd ihF ihG iht)
    (fun _ _ ihA ihe ↦ fund_term_emptyrec ihA ihe)
    (fun _ ihΓ ↦ ⟨ihΓ, unitValid, starValid⟩)
    (fun _ ihEq ↦ fund_typeEq_fromUniv ihEq)
    (fun _ ihA ↦ fund_typeEq_refl ihA)
    (fun _ ihEq ↦ fund_typeEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_typeEq_trans ih₁ ih₂)
    (fun _ _ _ _ ihFH ihGE ↦ fund_typeEq_pi ihFH ihGE)
    (fun _ _ _ _ ihFH ihGE ↦ fund_typeEq_sigma ihFH ihGE)
    (fun _ iht ↦ fund_termEq_refl iht)
    (fun _ ihEq ↦ fund_termEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_termEq_trans ih₁ ih₂)
    (fun _ _ ihEq ihAB ↦ fund_termEq_conv ihEq ihAB)
    (fun _ _ _ ihF ihFH ihGE ↦ fund_termEq_pi ihF ihFH ihGE)
    (fun _ _ ihfg ihab ↦ fund_termEq_app ihfg ihab)
    (fun _ _ _ _ ihb iha ↦ fund_termEq_beta ihb iha)
    (fun _ _ _ _ ihF ihf ihg ihfg ↦ fund_termEq_eta ihF ihf ihg ihfg)
    (fun _ ihmn ↦ fund_termEq_suc ihmn)
    (fun _ _ _ _ ihFF' ihzz' ihss' ihnn' ↦ fund_termEq_natrec ihFF' ihzz' ihss' ihnn')
    (fun _ _ _ ihF ihz ihs ↦ fund_termEq_natrecZero ihF ihz ihs)
    (fun _ _ _ _ ihn ihF ihz ihs ↦ fund_termEq_natrecSucc ihn ihF ihz ihs)
    (fun _ _ _ ihF ihFH ihGE ↦ fund_termEq_sigma ihF ihFH ihGE)
    (fun _ _ _ ihF ihG ih ↦ fund_termEq_fst ihF ihG ih)
    (fun _ _ _ ihF ihG ih ↦ fund_termEq_snd ihF ihG ih)
    (fun _ _ _ _ ihF ihG iht ihu ↦ fund_termEq_sigmaBeta1 ihF ihG iht ihu)
    (fun _ _ _ _ ihF ihG iht ihu ↦ fund_termEq_sigmaBeta2 ihF ihG iht ihu)
    (fun _ _ _ _ _ _ ihF ihG ihp ihr ihFst ihSnd ↦ fund_termEq_sigmaEta ihF ihG ihp ihr ihFst ihSnd)
    (fun _ _ ihA ihe ↦ fund_termEq_emptyrec ihA ihe)
    (fun _ _ ihe ihe' ↦ fund_termEq_etaUnit ihe ihe')
    Γ d

/-- Fundamental theorem for types (`fundamental`, Theorem 3.21). -/
theorem fundamental {eqrel : EqRelSet} {Γ : Context} {A : Term} (d : TypeWf Γ A) :
    ValidCtx eqrel Γ ∧ ValidType eqrel .one Γ A :=
  @TypeWf.rec
    (fun Γ _ ↦ FundCtxMotive eqrel Γ)
    (fun Γ A _ ↦ FundTypeMotive eqrel Γ A)
    (fun Γ t A _ ↦ FundTermMotive eqrel Γ t A)
    (fun Γ A B _ ↦ FundTypeEqMotive eqrel Γ A B)
    (fun Γ t u A _ ↦ FundTermEqMotive eqrel Γ t u A)
    .nil
    (fun _ _ _ ihA ↦ .cons ihA.1 ihA.2)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid⟩)
    (fun _ _ ihF ihG ↦ ⟨ihF.1, piValid ihF.2 ihG.2⟩)
    (fun _ ihA ↦ fund_type_fromUniv ihA)
    (fun _ ihΓ ↦ ⟨ihΓ, emptyValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, unitValid⟩)
    (fun _ _ ihF ihG ↦ ⟨ihF.1, sigmaValid ihF.2 ihG.2⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, natTermValid⟩)
    (fun _ _ ihF ihG ↦ fund_term_pi ihF ihG)
    (fun _ hm ihΓ ↦ ⟨ihΓ, fundamentalVar hm ihΓ⟩)
    (fun _ _ ihF iht ↦ fund_term_lam ihF iht)
    (fun _ _ ihg iha ↦ fund_term_app ihg iha)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid, zeroValid⟩)
    (fun _ ihn ↦ fund_term_suc ihn)
    (fun _ _ _ _ ihG ihz ihs ihn ↦ fund_term_natrec ihG ihz ihs ihn)
    (fun _ _ iht ihEq ↦ fund_term_conv iht ihEq)
    (fun _ _ ihF ihG ↦ fund_term_sigma ihF ihG)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, emptyTermValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, unitTermValid⟩)
    (fun _ _ _ _ ihF ihG iht ihu ↦ fund_term_prod ihF ihG iht ihu)
    (fun _ _ _ ihF ihG iht ↦ fund_term_fst ihF ihG iht)
    (fun _ _ _ ihF ihG iht ↦ fund_term_snd ihF ihG iht)
    (fun _ _ ihA ihe ↦ fund_term_emptyrec ihA ihe)
    (fun _ ihΓ ↦ ⟨ihΓ, unitValid, starValid⟩)
    (fun _ ihEq ↦ fund_typeEq_fromUniv ihEq)
    (fun _ ihA ↦ fund_typeEq_refl ihA)
    (fun _ ihEq ↦ fund_typeEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_typeEq_trans ih₁ ih₂)
    (fun _ _ _ _ ihFH ihGE ↦ fund_typeEq_pi ihFH ihGE)
    (fun _ _ _ _ ihFH ihGE ↦ fund_typeEq_sigma ihFH ihGE)
    (fun _ iht ↦ fund_termEq_refl iht)
    (fun _ ihEq ↦ fund_termEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_termEq_trans ih₁ ih₂)
    (fun _ _ ihEq ihAB ↦ fund_termEq_conv ihEq ihAB)
    (fun _ _ _ ihF ihFH ihGE ↦ fund_termEq_pi ihF ihFH ihGE)
    (fun _ _ ihfg ihab ↦ fund_termEq_app ihfg ihab)
    (fun _ _ _ _ ihb iha ↦ fund_termEq_beta ihb iha)
    (fun _ _ _ _ ihF ihf ihg ihfg ↦ fund_termEq_eta ihF ihf ihg ihfg)
    (fun _ ihmn ↦ fund_termEq_suc ihmn)
    (fun _ _ _ _ ihFF' ihzz' ihss' ihnn' ↦ fund_termEq_natrec ihFF' ihzz' ihss' ihnn')
    (fun _ _ _ ihF ihz ihs ↦ fund_termEq_natrecZero ihF ihz ihs)
    (fun _ _ _ _ ihn ihF ihz ihs ↦ fund_termEq_natrecSucc ihn ihF ihz ihs)
    (fun _ _ _ ihF ihFH ihGE ↦ fund_termEq_sigma ihF ihFH ihGE)
    (fun _ _ _ ihF ihG ih ↦ fund_termEq_fst ihF ihG ih)
    (fun _ _ _ ihF ihG ih ↦ fund_termEq_snd ihF ihG ih)
    (fun _ _ _ _ ihF ihG iht ihu ↦ fund_termEq_sigmaBeta1 ihF ihG iht ihu)
    (fun _ _ _ _ ihF ihG iht ihu ↦ fund_termEq_sigmaBeta2 ihF ihG iht ihu)
    (fun _ _ _ _ _ _ ihF ihG ihp ihr ihFst ihSnd ↦ fund_termEq_sigmaEta ihF ihG ihp ihr ihFst ihSnd)
    (fun _ _ ihA ihe ↦ fund_termEq_emptyrec ihA ihe)
    (fun _ _ ihe ihe' ↦ fund_termEq_etaUnit ihe ihe')
    Γ A d

/-- Fundamental theorem for terms (`fundamentalTerm`, Theorem 3.21). -/
theorem fundamentalTerm {eqrel : EqRelSet} {Γ : Context} {t A : Term} (d : HasType Γ t A) :
    FundTermMotive eqrel Γ t A :=
  @HasType.rec
    (fun Γ _ ↦ FundCtxMotive eqrel Γ)
    (fun Γ A _ ↦ FundTypeMotive eqrel Γ A)
    (fun Γ t A _ ↦ FundTermMotive eqrel Γ t A)
    (fun Γ A B _ ↦ FundTypeEqMotive eqrel Γ A B)
    (fun Γ t u A _ ↦ FundTermEqMotive eqrel Γ t u A)
    .nil
    (fun _ _ _ ihA ↦ .cons ihA.1 ihA.2)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid⟩)
    (fun _ _ ihF ihG ↦ ⟨ihF.1, piValid ihF.2 ihG.2⟩)
    (fun _ ihA ↦ fund_type_fromUniv ihA)
    (fun _ ihΓ ↦ ⟨ihΓ, emptyValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, unitValid⟩)
    (fun _ _ ihF ihG ↦ ⟨ihF.1, sigmaValid ihF.2 ihG.2⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, natTermValid⟩)
    (fun _ _ ihF ihG ↦ fund_term_pi ihF ihG)
    (fun _ hm ihΓ ↦ ⟨ihΓ, fundamentalVar hm ihΓ⟩)
    (fun _ _ ihF iht ↦ fund_term_lam ihF iht)
    (fun _ _ ihg iha ↦ fund_term_app ihg iha)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid, zeroValid⟩)
    (fun _ ihn ↦ fund_term_suc ihn)
    (fun _ _ _ _ ihG ihz ihs ihn ↦ fund_term_natrec ihG ihz ihs ihn)
    (fun _ _ iht ihEq ↦ fund_term_conv iht ihEq)
    (fun _ _ ihF ihG ↦ fund_term_sigma ihF ihG)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, emptyTermValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, unitTermValid⟩)
    (fun _ _ _ _ ihF ihG iht ihu ↦ fund_term_prod ihF ihG iht ihu)
    (fun _ _ _ ihF ihG iht ↦ fund_term_fst ihF ihG iht)
    (fun _ _ _ ihF ihG iht ↦ fund_term_snd ihF ihG iht)
    (fun _ _ ihA ihe ↦ fund_term_emptyrec ihA ihe)
    (fun _ ihΓ ↦ ⟨ihΓ, unitValid, starValid⟩)
    (fun _ ihEq ↦ fund_typeEq_fromUniv ihEq)
    (fun _ ihA ↦ fund_typeEq_refl ihA)
    (fun _ ihEq ↦ fund_typeEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_typeEq_trans ih₁ ih₂)
    (fun _ _ _ _ ihFH ihGE ↦ fund_typeEq_pi ihFH ihGE)
    (fun _ _ _ _ ihFH ihGE ↦ fund_typeEq_sigma ihFH ihGE)
    (fun _ iht ↦ fund_termEq_refl iht)
    (fun _ ihEq ↦ fund_termEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_termEq_trans ih₁ ih₂)
    (fun _ _ ihEq ihAB ↦ fund_termEq_conv ihEq ihAB)
    (fun _ _ _ ihF ihFH ihGE ↦ fund_termEq_pi ihF ihFH ihGE)
    (fun _ _ ihfg ihab ↦ fund_termEq_app ihfg ihab)
    (fun _ _ _ _ ihb iha ↦ fund_termEq_beta ihb iha)
    (fun _ _ _ _ ihF ihf ihg ihfg ↦ fund_termEq_eta ihF ihf ihg ihfg)
    (fun _ ihmn ↦ fund_termEq_suc ihmn)
    (fun _ _ _ _ ihFF' ihzz' ihss' ihnn' ↦ fund_termEq_natrec ihFF' ihzz' ihss' ihnn')
    (fun _ _ _ ihF ihz ihs ↦ fund_termEq_natrecZero ihF ihz ihs)
    (fun _ _ _ _ ihn ihF ihz ihs ↦ fund_termEq_natrecSucc ihn ihF ihz ihs)
    (fun _ _ _ ihF ihFH ihGE ↦ fund_termEq_sigma ihF ihFH ihGE)
    (fun _ _ _ ihF ihG ih ↦ fund_termEq_fst ihF ihG ih)
    (fun _ _ _ ihF ihG ih ↦ fund_termEq_snd ihF ihG ih)
    (fun _ _ _ _ ihF ihG iht ihu ↦ fund_termEq_sigmaBeta1 ihF ihG iht ihu)
    (fun _ _ _ _ ihF ihG iht ihu ↦ fund_termEq_sigmaBeta2 ihF ihG iht ihu)
    (fun _ _ _ _ _ _ ihF ihG ihp ihr ihFst ihSnd ↦ fund_termEq_sigmaEta ihF ihG ihp ihr ihFst ihSnd)
    (fun _ _ ihA ihe ↦ fund_termEq_emptyrec ihA ihe)
    (fun _ _ ihe ihe' ↦ fund_termEq_etaUnit ihe ihe')
    Γ t A d

/-- Fundamental theorem for type equality (`fundamentalEq`, Theorem 3.21). -/
theorem fundamentalEq {eqrel : EqRelSet} {Γ : Context} {A B : Term} (d : TypeEq Γ A B) :
    FundTypeEqMotive eqrel Γ A B :=
  @TypeEq.rec
    (fun Γ _ ↦ FundCtxMotive eqrel Γ)
    (fun Γ A _ ↦ FundTypeMotive eqrel Γ A)
    (fun Γ t A _ ↦ FundTermMotive eqrel Γ t A)
    (fun Γ A B _ ↦ FundTypeEqMotive eqrel Γ A B)
    (fun Γ t u A _ ↦ FundTermEqMotive eqrel Γ t u A)
    .nil
    (fun _ _ _ ihA ↦ .cons ihA.1 ihA.2)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid⟩)
    (fun _ _ ihF ihG ↦ ⟨ihF.1, piValid ihF.2 ihG.2⟩)
    (fun _ ihA ↦ fund_type_fromUniv ihA)
    (fun _ ihΓ ↦ ⟨ihΓ, emptyValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, unitValid⟩)
    (fun _ _ ihF ihG ↦ ⟨ihF.1, sigmaValid ihF.2 ihG.2⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, natTermValid⟩)
    (fun _ _ ihF ihG ↦ fund_term_pi ihF ihG)
    (fun _ hm ihΓ ↦ ⟨ihΓ, fundamentalVar hm ihΓ⟩)
    (fun _ _ ihF iht ↦ fund_term_lam ihF iht)
    (fun _ _ ihg iha ↦ fund_term_app ihg iha)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid, zeroValid⟩)
    (fun _ ihn ↦ fund_term_suc ihn)
    (fun _ _ _ _ ihG ihz ihs ihn ↦ fund_term_natrec ihG ihz ihs ihn)
    (fun _ _ iht ihEq ↦ fund_term_conv iht ihEq)
    (fun _ _ ihF ihG ↦ fund_term_sigma ihF ihG)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, emptyTermValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, unitTermValid⟩)
    (fun _ _ _ _ ihF ihG iht ihu ↦ fund_term_prod ihF ihG iht ihu)
    (fun _ _ _ ihF ihG iht ↦ fund_term_fst ihF ihG iht)
    (fun _ _ _ ihF ihG iht ↦ fund_term_snd ihF ihG iht)
    (fun _ _ ihA ihe ↦ fund_term_emptyrec ihA ihe)
    (fun _ ihΓ ↦ ⟨ihΓ, unitValid, starValid⟩)
    (fun _ ihEq ↦ fund_typeEq_fromUniv ihEq)
    (fun _ ihA ↦ fund_typeEq_refl ihA)
    (fun _ ihEq ↦ fund_typeEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_typeEq_trans ih₁ ih₂)
    (fun _ _ _ _ ihFH ihGE ↦ fund_typeEq_pi ihFH ihGE)
    (fun _ _ _ _ ihFH ihGE ↦ fund_typeEq_sigma ihFH ihGE)
    (fun _ iht ↦ fund_termEq_refl iht)
    (fun _ ihEq ↦ fund_termEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_termEq_trans ih₁ ih₂)
    (fun _ _ ihEq ihAB ↦ fund_termEq_conv ihEq ihAB)
    (fun _ _ _ ihF ihFH ihGE ↦ fund_termEq_pi ihF ihFH ihGE)
    (fun _ _ ihfg ihab ↦ fund_termEq_app ihfg ihab)
    (fun _ _ _ _ ihb iha ↦ fund_termEq_beta ihb iha)
    (fun _ _ _ _ ihF ihf ihg ihfg ↦ fund_termEq_eta ihF ihf ihg ihfg)
    (fun _ ihmn ↦ fund_termEq_suc ihmn)
    (fun _ _ _ _ ihFF' ihzz' ihss' ihnn' ↦ fund_termEq_natrec ihFF' ihzz' ihss' ihnn')
    (fun _ _ _ ihF ihz ihs ↦ fund_termEq_natrecZero ihF ihz ihs)
    (fun _ _ _ _ ihn ihF ihz ihs ↦ fund_termEq_natrecSucc ihn ihF ihz ihs)
    (fun _ _ _ ihF ihFH ihGE ↦ fund_termEq_sigma ihF ihFH ihGE)
    (fun _ _ _ ihF ihG ih ↦ fund_termEq_fst ihF ihG ih)
    (fun _ _ _ ihF ihG ih ↦ fund_termEq_snd ihF ihG ih)
    (fun _ _ _ _ ihF ihG iht ihu ↦ fund_termEq_sigmaBeta1 ihF ihG iht ihu)
    (fun _ _ _ _ ihF ihG iht ihu ↦ fund_termEq_sigmaBeta2 ihF ihG iht ihu)
    (fun _ _ _ _ _ _ ihF ihG ihp ihr ihFst ihSnd ↦ fund_termEq_sigmaEta ihF ihG ihp ihr ihFst ihSnd)
    (fun _ _ ihA ihe ↦ fund_termEq_emptyrec ihA ihe)
    (fun _ _ ihe ihe' ↦ fund_termEq_etaUnit ihe ihe')
    Γ A B d

/-- Fundamental theorem for term equality (`fundamentalTermEq`, Theorem 3.21). -/
theorem fundamentalTermEq {eqrel : EqRelSet} {Γ : Context} {t u A : Term} (d : TermEq Γ t u A) :
    FundTermEqMotive eqrel Γ t u A :=
  @TermEq.rec
    (fun Γ _ ↦ FundCtxMotive eqrel Γ)
    (fun Γ A _ ↦ FundTypeMotive eqrel Γ A)
    (fun Γ t A _ ↦ FundTermMotive eqrel Γ t A)
    (fun Γ A B _ ↦ FundTypeEqMotive eqrel Γ A B)
    (fun Γ t u A _ ↦ FundTermEqMotive eqrel Γ t u A)
    .nil
    (fun _ _ _ ihA ↦ .cons ihA.1 ihA.2)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid⟩)
    (fun _ _ ihF ihG ↦ ⟨ihF.1, piValid ihF.2 ihG.2⟩)
    (fun _ ihA ↦ fund_type_fromUniv ihA)
    (fun _ ihΓ ↦ ⟨ihΓ, emptyValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, unitValid⟩)
    (fun _ _ ihF ihG ↦ ⟨ihF.1, sigmaValid ihF.2 ihG.2⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, natTermValid⟩)
    (fun _ _ ihF ihG ↦ fund_term_pi ihF ihG)
    (fun _ hm ihΓ ↦ ⟨ihΓ, fundamentalVar hm ihΓ⟩)
    (fun _ _ ihF iht ↦ fund_term_lam ihF iht)
    (fun _ _ ihg iha ↦ fund_term_app ihg iha)
    (fun _ ihΓ ↦ ⟨ihΓ, natValid, zeroValid⟩)
    (fun _ ihn ↦ fund_term_suc ihn)
    (fun _ _ _ _ ihG ihz ihs ihn ↦ fund_term_natrec ihG ihz ihs ihn)
    (fun _ _ iht ihEq ↦ fund_term_conv iht ihEq)
    (fun _ _ ihF ihG ↦ fund_term_sigma ihF ihG)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, emptyTermValid⟩)
    (fun _ ihΓ ↦ ⟨ihΓ, UValid, unitTermValid⟩)
    (fun _ _ _ _ ihF ihG iht ihu ↦ fund_term_prod ihF ihG iht ihu)
    (fun _ _ _ ihF ihG iht ↦ fund_term_fst ihF ihG iht)
    (fun _ _ _ ihF ihG iht ↦ fund_term_snd ihF ihG iht)
    (fun _ _ ihA ihe ↦ fund_term_emptyrec ihA ihe)
    (fun _ ihΓ ↦ ⟨ihΓ, unitValid, starValid⟩)
    (fun _ ihEq ↦ fund_typeEq_fromUniv ihEq)
    (fun _ ihA ↦ fund_typeEq_refl ihA)
    (fun _ ihEq ↦ fund_typeEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_typeEq_trans ih₁ ih₂)
    (fun _ _ _ _ ihFH ihGE ↦ fund_typeEq_pi ihFH ihGE)
    (fun _ _ _ _ ihFH ihGE ↦ fund_typeEq_sigma ihFH ihGE)
    (fun _ iht ↦ fund_termEq_refl iht)
    (fun _ ihEq ↦ fund_termEq_symm ihEq)
    (fun _ _ ih₁ ih₂ ↦ fund_termEq_trans ih₁ ih₂)
    (fun _ _ ihEq ihAB ↦ fund_termEq_conv ihEq ihAB)
    (fun _ _ _ ihF ihFH ihGE ↦ fund_termEq_pi ihF ihFH ihGE)
    (fun _ _ ihfg ihab ↦ fund_termEq_app ihfg ihab)
    (fun _ _ _ _ ihb iha ↦ fund_termEq_beta ihb iha)
    (fun _ _ _ _ ihF ihf ihg ihfg ↦ fund_termEq_eta ihF ihf ihg ihfg)
    (fun _ ihmn ↦ fund_termEq_suc ihmn)
    (fun _ _ _ _ ihFF' ihzz' ihss' ihnn' ↦ fund_termEq_natrec ihFF' ihzz' ihss' ihnn')
    (fun _ _ _ ihF ihz ihs ↦ fund_termEq_natrecZero ihF ihz ihs)
    (fun _ _ _ _ ihn ihF ihz ihs ↦ fund_termEq_natrecSucc ihn ihF ihz ihs)
    (fun _ _ _ ihF ihFH ihGE ↦ fund_termEq_sigma ihF ihFH ihGE)
    (fun _ _ _ ihF ihG ih ↦ fund_termEq_fst ihF ihG ih)
    (fun _ _ _ ihF ihG ih ↦ fund_termEq_snd ihF ihG ih)
    (fun _ _ _ _ ihF ihG iht ihu ↦ fund_termEq_sigmaBeta1 ihF ihG iht ihu)
    (fun _ _ _ _ ihF ihG iht ihu ↦ fund_termEq_sigmaBeta2 ihF ihG iht ihu)
    (fun _ _ _ _ _ _ ihF ihG ihp ihr ihFst ihSnd ↦ fund_termEq_sigmaEta ihF ihG ihp ihr ihFst ihSnd)
    (fun _ _ ihA ihe ↦ fund_termEq_emptyrec ihA ihe)
    (fun _ _ ihe ihe' ↦ fund_termEq_etaUnit ihe ihe')
    Γ t u A d

/-- Fundamental theorem for substitutions (`fundamentalSubst`, Theorem 3.23). -/
theorem fundamentalSubst {eqrel : EqRelSet} {Γ Δ : Context} {σ : Subst}
    (hΓ : CtxWf Γ) (hΔ : CtxWf Δ) (hσ : SubstWf Δ σ Γ) :
    ValidCtx eqrel Γ ∧ ValidSubst eqrel Δ σ Γ := by
  induction hσ with
  | nil => exact ⟨.nil, trivial⟩
  | @cons Γ A σ _ hHead ih =>
      cases hΓ with
      | cons wfΓ wfA =>
          rcases fundamental (eqrel := eqrel) wfA with ⟨vΓ, hA⟩
          rcases fundamentalTerm (eqrel := eqrel) hHead with ⟨vΔ, hA', ht⟩
          rcases ih wfΓ with ⟨_, hTail⟩
          have idA := (hA' (soundContext vΔ) (idSubstS vΔ)).red
          have idA' := (hA hΔ hTail).red
          have idt := (ht (soundContext vΔ) (idSubstS vΔ)).term
          exact ⟨.cons vΓ hA,
            ValidSubst.cons hTail idA'
              (irrelevanceTerm'' (subst_id _) (subst_id _) idA idA' idt)⟩

/-- Fundamental theorem for substitution equality (`fundamentalSubstEq`, Theorem 3.23). -/
theorem fundamentalSubstEq {eqrel : EqRelSet} {Γ Δ : Context} {σ σ' : Subst}
    (hΓ : CtxWf Γ) (hΔ : CtxWf Δ) (hσσ' : SubstEq Δ σ σ' Γ) :
    ValidCtx eqrel Γ ∧ ValidSubst eqrel Δ σ Γ ∧ ValidSubst eqrel Δ σ' Γ ∧
    ValidSubstEq eqrel Δ σ σ' Γ := by
  induction hσσ' with
  | nil => exact ⟨.nil, trivial, trivial, trivial⟩
  | @cons Γ A σ σ' _ hHeadEq ih =>
      cases hΓ with
      | cons wfΓ wfA =>
          rcases fundamental (eqrel := eqrel) wfA with ⟨vΓ, hA⟩
          rcases ih wfΓ with ⟨_, hTail, hTail', hTailEq⟩
          rcases fundamentalTermEq (eqrel := eqrel) hHeadEq with ⟨vΔ, hA', ht, ht', htt'⟩
          have idA := (hA' (soundContext vΔ) (idSubstS vΔ)).red
          have idA' := (hA hΔ hTail).red
          have idA'' := (hA hΔ hTail').red
          have idt := (ht (soundContext vΔ) (idSubstS vΔ)).term
          have idt' := (ht' (soundContext vΔ) (idSubstS vΔ)).term
          have idtt' := htt' (soundContext vΔ) (idSubstS vΔ)
          exact ⟨.cons vΓ hA,
            ValidSubst.cons hTail idA'
              (irrelevanceTerm'' (subst_id _) (subst_id _) idA idA' idt),
            ValidSubst.cons hTail' idA''
              (convTerm₁ idA' idA'' ((hA hΔ hTail).eq hTail' hTailEq)
                (irrelevanceTerm'' (subst_id _) (subst_id _) idA idA' idt')),
            ValidSubstEq.cons hTailEq idA'
              (irrelevanceEqTerm'' (subst_id _) (subst_id _) (subst_id _) idA idA' idtt')⟩

/-!
## Reducibility Corollaries (`Definition/LogicalRelation/Fundamental/Reducibility.agda`)
-/

/-- Well-formed types are reducible (`reducible`). -/
theorem reducible {eqrel : EqRelSet} {Γ : Context} {A : Term} (hA : TypeWf Γ A) :
    RedType eqrel .one Γ A := by
  rcases fundamental (eqrel := eqrel) hA with ⟨vΓ, vA⟩
  exact reducibleValid vΓ vA

/-- Well-formed type equality is reducible (`reducibleEq`). -/
theorem reducibleEq {eqrel : EqRelSet} {Γ : Context} {A B : Term} (hAB : TypeEq Γ A B) :
    ∃ (pA : RedType eqrel .one Γ A), RedType eqrel .one Γ B ∧ RedEq pA B := by
  rcases fundamentalEq (eqrel := eqrel) hAB with ⟨vΓ, vA, vB, vAB⟩
  exact ⟨reducibleValid vΓ vA, reducibleValid vΓ vB, reducibleValidEq vΓ vA vAB⟩

/-- Well-formed terms are reducible (`reducibleTerm`). -/
theorem reducibleTerm {eqrel : EqRelSet} {Γ : Context} {t A : Term} (ht : HasType Γ t A) :
    ∃ (pA : RedType eqrel .one Γ A), RedTerm pA t := by
  rcases fundamentalTerm (eqrel := eqrel) ht with ⟨vΓ, vA, vt⟩
  exact ⟨reducibleValid vΓ vA, reducibleValidTerm vΓ vA vt⟩

/-- Well-formed term equality is reducible (`reducibleEqTerm`). -/
theorem reducibleEqTerm {eqrel : EqRelSet} {Γ : Context} {t u A : Term} (htu : TermEq Γ t u A) :
    ∃ (pA : RedType eqrel .one Γ A), RedTermEq pA t u := by
  rcases fundamentalTermEq (eqrel := eqrel) htu with ⟨vΓ, vA, _, _, vtu⟩
  exact ⟨reducibleValid vΓ vA, reducibleValidEqTerm vΓ vA vtu⟩

end LogrelMLTT
