import LogrelMLTT.LogicalRelationProperties

namespace LogrelMLTT

/-!
# Substitution Validity and Logical Relation Introductions

This module translates:
- `Definition/LogicalRelation/Substitution.agda`
- `Definition/LogicalRelation/Substitution/Irrelevance.agda`
- `Definition/LogicalRelation/Substitution/Reflexivity.agda`
- `Definition/LogicalRelation/Substitution/Weakening.agda`
- `Definition/LogicalRelation/Substitution/Conversion.agda`
- `Definition/LogicalRelation/Substitution/MaybeEmbed.agda`
- `Definition/LogicalRelation/Substitution/Properties.agda`
- `Definition/LogicalRelation/Substitution/Escape.agda`
- `Definition/LogicalRelation/Substitution/Reducibility.agda`
- `Definition/LogicalRelation/Substitution/Reduction.agda`
- `Definition/LogicalRelation/Substitution/Introductions/Universe.agda`
- `Definition/LogicalRelation/Substitution/Introductions/Nat.agda`
- `Definition/LogicalRelation/Substitution/Introductions/SingleSubst.agda`
- `Definition/LogicalRelation/Substitution/Introductions/Pi.agda`
- `Definition/LogicalRelation/Substitution/Introductions/Application.agda`
-/

/-!
## Validity Judgments (`Definition/LogicalRelation/Substitution.agda`)
-/

/-- Logical relation for substitutions (`Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ`). -/
def ValidSubst (eqrel : EqRelSet) (Δ : Context) (σ : Subst) : Context → Prop
  | [] => True
  | A :: Γ =>
      ValidSubst eqrel Δ (tailSubst σ) Γ ∧
      ∃ (l : TypeLevel) (pA : RedType eqrel l Δ (subst (tailSubst σ) A)),
        RedTerm pA (headSubst σ)

/-- Logical relation for equality of substitutions (`Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]`). -/
def ValidSubstEq (eqrel : EqRelSet) (Δ : Context) (σ σ' : Subst) : Context → Prop
  | [] => True
  | A :: Γ =>
      ValidSubstEq eqrel Δ (tailSubst σ) (tailSubst σ') Γ ∧
      ∃ (l : TypeLevel) (pA : RedType eqrel l Δ (subst (tailSubst σ) A)),
        RedTermEq pA (headSubst σ) (headSubst σ')

/-- Pointwise type validity at a target context `Δ` and substitution `σ`. -/
structure ValidTypeAt (eqrel : EqRelSet) (l : TypeLevel) (Δ Γ : Context)
    (σ : Subst) (A : Term) : Prop where
  red : RedType eqrel l Δ (subst σ A)
  eq : ∀ {σ' : Subst},
    ValidSubst eqrel Δ σ' Γ →
    ValidSubstEq eqrel Δ σ σ' Γ →
    RedEq red (subst σ' A)

/-- Validity of types (`Γ ⊩ᵛ⟨ l ⟩ A / [Γ]`). -/
def ValidType (eqrel : EqRelSet) (l : TypeLevel) (Γ : Context) (A : Term) : Prop :=
  ∀ {Δ : Context} {σ : Subst},
    CtxWf Δ → ValidSubst eqrel Δ σ Γ →
    ValidTypeAt eqrel l Δ Γ σ A

/-- Validity of contexts (`⊩ᵛ Γ`). -/
inductive ValidCtx (eqrel : EqRelSet) : Context → Prop where
  | nil : ValidCtx eqrel []
  | cons {Γ : Context} {A : Term} {l : TypeLevel} :
      ValidCtx eqrel Γ → ValidType eqrel l Γ A → ValidCtx eqrel (A :: Γ)

/-- Pointwise term validity at a target context `Δ` and substitution `σ`. -/
structure ValidTermAt {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} (Γ : Context)
    {σ : Subst} {A : Term} (pA : RedType eqrel l Δ (subst σ A)) (t : Term) : Prop where
  term : RedTerm pA (subst σ t)
  eq : ∀ {σ' : Subst},
    ValidSubst eqrel Δ σ' Γ →
    ValidSubstEq eqrel Δ σ σ' Γ →
    RedTermEq pA (subst σ t) (subst σ' t)

/-- Validity of terms (`Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A]`). -/
def ValidTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hA : ValidType eqrel l Γ A) (t : Term) : Prop :=
  ∀ {Δ : Context} {σ : Subst} (hΔ : CtxWf Δ) (hσ : ValidSubst eqrel Δ σ Γ),
    ValidTermAt Γ (hA hΔ hσ).red t

/-- Validity of type equality (`Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A]`). -/
def ValidTypeEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hA : ValidType eqrel l Γ A) (B : Term) : Prop :=
  ∀ {Δ : Context} {σ : Subst} (hΔ : CtxWf Δ) (hσ : ValidSubst eqrel Δ σ Γ),
    RedEq (hA hΔ hσ).red (subst σ B)

/-- Validity of term equality (`Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A]`). -/
def ValidTermEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hA : ValidType eqrel l Γ A) (t u : Term) : Prop :=
  ∀ {Δ : Context} {σ : Subst} (hΔ : CtxWf Δ) (hσ : ValidSubst eqrel Δ σ Γ),
    RedTermEq (hA hΔ hσ).red (subst σ t) (subst σ u)

/-- Valid term equality bundled with validity of its type and terms (`[ Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] ]`). -/
structure ModelsTermEq (eqrel : EqRelSet) (l : TypeLevel) (Γ : Context) (t u A : Term) : Prop where
  validA : ValidType eqrel l Γ A
  validt : ValidTerm validA t
  validu : ValidTerm validA u
  validEq : ValidTermEq validA t u

/-- Validity of term reduction (`Γ ⊩ᵛ t ⇒ u ∷ A / [Γ]`). -/
def ValidRedTerm (eqrel : EqRelSet) (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {σ : Subst},
    CtxWf Δ → ValidSubst eqrel Δ σ Γ →
    Step Δ (subst σ t) (subst σ u) (subst σ A)

/-!
## Projections and Constructors for `ValidSubst` and `ValidSubstEq`
-/

theorem ValidSubst.tail {eqrel : EqRelSet} {Δ : Context} {σ : Subst} {A : Term} {Γ : Context}
    (hσ : ValidSubst eqrel Δ σ (A :: Γ)) : ValidSubst eqrel Δ (tailSubst σ) Γ :=
  hσ.1

theorem ValidSubst.head {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} {σ : Subst}
    {A : Term} {Γ : Context}
    (hA : ValidType eqrel l Γ A) (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ (A :: Γ)) :
    RedTerm (hA hΔ hσ.1).red (headSubst σ) := by
  rcases hσ.2 with ⟨_, pA₀, hHead⟩
  exact irrelevanceTerm pA₀ (hA hΔ hσ.1).red hHead

theorem ValidSubst.cons {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} {σ : Subst}
    {A : Term} {Γ : Context}
    (hTail : ValidSubst eqrel Δ (tailSubst σ) Γ)
    (pA : RedType eqrel l Δ (subst (tailSubst σ) A))
    (hHead : RedTerm pA (headSubst σ)) :
    ValidSubst eqrel Δ σ (A :: Γ) :=
  ⟨hTail, l, pA, hHead⟩

theorem ValidSubstEq.tail {eqrel : EqRelSet} {Δ : Context} {σ σ' : Subst} {A : Term} {Γ : Context}
    (hσσ' : ValidSubstEq eqrel Δ σ σ' (A :: Γ)) :
    ValidSubstEq eqrel Δ (tailSubst σ) (tailSubst σ') Γ :=
  hσσ'.1

theorem ValidSubstEq.head {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} {σ σ' : Subst}
    {A : Term} {Γ : Context}
    (hA : ValidType eqrel l Γ A) (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ (A :: Γ))
    (hσσ' : ValidSubstEq eqrel Δ σ σ' (A :: Γ)) :
    RedTermEq (hA hΔ hσ.1).red (headSubst σ) (headSubst σ') := by
  rcases hσσ'.2 with ⟨_, pA₀, hHeadEq⟩
  exact irrelevanceEqTerm pA₀ (hA hΔ hσ.1).red hHeadEq

theorem ValidSubstEq.cons {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} {σ σ' : Subst}
    {A : Term} {Γ : Context}
    (hTailEq : ValidSubstEq eqrel Δ (tailSubst σ) (tailSubst σ') Γ)
    (pA : RedType eqrel l Δ (subst (tailSubst σ) A))
    (hHeadEq : RedTermEq pA (headSubst σ) (headSubst σ')) :
    ValidSubstEq eqrel Δ σ σ' (A :: Γ) :=
  ⟨hTailEq, l, pA, hHeadEq⟩

/-!
## Irrelevance (`Definition/LogicalRelation/Substitution/Irrelevance.agda`)
-/

theorem irrelevanceSubst {eqrel : EqRelSet} {σ : Subst} {Γ Δ : Context}
    (_hΓ _hΓ' : ValidCtx eqrel Γ) (_hΔ _hΔ' : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ) : ValidSubst eqrel Δ σ Γ :=
  hσ

theorem irrelevanceSubst' {eqrel : EqRelSet} {σ : Subst} {Γ Δ Δ' : Context}
    (heq : Δ = Δ') (hσ : ValidSubst eqrel Δ σ Γ) : ValidSubst eqrel Δ' σ Γ := by
  subst heq
  exact hσ

theorem irrelevanceSubstEq {eqrel : EqRelSet} {σ σ' : Subst} {Γ Δ : Context}
    (_hΓ _hΓ' : ValidCtx eqrel Γ) (_hΔ _hΔ' : CtxWf Δ)
    (_hσ _hσ' : ValidSubst eqrel Δ σ Γ)
    (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ) : ValidSubstEq eqrel Δ σ σ' Γ :=
  hσσ'

theorem irrelevanceValid {eqrel : EqRelSet} {l : TypeLevel} {A : Term} {Γ : Context}
    (_hΓ _hΓ' : ValidCtx eqrel Γ)
    (hA : ValidType eqrel l Γ A) : ValidType eqrel l Γ A :=
  hA

/-- Irrelevance of valid types under lifting of equal context types (`irrelevanceLift`). -/
theorem irrelevanceLift {eqrel : EqRelSet} {l : TypeLevel} {A F H : Term} {Γ : Context}
    (hF : ValidType eqrel l Γ F)
    (hH : ValidType eqrel l Γ H)
    (hFH : ValidTypeEq hF H)
    (hA : ValidType eqrel l (F :: Γ) A) :
    ValidType eqrel l (H :: Γ) A := by
  intro Δ σ hΔ hσ
  have hTail : ValidSubst eqrel Δ (tailSubst σ) Γ := hσ.tail
  have hHeadH : RedTerm (hH hΔ hTail).red (headSubst σ) := hσ.head hH hΔ
  have hHeadF : RedTerm (hF hΔ hTail).red (headSubst σ) :=
    convTerm₂ (hF hΔ hTail).red (hH hΔ hTail).red (hFH hΔ hTail) hHeadH
  have hσF : ValidSubst eqrel Δ σ (F :: Γ) :=
    ValidSubst.cons hTail (hF hΔ hTail).red hHeadF
  refine ⟨(hA hΔ hσF).red, fun {σ'} hσ' hσσ' ↦ ?_⟩
  have hTail' : ValidSubst eqrel Δ (tailSubst σ') Γ := hσ'.tail
  have hHeadH' : RedTerm (hH hΔ hTail').red (headSubst σ') := hσ'.head hH hΔ
  have hHeadF' : RedTerm (hF hΔ hTail').red (headSubst σ') :=
    convTerm₂ (hF hΔ hTail').red (hH hΔ hTail').red (hFH hΔ hTail') hHeadH'
  have hσ'F : ValidSubst eqrel Δ σ' (F :: Γ) :=
    ValidSubst.cons hTail' (hF hΔ hTail').red hHeadF'
  have hHeadEqH : RedTermEq (hH hΔ hTail).red (headSubst σ) (headSubst σ') :=
    hσσ'.head hH hΔ hσ
  have hHeadEqF : RedTermEq (hF hΔ hTail).red (headSubst σ) (headSubst σ') :=
    convEqTerm₂ (hF hΔ hTail).red (hH hΔ hTail).red (hFH hΔ hTail) hHeadEqH
  have hσσ'F : ValidSubstEq eqrel Δ σ σ' (F :: Γ) :=
    ValidSubstEq.cons hσσ'.tail (hF hΔ hTail).red hHeadEqF
  exact (hA hΔ hσF).eq hσ'F hσσ'F

/-- Irrelevance of valid type equality (`irrelevanceEq`). -/
theorem irrelevanceValidEq {eqrel : EqRelSet} {l l' : TypeLevel} {A B : Term} {Γ : Context}
    (hA : ValidType eqrel l Γ A)
    (hA' : ValidType eqrel l' Γ A)
    (hAB : ValidTypeEq hA B) :
    ValidTypeEq hA' B := by
  intro Δ σ hΔ hσ
  exact irrelevanceEq (hA hΔ hσ).red (hA' hΔ hσ).red (hAB hΔ hσ)

/-- Irrelevance of valid terms (`irrelevanceTerm`). -/
theorem irrelevanceValidTerm {eqrel : EqRelSet} {l l' : TypeLevel} {A t : Term} {Γ : Context}
    (hA : ValidType eqrel l Γ A)
    (hA' : ValidType eqrel l' Γ A)
    (ht : ValidTerm hA t) :
    ValidTerm hA' t := by
  intro Δ σ hΔ hσ
  refine ⟨irrelevanceTerm (hA hΔ hσ).red (hA' hΔ hσ).red (ht hΔ hσ).term,
    fun hσ' hσσ' ↦ irrelevanceEqTerm (hA hΔ hσ).red (hA' hΔ hσ).red ((ht hΔ hσ).eq hσ' hσσ')⟩

/-- Irrelevance of valid terms with propositionally equal types (`irrelevanceTerm′`). -/
theorem irrelevanceValidTerm' {eqrel : EqRelSet} {l l' : TypeLevel} {A A' t : Term} {Γ : Context}
    (heq : A = A')
    (hA : ValidType eqrel l Γ A)
    (hA' : ValidType eqrel l' Γ A')
    (ht : ValidTerm hA t) :
    ValidTerm hA' t := by
  subst heq
  exact irrelevanceValidTerm hA hA' ht

/-- Irrelevance of valid terms under lifting of equal context types (`irrelevanceTermLift`). -/
theorem irrelevanceTermLift {eqrel : EqRelSet} {l : TypeLevel} {A F H t : Term} {Γ : Context}
    (hF : ValidType eqrel l Γ F)
    (hH : ValidType eqrel l Γ H)
    (hFH : ValidTypeEq hF H)
    (hA : ValidType eqrel l (F :: Γ) A)
    (ht : ValidTerm hA t) :
    ValidTerm (irrelevanceLift hF hH hFH hA) t := by
  intro Δ σ hΔ hσ
  have hTail : ValidSubst eqrel Δ (tailSubst σ) Γ := hσ.tail
  have hHeadH : RedTerm (hH hΔ hTail).red (headSubst σ) := hσ.head hH hΔ
  have hHeadF : RedTerm (hF hΔ hTail).red (headSubst σ) :=
    convTerm₂ (hF hΔ hTail).red (hH hΔ hTail).red (hFH hΔ hTail) hHeadH
  have hσF : ValidSubst eqrel Δ σ (F :: Γ) :=
    ValidSubst.cons hTail (hF hΔ hTail).red hHeadF
  refine ⟨(ht hΔ hσF).term, fun {σ'} hσ' hσσ' ↦ ?_⟩
  have hTail' : ValidSubst eqrel Δ (tailSubst σ') Γ := hσ'.tail
  have hHeadH' : RedTerm (hH hΔ hTail').red (headSubst σ') := hσ'.head hH hΔ
  have hHeadF' : RedTerm (hF hΔ hTail').red (headSubst σ') :=
    convTerm₂ (hF hΔ hTail').red (hH hΔ hTail').red (hFH hΔ hTail') hHeadH'
  have hσ'F : ValidSubst eqrel Δ σ' (F :: Γ) :=
    ValidSubst.cons hTail' (hF hΔ hTail').red hHeadF'
  have hHeadEqH : RedTermEq (hH hΔ hTail).red (headSubst σ) (headSubst σ') :=
    hσσ'.head hH hΔ hσ
  have hHeadEqF : RedTermEq (hF hΔ hTail).red (headSubst σ) (headSubst σ') :=
    convEqTerm₂ (hF hΔ hTail).red (hH hΔ hTail).red (hFH hΔ hTail) hHeadEqH
  have hσσ'F : ValidSubstEq eqrel Δ σ σ' (F :: Γ) :=
    ValidSubstEq.cons hσσ'.tail (hF hΔ hTail).red hHeadEqF
  exact (ht hΔ hσF).eq hσ'F hσσ'F

/-- Irrelevance of valid term equality (`irrelevanceEqTerm`). -/
theorem irrelevanceValidEqTerm {eqrel : EqRelSet} {l l' : TypeLevel} {A t u : Term} {Γ : Context}
    (hA : ValidType eqrel l Γ A)
    (hA' : ValidType eqrel l' Γ A)
    (htu : ValidTermEq hA t u) :
    ValidTermEq hA' t u := by
  intro Δ σ hΔ hσ
  exact irrelevanceEqTerm (hA hΔ hσ).red (hA' hΔ hσ).red (htu hΔ hσ)

/-!
## Reflexivity (`Definition/LogicalRelation/Substitution/Reflexivity.agda`)
-/

/-- Reflexivity of valid types (`reflᵛ`). -/
theorem reflValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hA : ValidType eqrel l Γ A) : ValidTypeEq hA A :=
  fun hΔ hσ ↦ reflEq (hA hΔ hσ).red

/-- Reflexivity of valid terms (`reflᵗᵛ`). -/
theorem reflValidTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t : Term}
    (hA : ValidType eqrel l Γ A) (ht : ValidTerm hA t) :
    ValidTermEq hA t t :=
  fun hΔ hσ ↦ reflEqTerm (hA hΔ hσ).red (ht hΔ hσ).term

/-!
## Weakening (`Definition/LogicalRelation/Substitution/Weakening.agda`)
-/

/-- Weakening of valid types by one (`wk1ᵛ`). -/
theorem wk1Valid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A F : Term}
    (hA : ValidType eqrel l Γ A) :
    ValidType eqrel l (F :: Γ) (wk1 A) := by
  intro Δ σ hΔ hσ
  have pA : RedType eqrel l Δ (subst (tailSubst σ) A) := (hA hΔ hσ.tail).red
  have pA' : RedType eqrel l Δ (subst σ (wk1 A)) :=
    irrelevance' (subst_wk A).symm pA
  refine ⟨pA', fun {σ'} hσ' hσσ' ↦ ?_⟩
  exact irrelevanceEq'' (subst_wk A).symm (subst_wk A).symm pA pA'
    ((hA hΔ hσ.tail).eq hσ'.tail hσσ'.tail)

/-- Weakening of valid type equality by one (`wk1Eqᵛ`). -/
theorem wk1ValidEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B F : Term}
    (hA : ValidType eqrel l Γ A) (hAB : ValidTypeEq hA B) :
    ValidTypeEq (wk1Valid (F := F) hA) (wk1 B) := by
  intro Δ σ hΔ hσ
  have pA : RedType eqrel l Δ (subst (tailSubst σ) A) := (hA hΔ hσ.tail).red
  have pA' : RedType eqrel l Δ (subst σ (wk1 A)) :=
    irrelevance' (subst_wk A).symm pA
  exact irrelevanceEq'' (subst_wk A).symm (subst_wk B).symm pA pA' (hAB hΔ hσ.tail)

/-!
## Conversion (`Definition/LogicalRelation/Substitution/Conversion.agda`)
-/

/-- Conversion from left to right of valid terms (`convᵛ`). -/
theorem convValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {t A B : Term}
    (hA : ValidType eqrel l Γ A)
    (hB : ValidType eqrel l Γ B)
    (hAB : ValidTypeEq hA B)
    (ht : ValidTerm hA t) :
    ValidTerm hB t := by
  intro Δ σ hΔ hσ
  have pA := (hA hΔ hσ).red
  have pB := (hB hΔ hσ).red
  have pAB := hAB hΔ hσ
  refine ⟨convTerm₁ pA pB pAB (ht hΔ hσ).term,
    fun hσ' hσσ' ↦ convEqTerm₁ pA pB pAB ((ht hΔ hσ).eq hσ' hσσ')⟩

/-- Conversion from right to left of valid terms (`conv₂ᵛ`). -/
theorem conv2Valid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {t A B : Term}
    (hA : ValidType eqrel l Γ A)
    (hB : ValidType eqrel l Γ B)
    (hAB : ValidTypeEq hA B)
    (ht : ValidTerm hB t) :
    ValidTerm hA t := by
  intro Δ σ hΔ hσ
  have pA := (hA hΔ hσ).red
  have pB := (hB hΔ hσ).red
  have pAB := hAB hΔ hσ
  refine ⟨convTerm₂ pA pB pAB (ht hΔ hσ).term,
    fun hσ' hσσ' ↦ convEqTerm₂ pA pB pAB ((ht hΔ hσ).eq hσ' hσσ')⟩

/-- Conversion from left to right of valid term equality (`convEqᵛ`). -/
theorem convValidEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {t u A B : Term}
    (hA : ValidType eqrel l Γ A)
    (hB : ValidType eqrel l Γ B)
    (hAB : ValidTypeEq hA B)
    (htu : ValidTermEq hA t u) :
    ValidTermEq hB t u := by
  intro Δ σ hΔ hσ
  exact convEqTerm₁ (hA hΔ hσ).red (hB hΔ hσ).red (hAB hΔ hσ) (htu hΔ hσ)

/-!
## Level Embedding (`Definition/LogicalRelation/Substitution/MaybeEmbed.agda`)
-/

/-- Embedding of any validity level into `¹` (`maybeEmbᵛ`). -/
theorem maybeEmbValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hA : ValidType eqrel l Γ A) : ValidType eqrel .one Γ A := by
  intro Δ σ hΔ hσ
  have pA := (hA hΔ hσ).red
  have pA' := maybeEmb pA
  exact ⟨pA', fun hσ' hσσ' ↦ irrelevanceEq pA pA' ((hA hΔ hσ).eq hσ' hσσ')⟩

/-- Embedding of validity level `⁰` into any level `l` (`maybeEmbₛ′`). -/
theorem maybeEmbValid' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hA : ValidType eqrel .zero Γ A) : ValidType eqrel l Γ A := by
  intro Δ σ hΔ hσ
  have pA := (hA hΔ hσ).red
  have pA' := maybeEmb' (l := l) pA
  exact ⟨pA', fun hσ' hσσ' ↦ irrelevanceEq pA pA' ((hA hΔ hσ).eq hσ' hσσ')⟩

/-!
## Substitution Properties (`Definition/LogicalRelation/Substitution/Properties.agda`)
-/

/-- Valid substitutions are syntactically well-formed (`wellformedSubst`). -/
theorem wellformedSubst {eqrel : EqRelSet} {Γ Δ : Context} {σ : Subst}
    (hΓ : ValidCtx eqrel Γ) (hΔ : CtxWf Δ) (hσ : ValidSubst eqrel Δ σ Γ) :
    SubstWf Δ σ Γ := by
  induction hΓ generalizing σ with
  | nil => exact .nil
  | cons _ hA ih =>
      exact .cons (ih hσ.tail) (escapeTerm (hA hΔ hσ.tail).red (hσ.head hA hΔ))

/-- Valid substitution equality is syntactically well-formed (`wellformedSubstEq`). -/
theorem wellformedSubstEq {eqrel : EqRelSet} {Γ Δ : Context} {σ σ' : Subst}
    (hΓ : ValidCtx eqrel Γ) (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ) (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ) :
    SubstEq Δ σ σ' Γ := by
  induction hΓ generalizing σ σ' with
  | nil => exact .nil
  | cons _ hA ih =>
      exact .cons (ih hσ.tail hσσ'.tail)
        (eqrel.termToEq (escapeTermEq (hA hΔ hσ.tail).red (hσσ'.head hA hΔ hσ)))

/-- Extend a valid substitution with a term (`consSubstS`). -/
theorem consSubstS {eqrel : EqRelSet} {l : TypeLevel} {σ : Subst} {t A : Term} {Γ Δ : Context}
    (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ)
    (hA : ValidType eqrel l Γ A)
    (ht : RedTerm (hA hΔ hσ).red t) :
    ValidSubst eqrel Δ (consSubst σ t) (A :: Γ) :=
  ValidSubst.cons hσ (hA hΔ hσ).red ht

/-- Extend a valid substitution equality with a term (`consSubstSEq`). -/
theorem consSubstSEq {eqrel : EqRelSet} {l : TypeLevel} {σ σ' : Subst} {t A : Term}
    {Γ Δ : Context}
    (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ)
    (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ)
    (hA : ValidType eqrel l Γ A)
    (ht : RedTerm (hA hΔ hσ).red t) :
    ValidSubstEq eqrel Δ (consSubst σ t) (consSubst σ' t) (A :: Γ) :=
  ValidSubstEq.cons hσσ' (hA hΔ hσ).red (reflEqTerm (hA hΔ hσ).red ht)

/-- Weakening of valid substitutions (`wkSubstS`). -/
theorem wkSubstS {eqrel : EqRelSet} {ρ : Wk} {σ : Subst} {Γ Δ Δ' : Context}
    (hρ : WkCtx ρ Δ' Δ) (hΔ' : CtxWf Δ')
    (hσ : ValidSubst eqrel Δ σ Γ) :
    ValidSubst eqrel Δ' (wkSubst ρ σ) Γ := by
  induction Γ generalizing σ with
  | nil => trivial
  | cons A Γ ih =>
      rcases hσ with ⟨hTail, l, pA, hHead⟩
      have pA_wk : RedType eqrel l Δ' (wk ρ (subst (tailSubst σ) A)) :=
        wkRed hρ hΔ' pA
      have pA' : RedType eqrel l Δ' (subst (tailSubst (wkSubst ρ σ)) A) :=
        irrelevance' (wk_subst A) pA_wk
      have hHead_wk : RedTerm pA_wk (wk ρ (headSubst σ)) :=
        wkRedTerm hρ hΔ' pA hHead
      have hHead' : RedTerm pA' (headSubst (wkSubst ρ σ)) :=
        irrelevanceTerm' (wk_subst A) pA_wk pA' hHead_wk
      exact ⟨ih hTail, l, pA', hHead'⟩

/-- Weakening of valid substitution equality (`wkSubstSEq`). -/
theorem wkSubstSEq {eqrel : EqRelSet} {ρ : Wk} {σ σ' : Subst} {Γ Δ Δ' : Context}
    (hρ : WkCtx ρ Δ' Δ) (hΔ' : CtxWf Δ')
    (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ) :
    ValidSubstEq eqrel Δ' (wkSubst ρ σ) (wkSubst ρ σ') Γ := by
  induction Γ generalizing σ σ' with
  | nil => trivial
  | cons A Γ ih =>
      rcases hσσ' with ⟨hTailEq, l, pA, hHeadEq⟩
      have pA_wk : RedType eqrel l Δ' (wk ρ (subst (tailSubst σ) A)) :=
        wkRed hρ hΔ' pA
      have pA' : RedType eqrel l Δ' (subst (tailSubst (wkSubst ρ σ)) A) :=
        irrelevance' (wk_subst A) pA_wk
      have hHeadEq_wk : RedTermEq pA_wk (wk ρ (headSubst σ)) (wk ρ (headSubst σ')) :=
        wkRedTermEq hρ hΔ' pA hHeadEq
      have hHeadEq' : RedTermEq pA' (headSubst (wkSubst ρ σ)) (headSubst (wkSubst ρ σ')) :=
        irrelevanceEqTerm' (wk_subst A) pA_wk pA' hHeadEq_wk
      exact ⟨ih hTailEq, l, pA', hHeadEq'⟩

/-- Weaken a valid substitution by one type (`wk1SubstS`). -/
theorem wk1SubstS {eqrel : EqRelSet} {F : Term} {σ : Subst} {Γ Δ : Context}
    (hΔ : CtxWf Δ) (hF : TypeWf Δ F)
    (hσ : ValidSubst eqrel Δ σ Γ) :
    ValidSubst eqrel (F :: Δ) (wk1Subst σ) Γ :=
  wkSubstS (.step .id) (.cons hΔ hF) hσ

/-- Weaken a valid substitution equality by one type (`wk1SubstSEq`). -/
theorem wk1SubstSEq {eqrel : EqRelSet} {F : Term} {σ σ' : Subst} {Γ Δ : Context}
    (hΔ : CtxWf Δ) (hF : TypeWf Δ F)
    (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ) :
    ValidSubstEq eqrel (F :: Δ) (wk1Subst σ) (wk1Subst σ') Γ :=
  wkSubstSEq (.step .id) (.cons hΔ hF) hσσ'

/-- Lift a valid substitution (`liftSubstS`). -/
theorem member_here_wk1Subst (σ : Subst) (F : Term) (Δ : Context) :
    Member 0 (subst (wk1Subst σ) F) (subst σ F :: Δ) := by
  change Member 0 (subst (wkSubst (.step .id) σ) F) (subst σ F :: Δ)
  rw [← wk_subst (ρ := .step .id) (σ := σ) F]
  exact .here

theorem liftSubstS {eqrel : EqRelSet} {l : TypeLevel} {F : Term} {σ : Subst} {Γ Δ : Context}
    (hΔ : CtxWf Δ)
    (hF : ValidType eqrel l Γ F)
    (hσ : ValidSubst eqrel Δ σ Γ) :
    ValidSubst eqrel (subst σ F :: Δ) (liftSubst σ) (F :: Γ) := by
  have hσF : TypeWf Δ (subst σ F) := escape (hF hΔ hσ).red
  have hΔF : CtxWf (subst σ F :: Δ) := .cons hΔ hσF
  have hTail : ValidSubst eqrel (subst σ F :: Δ) (wk1Subst σ) Γ :=
    wk1SubstS hΔ hσF hσ
  have pF : RedType eqrel l (subst σ F :: Δ) (subst (wk1Subst σ) F) :=
    (hF hΔF hTail).red
  have hLookup : Member 0 (subst (wk1Subst σ) F) (subst σ F :: Δ) :=
    member_here_wk1Subst σ F Δ
  have hVar0 : HasType (subst σ F :: Δ) (.var 0) (subst (wk1Subst σ) F) :=
    .var hΔF hLookup
  have hHead : RedTerm pF (.var 0) :=
    neuTerm pF (.var 0) hVar0 (eqrel.varRefl hVar0)
  exact ⟨hTail, l, pF, hHead⟩

/-- Lift a valid substitution equality (`liftSubstSEq`). -/
theorem liftSubstSEq {eqrel : EqRelSet} {l : TypeLevel} {F : Term} {σ σ' : Subst} {Γ Δ : Context}
    (hΔ : CtxWf Δ)
    (hF : ValidType eqrel l Γ F)
    (hσ : ValidSubst eqrel Δ σ Γ)
    (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ) :
    ValidSubstEq eqrel (subst σ F :: Δ) (liftSubst σ) (liftSubst σ') (F :: Γ) := by
  have hσF : TypeWf Δ (subst σ F) := escape (hF hΔ hσ).red
  have hΔF : CtxWf (subst σ F :: Δ) := .cons hΔ hσF
  have hTail : ValidSubst eqrel (subst σ F :: Δ) (wk1Subst σ) Γ :=
    wk1SubstS hΔ hσF hσ
  have hTailEq : ValidSubstEq eqrel (subst σ F :: Δ) (wk1Subst σ) (wk1Subst σ') Γ :=
    wk1SubstSEq hΔ hσF hσσ'
  have pF : RedType eqrel l (subst σ F :: Δ) (subst (wk1Subst σ) F) :=
    (hF hΔF hTail).red
  have hLookup : Member 0 (subst (wk1Subst σ) F) (subst σ F :: Δ) :=
    member_here_wk1Subst σ F Δ
  have hVar0 : HasType (subst σ F :: Δ) (.var 0) (subst (wk1Subst σ) F) :=
    .var hΔF hLookup
  have hHeadEq : RedTermEq pF (.var 0) (.var 0) :=
    neuEqTerm pF (.var 0) (.var 0) hVar0 hVar0 (eqrel.varRefl hVar0)
  exact ⟨hTailEq, l, pF, hHeadEq⟩

/-- Valid contexts are well-formed and admit a valid identity substitution
(`soundContext` and `idSubstS`). -/
theorem soundContext_and_idSubstS {eqrel : EqRelSet} {Γ : Context}
    (hΓ : ValidCtx eqrel Γ) :
    CtxWf Γ ∧ ValidSubst eqrel Γ idSubst Γ := by
  induction hΓ with
  | nil => exact ⟨.nil, trivial⟩
  | @cons Γ A l _ hA ih =>
      rcases ih with ⟨wfΓ, idΓ⟩
      have pA_id : RedType eqrel l Γ (subst idSubst A) := (hA wfΓ idΓ).red
      have wfA : TypeWf Γ A := escape (irrelevance' (subst_id A) pA_id)
      have wfΓA : CtxWf (A :: Γ) := .cons wfΓ wfA
      have hTail : ValidSubst eqrel (A :: Γ) (wk1Subst idSubst) Γ :=
        wk1SubstS wfΓ wfA idΓ
      have pA_tail : RedType eqrel l (A :: Γ) (subst (wk1Subst idSubst) A) :=
        (hA wfΓA hTail).red
      have hLookup : Member 0 (subst (wk1Subst idSubst) A) (A :: Γ) := by
        have h0 := member_here_wk1Subst idSubst A Γ
        rwa [subst_id A] at h0
      have hVar0 : HasType (A :: Γ) (.var 0) (subst (wk1Subst idSubst) A) :=
        .var wfΓA hLookup
      have hHead : RedTerm pA_tail (.var 0) :=
        neuTerm pA_tail (.var 0) hVar0 (eqrel.varRefl hVar0)
      exact ⟨wfΓA, hTail, l, pA_tail, hHead⟩

/-- Valid contexts are syntactically well-formed (`soundContext`). -/
theorem soundContext {eqrel : EqRelSet} {Γ : Context} (hΓ : ValidCtx eqrel Γ) : CtxWf Γ :=
  (soundContext_and_idSubstS hΓ).1

/-- Identity substitution is valid on a valid context (`idSubstS`). -/
theorem idSubstS {eqrel : EqRelSet} {Γ : Context} (hΓ : ValidCtx eqrel Γ) :
    ValidSubst eqrel Γ idSubst Γ :=
  (soundContext_and_idSubstS hΓ).2

/-- Reflexivity of valid substitutions (`reflSubst`). -/
theorem reflSubst {eqrel : EqRelSet} {σ : Subst} {Γ Δ : Context}
    (hσ : ValidSubst eqrel Δ σ Γ) :
    ValidSubstEq eqrel Δ σ σ Γ := by
  induction Γ generalizing σ with
  | nil => trivial
  | cons A Γ ih =>
      rcases hσ with ⟨hTail, l, pA, hHead⟩
      exact ⟨ih hTail, l, pA, reflEqTerm pA hHead⟩

/-- Reflexivity of the valid identity substitution (`reflIdSubst`). -/
theorem reflIdSubst {eqrel : EqRelSet} {Γ : Context} (hΓ : ValidCtx eqrel Γ) :
    ValidSubstEq eqrel Γ idSubst idSubst Γ :=
  reflSubst (idSubstS hΓ)

/-- Symmetry of valid substitution equality (`symS`). -/
theorem symS {eqrel : EqRelSet} {σ σ' : Subst} {Γ Δ : Context}
    (hΓ : ValidCtx eqrel Γ) (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ)
    (hσ' : ValidSubst eqrel Δ σ' Γ)
    (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ) :
    ValidSubstEq eqrel Δ σ' σ Γ := by
  induction hΓ generalizing σ σ' with
  | nil => trivial
  | @cons Γ A l _ hA ih =>
      have pA := (hA hΔ hσ.tail).red
      have pA' := (hA hΔ hσ'.tail).red
      have pAA' := (hA hΔ hσ.tail).eq hσ'.tail hσσ'.tail
      have hSym : RedTermEq pA (headSubst σ') (headSubst σ) :=
        symEqTerm pA (hσσ'.head hA hΔ hσ)
      exact ⟨ih hσ.tail hσ'.tail hσσ'.tail,
        l, pA', convEqTerm₁ pA pA' pAA' hSym⟩

/-- Transitivity of valid substitution equality (`transS`). -/
theorem transS {eqrel : EqRelSet} {σ σ' σ'' : Subst} {Γ Δ : Context}
    (hΓ : ValidCtx eqrel Γ) (hΔ : CtxWf Δ)
    (hσ : ValidSubst eqrel Δ σ Γ)
    (hσ' : ValidSubst eqrel Δ σ' Γ)
    (_hσ'' : ValidSubst eqrel Δ σ'' Γ)
    (hσσ' : ValidSubstEq eqrel Δ σ σ' Γ)
    (hσ'σ'' : ValidSubstEq eqrel Δ σ' σ'' Γ) :
    ValidSubstEq eqrel Δ σ σ'' Γ := by
  induction hΓ generalizing σ σ' σ'' with
  | nil => trivial
  | @cons Γ A l _ hA ih =>
      have pA := (hA hΔ hσ.tail).red
      have pA' := (hA hΔ hσ'.tail).red
      have pAA' := (hA hΔ hσ.tail).eq hσ'.tail hσσ'.tail
      have h1 : RedTermEq pA (headSubst σ) (headSubst σ') :=
        hσσ'.head hA hΔ hσ
      have h2' : RedTermEq pA' (headSubst σ') (headSubst σ'') :=
        hσ'σ''.head hA hΔ hσ'
      have h2 : RedTermEq pA (headSubst σ') (headSubst σ'') :=
        convEqTerm₂ pA pA' pAA' h2'
      exact ⟨ih hσ.tail hσ'.tail _hσ''.tail hσσ'.tail hσ'σ''.tail,
        l, pA, transEqTerm pA h1 h2⟩

/-!
## Escape and Reducibility of Valid Judgments
(`Definition/LogicalRelation/Substitution/Escape.agda` and `Reducibility.agda`)
-/

/-- Valid types are reducible (`reducibleᵛ`). -/
theorem reducibleValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hΓ : ValidCtx eqrel Γ) (hA : ValidType eqrel l Γ A) :
    RedType eqrel l Γ A :=
  irrelevance' (subst_id A) (hA (soundContext hΓ) (idSubstS hΓ)).red

/-- Valid type equality is reducible (`reducibleEqᵛ`). -/
theorem reducibleValidEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B : Term}
    (hΓ : ValidCtx eqrel Γ) (hA : ValidType eqrel l Γ A)
    (hAB : ValidTypeEq hA B) :
    RedEq (reducibleValid hΓ hA) B := by
  have wfΓ := soundContext hΓ
  have idΓ := idSubstS hΓ
  exact irrelevanceEq'' (subst_id A) (subst_id B)
    (hA wfΓ idΓ).red (reducibleValid hΓ hA) (hAB wfΓ idΓ)

/-- Valid terms are reducible (`reducibleTermᵛ`). -/
theorem reducibleValidTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {t A : Term}
    (hΓ : ValidCtx eqrel Γ) (hA : ValidType eqrel l Γ A)
    (ht : ValidTerm hA t) :
    RedTerm (reducibleValid hΓ hA) t := by
  have wfΓ := soundContext hΓ
  have idΓ := idSubstS hΓ
  exact irrelevanceTerm'' (subst_id A) (subst_id t)
    (hA wfΓ idΓ).red (reducibleValid hΓ hA) (ht wfΓ idΓ).term

/-- Valid term equality is reducible (`reducibleEqTermᵛ`). -/
theorem reducibleValidEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {t u A : Term}
    (hΓ : ValidCtx eqrel Γ) (hA : ValidType eqrel l Γ A)
    (htu : ValidTermEq hA t u) :
    RedTermEq (reducibleValid hΓ hA) t u := by
  have wfΓ := soundContext hΓ
  have idΓ := idSubstS hΓ
  exact irrelevanceEqTerm'' (subst_id t) (subst_id u) (subst_id A)
    (hA wfΓ idΓ).red (reducibleValid hΓ hA) (htu wfΓ idΓ)

/-- Valid types are syntactically well-formed (`escapeᵛ`). -/
theorem escapeValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hΓ : ValidCtx eqrel Γ) (hA : ValidType eqrel l Γ A) :
    TypeWf Γ A :=
  escape (reducibleValid hΓ hA)

/-- Valid type equality respects `eqrel.TypeEqRel` (`escapeEqᵛ`). -/
theorem escapeValidEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B : Term}
    (hΓ : ValidCtx eqrel Γ) (hA : ValidType eqrel l Γ A)
    (hAB : ValidTypeEq hA B) :
    eqrel.TypeEqRel Γ A B :=
  escapeEq (reducibleValid hΓ hA) (reducibleValidEq hΓ hA hAB)

/-- Valid terms are syntactically well-typed (`escapeTermᵛ`). -/
theorem escapeValidTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {t A : Term}
    (hΓ : ValidCtx eqrel Γ) (hA : ValidType eqrel l Γ A)
    (ht : ValidTerm hA t) :
    HasType Γ t A :=
  escapeTerm (reducibleValid hΓ hA) (reducibleValidTerm hΓ hA ht)

/-- Valid term equality respects `eqrel.TermEqRel` (`escapeEqTermᵛ`). -/
theorem escapeValidEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {t u A : Term}
    (hΓ : ValidCtx eqrel Γ) (hA : ValidType eqrel l Γ A)
    (htu : ValidTermEq hA t u) :
    eqrel.TermEqRel Γ t u A :=
  escapeTermEq (reducibleValid hΓ hA) (reducibleValidEqTerm hΓ hA htu)

/-!
## Weak-Head Expansion of Valid Terms (`Definition/LogicalRelation/Substitution/Reduction.agda`)
-/

/-- Weak-head expansion of valid terms (`redSubstTermᵛ`). -/
theorem redSubstTermValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u : Term}
    (htu : ValidRedTerm eqrel Γ t u A)
    (hA : ValidType eqrel l Γ A)
    (hu : ValidTerm hA u) :
    ValidTerm hA t ∧ ValidTermEq hA t u := by
  refine ⟨fun hΔ hσ ↦ ?_, fun hΔ hσ ↦ ?_⟩
  · have pA := (hA hΔ hσ).red
    rcases redSubstTerm (htu hΔ hσ) pA (hu hΔ hσ).term with ⟨ht, htu_eq⟩
    refine ⟨ht, fun {σ'} hσ' hσσ' ↦ ?_⟩
    have pA' := (hA hΔ hσ').red
    have pAA' := (hA hΔ hσ).eq hσ' hσσ'
    rcases redSubstTerm (htu hΔ hσ') pA' (hu hΔ hσ').term with ⟨_, ht'u'_eq⟩
    exact transEqTerm pA htu_eq
      (transEqTerm pA ((hu hΔ hσ).eq hσ' hσσ')
        (convEqTerm₂ pA pA' pAA' (symEqTerm pA' ht'u'_eq)))
  · exact (redSubstTerm (htu hΔ hσ) (hA hΔ hσ).red (hu hΔ hσ).term).2

/-!
## Universe Introductions (`Definition/LogicalRelation/Substitution/Introductions/Universe.agda`)
-/

/-- Helper constructing `RedType eqrel .one Δ .univ`. -/
theorem redUOne {eqrel : EqRelSet} {Δ : Context} (hΔ : CtxWf Δ) :
    RedType eqrel .one Δ .univ :=
  ⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩⟩

/-- Validity of the universe type `U` (`Uᵛ`). -/
theorem UValid {eqrel : EqRelSet} {Γ : Context} :
    ValidType eqrel .one Γ .univ :=
  fun hΔ _ ↦
    ⟨redUOne hΔ,
      fun _ _ ↦ ⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) _,
        .U ⟨.zeroLT, hΔ⟩, rfl⟩⟩

/-- Valid terms of type `U` are valid types (`univᵛ`). -/
theorem univValid {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A : Term}
    (hU : ValidType eqrel l Γ .univ)
    (hA : ValidTerm hU A) :
    ValidType eqrel l' Γ A := by
  intro Δ σ hΔ hσ
  have pU := (hU hΔ hσ).red
  have pA₀ : RedType eqrel .zero Δ (subst σ A) := univEq pU (hA hΔ hσ).term
  have pA : RedType eqrel l' Δ (subst σ A) := maybeEmb' pA₀
  exact ⟨pA, fun hσ' hσσ' ↦ univEqEq pU pA ((hA hΔ hσ).eq hσ' hσσ')⟩

/-- Valid term equality of type `U` is valid type equality (`univEqᵛ`). -/
theorem univEqValid {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B : Term}
    (hU : ValidType eqrel l' Γ .univ)
    (hA : ValidType eqrel l Γ A)
    (hAB : ValidTermEq hU A B) :
    ValidTypeEq hA B :=
  fun hΔ hσ ↦ univEqEq (hU hΔ hσ).red (hA hΔ hσ).red (hAB hΔ hσ)

/-!
## Natural Number Introductions (`Definition/LogicalRelation/Substitution/Introductions/Nat.agda`)
-/

/-- Helper constructing `RedType eqrel l Δ .nat`. -/
theorem redNat {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} (hΔ : CtxWf Δ) :
    RedType eqrel l Δ .nat :=
  ⟨RedNatRel eqrel Δ, .nat (idRedWf (.nat hΔ))⟩

/-- Validity of `ℕ` (`ℕᵛ`). -/
theorem natValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} :
    ValidType eqrel l Γ .nat :=
  fun hΔ _ ↦
    ⟨redNat hΔ,
      fun _ _ ↦ ⟨RedNatRel eqrel _, .nat (idRedWf (.nat hΔ)), .refl (.nat hΔ)⟩⟩

/-- Validity of `ℕ` as a term of `U` (`ℕᵗᵛ`). -/
theorem natTermValid {eqrel : EqRelSet} {Γ : Context} :
    ValidTerm (UValid (eqrel := eqrel) (Γ := Γ)) .nat := by
  intro Δ σ hΔ _
  have hNatU : HasType Δ .nat .univ := .nat hΔ
  have hNatWf : TypeWf Δ .nat := .nat hΔ
  refine ⟨⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩,
      ⟨.nat, idRedTermWf hNatU, .nat, eqrel.natTermRefl hΔ,
        RedNatRel eqrel Δ, .nat (idRedWf hNatWf)⟩⟩,
    fun _ _ ↦ ⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩,
      ⟨.nat, .nat, idRedTermWf hNatU, idRedTermWf hNatU, .nat, .nat,
        eqrel.natTermRefl hΔ, RedNatRel eqrel Δ, .nat (idRedWf hNatWf),
        ⟨RedNatRel eqrel Δ, .nat (idRedWf hNatWf)⟩, .refl hNatWf⟩⟩⟩

/-- Validity of `zero` (`zeroᵛ`). -/
theorem zeroValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} :
    ValidTerm (natValid (eqrel := eqrel) (l := l) (Γ := Γ)) .zero := by
  intro Δ σ hΔ _
  have hZero : HasType Δ .zero .nat := .zero hΔ
  have hNatWf : TypeWf Δ .nat := .nat hΔ
  refine ⟨⟨RedNatRel eqrel Δ, .nat (idRedWf hNatWf),
      .mk .zero .zero (idRedTermWf hZero) (eqrel.zeroRefl hΔ) .zero⟩,
    fun _ _ ↦ ⟨RedNatRel eqrel Δ, .nat (idRedWf hNatWf),
      .mk .zero .zero .zero .zero (idRedTermWf hZero) (idRedTermWf hZero)
        (eqrel.zeroRefl hΔ) .zero⟩⟩

/-- Validity of `suc` (`sucᵛ`). -/
theorem sucValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {n : Term}
    (hNat : ValidType eqrel l Γ .nat)
    (hn : ValidTerm hNat n) :
    ValidTerm hNat (.succ n) := by
  intro Δ σ hΔ hσ
  have pNat := (hNat hΔ hσ).red
  refine ⟨sucTerm pNat (hn hΔ hσ).term,
    fun hσ' hσσ' ↦ sucEqTerm pNat ((hn hΔ hσ).eq hσ' hσσ')⟩

/-!
## Empty and Unit Introductions
(`Definition/LogicalRelation/Substitution/Introductions/Empty.agda` and `Unit.agda`)
-/

/-- Helper constructing `RedType eqrel l Δ .empty`. -/
theorem redEmpty {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} (hΔ : CtxWf Δ) :
    RedType eqrel l Δ .empty :=
  ⟨RedEmptyRel eqrel Δ, .empty (idRedWf (.empty hΔ))⟩

/-- Validity of `Empty` (`Emptyᵛ`). -/
theorem emptyValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} :
    ValidType eqrel l Γ .empty :=
  fun hΔ _ ↦
    ⟨redEmpty hΔ,
      fun _ _ ↦ ⟨RedEmptyRel eqrel _, .empty (idRedWf (.empty hΔ)), .refl (.empty hΔ)⟩⟩

/-- Validity of `Empty` as a term of `U` (`Emptyᵗᵛ`). -/
theorem emptyTermValid {eqrel : EqRelSet} {Γ : Context} :
    ValidTerm (UValid (eqrel := eqrel) (Γ := Γ)) .empty := by
  intro Δ σ hΔ _
  have hEmptyU : HasType Δ .empty .univ := .empty hΔ
  have hEmptyWf : TypeWf Δ .empty := .empty hΔ
  refine ⟨⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩,
      ⟨.empty, idRedTermWf hEmptyU, .empty, eqrel.emptyTermRefl hΔ,
        RedEmptyRel eqrel Δ, .empty (idRedWf hEmptyWf)⟩⟩,
    fun _ _ ↦ ⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩,
      ⟨.empty, .empty, idRedTermWf hEmptyU, idRedTermWf hEmptyU, .empty, .empty,
        eqrel.emptyTermRefl hΔ, RedEmptyRel eqrel Δ, .empty (idRedWf hEmptyWf),
        ⟨RedEmptyRel eqrel Δ, .empty (idRedWf hEmptyWf)⟩, .refl hEmptyWf⟩⟩⟩

/-- Helper constructing `RedType eqrel l Δ .unit`. -/
theorem redUnit {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} (hΔ : CtxWf Δ) :
    RedType eqrel l Δ .unit :=
  ⟨RedUnitRel Δ, .unit (idRedWf (.unit hΔ))⟩

/-- Validity of `Unit` (`Unitᵛ`). -/
theorem unitValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} :
    ValidType eqrel l Γ .unit :=
  fun hΔ _ ↦
    ⟨redUnit hΔ,
      fun _ _ ↦ ⟨RedUnitRel _, .unit (idRedWf (.unit hΔ)), .refl (.unit hΔ)⟩⟩

/-- Validity of `Unit` as a term of `U` (`Unitᵗᵛ`). -/
theorem unitTermValid {eqrel : EqRelSet} {Γ : Context} :
    ValidTerm (UValid (eqrel := eqrel) (Γ := Γ)) .unit := by
  intro Δ σ hΔ _
  have hUnitU : HasType Δ .unit .univ := .unit hΔ
  have hUnitWf : TypeWf Δ .unit := .unit hΔ
  refine ⟨⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩,
      ⟨.unit, idRedTermWf hUnitU, .unit, eqrel.unitTermRefl hΔ,
        RedUnitRel Δ, .unit (idRedWf hUnitWf)⟩⟩,
    fun _ _ ↦ ⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩,
      ⟨.unit, .unit, idRedTermWf hUnitU, idRedTermWf hUnitU, .unit, .unit,
        eqrel.unitTermRefl hΔ, RedUnitRel Δ, .unit (idRedWf hUnitWf),
        ⟨RedUnitRel Δ, .unit (idRedWf hUnitWf)⟩, .refl hUnitWf⟩⟩⟩

/-- Validity of `star` (`starᵛ`). -/
theorem starValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} :
    ValidTerm (unitValid (eqrel := eqrel) (l := l) (Γ := Γ)) .star := by
  intro Δ σ hΔ _
  have hStar : HasType Δ .star .unit := .star hΔ
  have hUnitWf : TypeWf Δ .unit := .unit hΔ
  refine ⟨⟨RedUnitRel Δ, .unit (idRedWf hUnitWf),
      .mk .star (idRedTermWf hStar) .star⟩,
    fun _ _ ↦ ⟨RedUnitRel Δ, .unit (idRedWf hUnitWf),
      ⟨hStar, hStar⟩⟩⟩

/-- Validity of `η-unit` (`η-unitᵛ`). -/
theorem etaUnitValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {e e' : Term}
    (hUnit : ValidType eqrel l Γ .unit)
    (he : ValidTerm hUnit e)
    (he' : ValidTerm hUnit e') :
    ValidTermEq hUnit e e' := by
  intro Δ σ hΔ hσ
  have pUnit := (hUnit hΔ hσ).red
  have pUnit₀ : RedType eqrel l Δ .unit := redUnit hΔ
  have hte : HasType Δ (subst σ e) .unit := escapeTerm pUnit (he hΔ hσ).term
  have hte' : HasType Δ (subst σ e') .unit := escapeTerm pUnit (he' hΔ hσ).term
  exact irrelevanceEqTerm pUnit₀ pUnit
    ⟨RedUnitRel Δ, .unit (idRedWf (.unit hΔ)), ⟨hte, hte'⟩⟩

/-!
## Single Variable Substitution (`Definition/LogicalRelation/Substitution/Introductions/SingleSubst.agda`)
-/

/-- Validity of substituting a single variable in a type (`substS`). -/
theorem substS {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (ht : ValidTerm hF t) :
    ValidType eqrel l Γ (subst0 G t) := by
  intro Δ σ hΔ hσ
  have hσt : ValidSubst eqrel Δ (consSubst σ (subst σ t)) (F :: Γ) :=
    consSubstS hΔ hσ hF (ht hΔ hσ).term
  have pGt := (hG hΔ hσt).red
  have pGt' : RedType eqrel l Δ (subst σ (subst0 G t)) :=
    irrelevance' (substConsId G) pGt
  refine ⟨pGt', fun {σ'} hσ' hσσ' ↦ ?_⟩
  have hσ't : ValidSubst eqrel Δ (consSubst σ' (subst σ' t)) (F :: Γ) :=
    consSubstS hΔ hσ' hF (ht hΔ hσ').term
  have hσσ't : ValidSubstEq eqrel Δ (consSubst σ (subst σ t)) (consSubst σ' (subst σ' t)) (F :: Γ) :=
    ValidSubstEq.cons hσσ' (hF hΔ hσ).red ((ht hΔ hσ).eq hσ' hσσ')
  exact irrelevanceEq'' (substConsId G) (substConsId G) pGt pGt'
    ((hG hΔ hσt).eq hσ't hσσ't)

/-- Validity of substituting a single variable in type equality (`substSEq`). -/
theorem substSEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F F' G G' t t' : Term}
    (hF : ValidType eqrel l Γ F)
    (hF' : ValidType eqrel l Γ F')
    (hFF' : ValidTypeEq hF F')
    (hG : ValidType eqrel l (F :: Γ) G)
    (hG' : ValidType eqrel l (F' :: Γ) G')
    (hGG' : ValidTypeEq hG G')
    (ht : ValidTerm hF t)
    (ht' : ValidTerm hF' t')
    (htt' : ValidTermEq hF t t') :
    ValidTypeEq (substS hF hG ht) (subst0 G' t') := by
  intro Δ σ hΔ hσ
  have hσt : ValidSubst eqrel Δ (consSubst σ (subst σ t)) (F :: Γ) :=
    consSubstS hΔ hσ hF (ht hΔ hσ).term
  have pGt := (hG hΔ hσt).red
  have pGt' : RedType eqrel l Δ (subst σ (subst0 G t)) :=
    irrelevance' (substConsId G) pGt
  have ht_conv : ValidTerm hF' t := convValid hF hF' hFF' ht
  have hσt_F' : ValidSubst eqrel Δ (consSubst σ (subst σ t)) (F' :: Γ) :=
    consSubstS hΔ hσ hF' (ht_conv hΔ hσ).term
  have pG't := (hG' hΔ hσt_F').red
  have hGt_G't : RedEq pGt' (subst (consSubst σ (subst σ t)) G') :=
    irrelevanceEq' (substConsId G) pGt pGt' (hGG' hΔ hσt)
  have hσt'_F' : ValidSubst eqrel Δ (consSubst σ (subst σ t')) (F' :: Γ) :=
    consSubstS hΔ hσ hF' (ht' hΔ hσ).term
  have htt'_F' : ValidTermEq hF' t t' := convValidEq hF hF' hFF' htt'
  have hσσ_t_t' : ValidSubstEq eqrel Δ (consSubst σ (subst σ t)) (consSubst σ (subst σ t')) (F' :: Γ) :=
    ValidSubstEq.cons (reflSubst hσ) (hF' hΔ hσ).red (htt'_F' hΔ hσ)
  have hG't_G't' : RedEq pG't (subst σ (subst0 G' t')) :=
    irrelevanceEq'' rfl (substConsId G') pG't pG't ((hG' hΔ hσt_F').eq hσt'_F' hσσ_t_t')
  have pG't'_raw := (hG' hΔ hσt'_F').red
  have pG't' : RedType eqrel l Δ (subst σ (subst0 G' t')) :=
    irrelevance' (substConsId G') pG't'_raw
  exact transEq pGt' pG't pG't' hGt_G't hG't_G't'

/-- Validity of substituting a single variable in a term (`substSTerm`). -/
theorem substSTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t f : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (hf : ValidTerm hG f)
    (ht : ValidTerm hF t) :
    ValidTerm (substS hF hG ht) (subst0 f t) := by
  intro Δ σ hΔ hσ
  have hσt : ValidSubst eqrel Δ (consSubst σ (subst σ t)) (F :: Γ) :=
    consSubstS hΔ hσ hF (ht hΔ hσ).term
  have pGt := (hG hΔ hσt).red
  have pGt' : RedType eqrel l Δ (subst σ (subst0 G t)) :=
    irrelevance' (substConsId G) pGt
  have pft : RedTerm pGt' (subst σ (subst0 f t)) :=
    irrelevanceTerm'' (substConsId G) (substConsId f) pGt pGt' (hf hΔ hσt).term
  refine ⟨pft, fun {σ'} hσ' hσσ' ↦ ?_⟩
  have hσ't : ValidSubst eqrel Δ (consSubst σ' (subst σ' t)) (F :: Γ) :=
    consSubstS hΔ hσ' hF (ht hΔ hσ').term
  have hσσ't : ValidSubstEq eqrel Δ (consSubst σ (subst σ t)) (consSubst σ' (subst σ' t)) (F :: Γ) :=
    ValidSubstEq.cons hσσ' (hF hΔ hσ).red ((ht hΔ hσ).eq hσ' hσσ')
  exact irrelevanceEqTerm'' (substConsId f) (substConsId f) (substConsId G)
    pGt pGt' ((hf hΔ hσt).eq hσ't hσσ't)

/-- Validity of single lifted substitution in types (`subst↑S`). -/
theorem substUpS {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (ht : ValidTerm (wk1Valid (F := F) hF) t) :
    ValidType eqrel l (F :: Γ) (substKeep G t) := by
  intro Δ σ hΔ hσ
  have hwk1F : ValidType eqrel l (F :: Γ) (wk1 F) := wk1Valid (F := F) hF
  have pwk1F := (hwk1F hΔ hσ).red
  have pTailF := (hF hΔ hσ.tail).red
  have ht' : RedTerm pTailF (subst σ t) :=
    irrelevanceTerm' (subst_wk F) pwk1F pTailF (ht hΔ hσ).term
  have hσ_t : ValidSubst eqrel Δ (consSubst (tailSubst σ) (subst σ t)) (F :: Γ) :=
    ValidSubst.cons hσ.tail pTailF ht'
  have pGt := (hG hΔ hσ_t).red
  have pGt' : RedType eqrel l Δ (subst σ (substKeep G t)) :=
    irrelevance' (substConsTailId (G := G) (t := t) (σ := σ)) pGt
  refine ⟨pGt', fun {σ'} hσ' hσσ' ↦ ?_⟩
  have pwk1F' := (hwk1F hΔ hσ').red
  have pTailF' := (hF hΔ hσ'.tail).red
  have ht'_σ' : RedTerm pTailF' (subst σ' t) :=
    irrelevanceTerm' (subst_wk F) pwk1F' pTailF' (ht hΔ hσ').term
  have hσ'_t : ValidSubst eqrel Δ (consSubst (tailSubst σ') (subst σ' t)) (F :: Γ) :=
    ValidSubst.cons hσ'.tail pTailF' ht'_σ'
  have hteq : RedTermEq pTailF (subst σ t) (subst σ' t) :=
    irrelevanceEqTerm' (subst_wk F) pwk1F pTailF ((ht hΔ hσ).eq hσ' hσσ')
  have hσσ'_t : ValidSubstEq eqrel Δ
      (consSubst (tailSubst σ) (subst σ t))
      (consSubst (tailSubst σ') (subst σ' t)) (F :: Γ) :=
    ValidSubstEq.cons hσσ'.tail pTailF hteq
  exact irrelevanceEq''
    (substConsTailId (G := G) (t := t) (σ := σ))
    (substConsTailId (G := G) (t := t) (σ := σ'))
    pGt pGt' ((hG hΔ hσ_t).eq hσ'_t hσσ'_t)

/-- Validity of single lifted substitution in type equality (`subst↑SEq`). -/
theorem substUpSEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G G' t t' : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (hG' : ValidType eqrel l (F :: Γ) G')
    (hGG' : ValidTypeEq hG G')
    (ht : ValidTerm (wk1Valid (F := F) hF) t)
    (ht' : ValidTerm (wk1Valid (F := F) hF) t')
    (htt' : ValidTermEq (wk1Valid (F := F) hF) t t') :
    ValidTypeEq (substUpS hF hG ht) (substKeep G' t') := by
  intro Δ σ hΔ hσ
  have hwk1F : ValidType eqrel l (F :: Γ) (wk1 F) := wk1Valid (F := F) hF
  have pwk1F := (hwk1F hΔ hσ).red
  have pTailF := (hF hΔ hσ.tail).red
  have ht₁ : RedTerm pTailF (subst σ t) :=
    irrelevanceTerm' (subst_wk F) pwk1F pTailF (ht hΔ hσ).term
  have ht₂ : RedTerm pTailF (subst σ t') :=
    irrelevanceTerm' (subst_wk F) pwk1F pTailF (ht' hΔ hσ).term
  have htt'₁ : RedTermEq pTailF (subst σ t) (subst σ t') :=
    irrelevanceEqTerm' (subst_wk F) pwk1F pTailF (htt' hΔ hσ)
  have hσ_t : ValidSubst eqrel Δ (consSubst (tailSubst σ) (subst σ t)) (F :: Γ) :=
    ValidSubst.cons hσ.tail pTailF ht₁
  have hσ_t' : ValidSubst eqrel Δ (consSubst (tailSubst σ) (subst σ t')) (F :: Γ) :=
    ValidSubst.cons hσ.tail pTailF ht₂
  have pGt := (hG hΔ hσ_t).red
  have pGt' := irrelevance' (substConsTailId (G := G) (t := t) (σ := σ)) pGt
  have pG't := (hG' hΔ hσ_t).red
  have pG't' := irrelevance' (substConsTailId (G := G') (t := t) (σ := σ)) pG't
  have pG't₂ := (hG' hΔ hσ_t').red
  have pG't₂' := irrelevance' (substConsTailId (G := G') (t := t') (σ := σ)) pG't₂
  have h1 : RedEq pGt' (subst σ (substKeep G' t)) :=
    irrelevanceEq''
      (substConsTailId (G := G) (t := t) (σ := σ))
      (substConsTailId (G := G') (t := t) (σ := σ))
      pGt pGt' (hGG' hΔ hσ_t)
  have hσσ_t_t' : ValidSubstEq eqrel Δ
      (consSubst (tailSubst σ) (subst σ t))
      (consSubst (tailSubst σ) (subst σ t')) (F :: Γ) :=
    ValidSubstEq.cons (reflSubst hσ.tail) pTailF htt'₁
  have h2 : RedEq pG't' (subst σ (substKeep G' t')) :=
    irrelevanceEq''
      (substConsTailId (G := G') (t := t) (σ := σ))
      (substConsTailId (G := G') (t := t') (σ := σ))
      pG't pG't' ((hG' hΔ hσ_t).eq hσ_t' hσσ_t_t')
  exact transEq pGt' pG't' pG't₂' h1 h2

theorem elimPiAt_zero {eqrel : EqRelSet} {Γ : Context} {A F G : Term}
    (D : TypeStar Γ A (.pi F G)) (p : RedType eqrel .zero Γ A) :
    RedPiAt eqrel .zero Γ A F G := by
  rcases p with ⟨rel, h⟩
  cases h with
  | U _ => cases whnfRedStar D .univ
  | nat D' => cases whrDetStar ⟨D'.reduction, .nat⟩ ⟨D, .pi⟩
  | empty D' => cases whrDetStar ⟨D'.reduction, .empty⟩ ⟨D, .pi⟩
  | unit D' => cases whrDetStar ⟨D'.reduction, .unit⟩ ⟨D, .pi⟩
  | ne neA =>
      have h := whrDetStar ⟨D, .pi⟩ ⟨neA.D.reduction, .neutral neA.neK⟩
      subst h
      cases neA.neK
  | pi D' hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext =>
      have hPi : Term.pi _ _ = Term.pi F G :=
        whrDetStar ⟨D'.reduction, .pi⟩ ⟨D, .pi⟩
      injection hPi with hF₀ hG₀
      subst hF₀ hG₀
      refine ⟨D', hF, hG, AeqA, ?_, ?_, ?_⟩
      · intro ρ Δ hρ hΔ
        rcases hF_ex hρ hΔ with ⟨r, hr⟩
        exact ⟨r, derivF hρ hΔ r hr⟩
      · intro ρ Δ a hρ hΔ ha
        have ha' : RelFHasTerm relF ρ Δ a := by
          rcases hF_ex hρ hΔ with ⟨r, hr⟩
          have hrAt := derivF hρ hΔ r hr
          exact ⟨r, hr, (RedTerm_of_LogRelAt hrAt _).mp ha⟩
        rcases hG_ex hρ hΔ ha' with ⟨s, hs⟩
        exact ⟨s, derivG hρ hΔ ha' s hs⟩
      · intro ρ Δ a b hρ hΔ ha hb hab
        have ha' : RelFHasTerm relF ρ Δ a := by
          rcases hF_ex hρ hΔ with ⟨r, hr⟩
          exact ⟨r, hr, (RedTerm_of_LogRelAt (derivF hρ hΔ r hr) _).mp ha⟩
        have hb' : RelFHasTerm relF ρ Δ b := by
          rcases hF_ex hρ hΔ with ⟨r, hr⟩
          exact ⟨r, hr, (RedTerm_of_LogRelAt (derivF hρ hΔ r hr) _).mp hb⟩
        have hab' : RelFEqTerm relF ρ Δ a b := by
          rcases hF_ex hρ hΔ with ⟨r, hr⟩
          exact ⟨r, hr, (RedTermEq_of_LogRelAt (derivF hρ hΔ r hr) _).mp hab⟩
        rcases Gext hρ hΔ ha' hb' hab' with ⟨s, hs, hB⟩
        exact ⟨s, derivG hρ hΔ ha' s hs, hB⟩
  | sigma D' => cases whrDetStar ⟨D'.reduction, .sigma⟩ ⟨D, .pi⟩
  | emb hlt _ => cases hlt

theorem elimSigmaAt_zero {eqrel : EqRelSet} {Γ : Context} {A F G : Term}
    (D : TypeStar Γ A (.sigma F G)) (p : RedType eqrel .zero Γ A) :
    RedSigmaAt eqrel .zero Γ A F G := by
  rcases p with ⟨rel, h⟩
  cases h with
  | U _ => cases whnfRedStar D .univ
  | nat D' => cases whrDetStar ⟨D'.reduction, .nat⟩ ⟨D, .sigma⟩
  | empty D' => cases whrDetStar ⟨D'.reduction, .empty⟩ ⟨D, .sigma⟩
  | unit D' => cases whrDetStar ⟨D'.reduction, .unit⟩ ⟨D, .sigma⟩
  | ne neA =>
      have h := whrDetStar ⟨D, .sigma⟩ ⟨neA.D.reduction, .neutral neA.neK⟩
      subst h
      cases neA.neK
  | pi D' => cases whrDetStar ⟨D'.reduction, .pi⟩ ⟨D, .sigma⟩
  | sigma D' hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext =>
      have hSigma : Term.sigma _ _ = Term.sigma F G :=
        whrDetStar ⟨D'.reduction, .sigma⟩ ⟨D, .sigma⟩
      injection hSigma with hF₀ hG₀
      subst hF₀ hG₀
      refine ⟨D', hF, hG, AeqA, ?_, ?_, ?_⟩
      · intro ρ Δ hρ hΔ
        rcases hF_ex hρ hΔ with ⟨r, hr⟩
        exact ⟨r, derivF hρ hΔ r hr⟩
      · intro ρ Δ a hρ hΔ ha
        have ha' : RelFHasTerm relF ρ Δ a := by
          rcases hF_ex hρ hΔ with ⟨r, hr⟩
          have hrAt := derivF hρ hΔ r hr
          exact ⟨r, hr, (RedTerm_of_LogRelAt hrAt _).mp ha⟩
        rcases hG_ex hρ hΔ ha' with ⟨s, hs⟩
        exact ⟨s, derivG hρ hΔ ha' s hs⟩
      · intro ρ Δ a b hρ hΔ ha hb hab
        have ha' : RelFHasTerm relF ρ Δ a := by
          rcases hF_ex hρ hΔ with ⟨r, hr⟩
          exact ⟨r, hr, (RedTerm_of_LogRelAt (derivF hρ hΔ r hr) _).mp ha⟩
        have hb' : RelFHasTerm relF ρ Δ b := by
          rcases hF_ex hρ hΔ with ⟨r, hr⟩
          exact ⟨r, hr, (RedTerm_of_LogRelAt (derivF hρ hΔ r hr) _).mp hb⟩
        have hab' : RelFEqTerm relF ρ Δ a b := by
          rcases hF_ex hρ hΔ with ⟨r, hr⟩
          exact ⟨r, hr, (RedTermEq_of_LogRelAt (derivF hρ hΔ r hr) _).mp hab⟩
        rcases Gext hρ hΔ ha' hb' hab' with ⟨s, hs, hB⟩
        exact ⟨s, derivG hρ hΔ ha' s hs, hB⟩
  | emb hlt _ => cases hlt

/-- Reducible substitution of `Π`-types (`substSΠ₁`). -/
theorem substSPi₁ {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {F G t : Term}
    (pPi : RedType eqrel l Γ (.pi F G))
    (pF : RedType eqrel l' Γ F)
    (ht : RedTerm pF t) :
    RedType eqrel l Γ (subst0 G t) := by
  have hGeq : subst0 (wk (.lift .id) G) t = subst0 G t := by
    rw [wk_lift_id]
  cases l with
  | zero =>
      have piA := elimPiAt_zero (.refl (escape pPi)) pPi
      have wfΓ : CtxWf Γ := wfType piA.hF
      have ht_id : RedTerm (piA.redF .id wfΓ) t :=
        irrelevanceTerm' (wk_id F).symm pF (piA.redF .id wfΓ) ht
      exact irrelevance' hGeq (piA.redG .id wfΓ ht_id)
  | one =>
      rcases elimPiAt' (.refl (escape pPi)) pPi with ⟨l₀, piA⟩
      have wfΓ : CtxWf Γ := wfType piA.hF
      have ht_id : RedTerm (piA.redF .id wfΓ) t :=
        irrelevanceTerm' (wk_id F).symm pF (piA.redF .id wfΓ) ht
      exact maybeEmb (irrelevance' hGeq (piA.redG .id wfΓ ht_id))

/-- Reducible substitution of `Π`-type congruence (`substSΠ₂`). -/
theorem substSPi₂ {eqrel : EqRelSet} {l l' l'' l''' : TypeLevel} {Γ : Context}
    {F F' G G' t t' : Term}
    (pPi : RedType eqrel l Γ (.pi F G))
    (pPiEq : RedEq pPi (.pi F' G'))
    (pF : RedType eqrel l' Γ F)
    (pF' : RedType eqrel l' Γ F')
    (ht : RedTerm pF t)
    (ht' : RedTerm pF' t')
    (htt' : RedTermEq pF t t')
    (pGt : RedType eqrel l'' Γ (subst0 G t))
    (pG't' : RedType eqrel l''' Γ (subst0 G' t')) :
    RedEq pGt (subst0 G' t') := by
  rcases elimPiAt' (.refl (escape pPi)) pPi with ⟨l₀, piA⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ rel ↦ LogRelAt eqrel l₀ Δ (wk ρ F) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ a rel ↦ LogRelAt eqrel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel
  have hAt : LogRelAt eqrel l₀ Γ (.pi F G) (RedPiRel eqrel Γ F G relF₀ relG₀) :=
    .pi piA.D piA.hF piA.hG piA.AeqA relF₀ relG₀
      piA.redF (fun _ _ _ h ↦ h) piA.redG (fun _ _ _ _ h ↦ h) piA.Gext
  have pPi₀ : RedType eqrel l₀ Γ (.pi F G) := ⟨_, hAt⟩
  have hPiEq_rel : RedPiEq eqrel Γ F G relF₀ relG₀ (.pi F' G') :=
    (RedEq_of_LogRelAt hAt pPi₀).mp (irrelevanceEq pPi pPi₀ pPiEq)
  rcases hPiEq_rel with ⟨F₂, G₂, D', _, FeqF', GeqG'⟩
  have hPi₂ : Term.pi F' G' = Term.pi F₂ G₂ := whnfRedStar D' .pi
  injection hPi₂ with hF'F₂ hG'G₂
  subst hF'F₂ hG'G₂
  have wfΓ : CtxWf Γ := wfType piA.hF
  have pF_id : RedType eqrel l₀ Γ (wk .id F) := piA.redF .id wfΓ
  have ht_id : RedTerm pF_id t := irrelevanceTerm' (wk_id F).symm pF pF_id ht
  have pFF'_id : RedEq pF_id (wk .id F') := FeqF' .id wfΓ
  have ht'_id : RedTerm pF_id t' :=
    convTerm₂' (wk_id F').symm pF_id pF' pFF'_id ht'
  have htt'_id : RedTermEq pF_id t t' :=
    irrelevanceEqTerm' (wk_id F).symm pF pF_id htt'
  have pGt_id : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) t) :=
    piA.redG .id wfΓ ht_id
  have pGt'_id : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) t') :=
    piA.redG .id wfΓ ht'_id
  have hGt_Gt' : RedEq pGt_id (subst0 (wk (.lift .id) G) t') :=
    piA.Gext .id wfΓ ht_id ht'_id htt'_id
  have hGt'_G't' : RedEq pGt'_id (subst0 (wk (.lift .id) G') t') :=
    GeqG' .id wfΓ ht'_id
  have hGeq : subst0 (wk (.lift .id) G) t = subst0 G t := by
    rw [wk_lift_id]
  have hG'eq : subst0 (wk (.lift .id) G') t' = subst0 G' t' := by
    rw [wk_lift_id]
  exact irrelevanceEq' hGeq pGt_id pGt
    (transEq pGt_id pGt'_id pG't' hGt_Gt' (irrelevanceEqR' hG'eq pGt'_id hGt'_G't'))

/-- Valid substitution of `Π`-types (`substSΠ`). -/
theorem substSPi {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t : Term}
    (hF : ValidType eqrel l Γ F)
    (hPi : ValidType eqrel l Γ (.pi F G))
    (ht : ValidTerm hF t) :
    ValidType eqrel l Γ (subst0 G t) := by
  intro Δ σ hΔ hσ
  have pGt := substSPi₁ (hPi hΔ hσ).red (hF hΔ hσ).red (ht hΔ hσ).term
  have pGt' : RedType eqrel l Δ (subst σ (subst0 G t)) :=
    irrelevance' (singleSubstLift G t).symm pGt
  refine ⟨pGt', fun {σ'} hσ' hσσ' ↦ ?_⟩
  have pGt_σ' := substSPi₁ (hPi hΔ hσ').red (hF hΔ hσ').red (ht hΔ hσ').term
  exact irrelevanceEq'' (singleSubstLift G t).symm (singleSubstLift G t).symm pGt pGt'
    (substSPi₂ (hPi hΔ hσ).red ((hPi hΔ hσ).eq hσ' hσσ')
      (hF hΔ hσ).red (hF hΔ hσ').red
      (ht hΔ hσ).term (ht hΔ hσ').term ((ht hΔ hσ).eq hσ' hσσ')
      pGt pGt_σ')

/-- Valid substitution of `Π`-congruence (`substSΠEq`). -/
theorem substSPiEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G F' G' t u : Term}
    (hF : ValidType eqrel l Γ F)
    (hF' : ValidType eqrel l Γ F')
    (hPi : ValidType eqrel l Γ (.pi F G))
    (hPi' : ValidType eqrel l Γ (.pi F' G'))
    (hPiEq : ValidTypeEq hPi (.pi F' G'))
    (ht : ValidTerm hF t)
    (hu : ValidTerm hF' u)
    (htu : ValidTermEq hF t u) :
    ValidTypeEq (substSPi hF hPi ht) (subst0 G' u) := by
  intro Δ σ hΔ hσ
  have hGt : ValidType eqrel l Γ (subst0 G t) := substSPi hF hPi ht
  have pGt := substSPi₁ (hPi hΔ hσ).red (hF hΔ hσ).red (ht hΔ hσ).term
  have pG'u := substSPi₁ (hPi' hΔ hσ).red (hF' hΔ hσ).red (hu hΔ hσ).term
  exact irrelevanceEq'' (singleSubstLift G t).symm (singleSubstLift G' u).symm
    pGt (hGt hΔ hσ).red
    (substSPi₂ (hPi hΔ hσ).red (hPiEq hΔ hσ)
      (hF hΔ hσ).red (hF' hΔ hσ).red
      (ht hΔ hσ).term (hu hΔ hσ).term (htu hΔ hσ)
      pGt pG'u)

/-- Reducible substitution of `Σ`-types (`substSΠ₁ BΣ`). -/
theorem substSSigma₁ {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {F G t : Term}
    (pSigma : RedType eqrel l Γ (.sigma F G))
    (pF : RedType eqrel l' Γ F)
    (ht : RedTerm pF t) :
    RedType eqrel l Γ (subst0 G t) := by
  have hGeq : subst0 (wk (.lift .id) G) t = subst0 G t := by
    rw [wk_lift_id]
  cases l with
  | zero =>
      have sigmaA := elimSigmaAt_zero (.refl (escape pSigma)) pSigma
      have wfΓ : CtxWf Γ := wfType sigmaA.hF
      have ht_id : RedTerm (sigmaA.redF .id wfΓ) t :=
        irrelevanceTerm' (wk_id F).symm pF (sigmaA.redF .id wfΓ) ht
      exact irrelevance' hGeq (sigmaA.redG .id wfΓ ht_id)
  | one =>
      rcases elimSigmaAt' (.refl (escape pSigma)) pSigma with ⟨l₀, sigmaA⟩
      have wfΓ : CtxWf Γ := wfType sigmaA.hF
      have ht_id : RedTerm (sigmaA.redF .id wfΓ) t :=
        irrelevanceTerm' (wk_id F).symm pF (sigmaA.redF .id wfΓ) ht
      exact maybeEmb (irrelevance' hGeq (sigmaA.redG .id wfΓ ht_id))

/-- Reducible substitution of `Σ`-type congruence (`substSΠ₂ BΣ`). -/
theorem substSSigma₂ {eqrel : EqRelSet} {l l' l'' l''' : TypeLevel} {Γ : Context}
    {F F' G G' t t' : Term}
    (pSigma : RedType eqrel l Γ (.sigma F G))
    (pSigmaEq : RedEq pSigma (.sigma F' G'))
    (pF : RedType eqrel l' Γ F)
    (pF' : RedType eqrel l' Γ F')
    (ht : RedTerm pF t)
    (ht' : RedTerm pF' t')
    (htt' : RedTermEq pF t t')
    (pGt : RedType eqrel l'' Γ (subst0 G t))
    (pG't' : RedType eqrel l''' Γ (subst0 G' t')) :
    RedEq pGt (subst0 G' t') := by
  rcases elimSigmaAt' (.refl (escape pSigma)) pSigma with ⟨l₀, sigmaA⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ rel ↦ LogRelAt eqrel l₀ Δ (wk ρ F) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ a rel ↦ LogRelAt eqrel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel
  have hAt : LogRelAt eqrel l₀ Γ (.sigma F G) (RedSigmaRel eqrel Γ F G relF₀ relG₀) :=
    .sigma sigmaA.D sigmaA.hF sigmaA.hG sigmaA.AeqA relF₀ relG₀
      sigmaA.redF (fun _ _ _ h ↦ h) sigmaA.redG (fun _ _ _ _ h ↦ h) sigmaA.Gext
  have pSigma₀ : RedType eqrel l₀ Γ (.sigma F G) := ⟨_, hAt⟩
  have hSigmaEq_rel : RedSigmaEq eqrel Γ F G relF₀ relG₀ (.sigma F' G') :=
    (RedEq_of_LogRelAt hAt pSigma₀).mp (irrelevanceEq pSigma pSigma₀ pSigmaEq)
  rcases hSigmaEq_rel with ⟨F₂, G₂, D', _, FeqF', GeqG'⟩
  have hSigma₂ : Term.sigma F' G' = Term.sigma F₂ G₂ := whnfRedStar D' .sigma
  injection hSigma₂ with hF'F₂ hG'G₂
  subst hF'F₂ hG'G₂
  have wfΓ : CtxWf Γ := wfType sigmaA.hF
  have pF_id : RedType eqrel l₀ Γ (wk .id F) := sigmaA.redF .id wfΓ
  have ht_id : RedTerm pF_id t := irrelevanceTerm' (wk_id F).symm pF pF_id ht
  have pFF'_id : RedEq pF_id (wk .id F') := FeqF' .id wfΓ
  have ht'_id : RedTerm pF_id t' :=
    convTerm₂' (wk_id F').symm pF_id pF' pFF'_id ht'
  have htt'_id : RedTermEq pF_id t t' :=
    irrelevanceEqTerm' (wk_id F).symm pF pF_id htt'
  have pGt_id : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) t) :=
    sigmaA.redG .id wfΓ ht_id
  have pGt'_id : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) t') :=
    sigmaA.redG .id wfΓ ht'_id
  have hGt_Gt' : RedEq pGt_id (subst0 (wk (.lift .id) G) t') :=
    sigmaA.Gext .id wfΓ ht_id ht'_id htt'_id
  have hGt'_G't' : RedEq pGt'_id (subst0 (wk (.lift .id) G') t') :=
    GeqG' .id wfΓ ht'_id
  have hGeq : subst0 (wk (.lift .id) G) t = subst0 G t := by
    rw [wk_lift_id]
  have hG'eq : subst0 (wk (.lift .id) G') t' = subst0 G' t' := by
    rw [wk_lift_id]
  exact irrelevanceEq' hGeq pGt_id pGt
    (transEq pGt_id pGt'_id pG't' hGt_Gt' (irrelevanceEqR' hG'eq pGt'_id hGt'_G't'))

/-- Valid substitution of `Σ`-types (`substSΠ BΣ`). -/
theorem substSSigma {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t : Term}
    (hF : ValidType eqrel l Γ F)
    (hSigma : ValidType eqrel l Γ (.sigma F G))
    (ht : ValidTerm hF t) :
    ValidType eqrel l Γ (subst0 G t) := by
  intro Δ σ hΔ hσ
  have pGt := substSSigma₁ (hSigma hΔ hσ).red (hF hΔ hσ).red (ht hΔ hσ).term
  have pGt' : RedType eqrel l Δ (subst σ (subst0 G t)) :=
    irrelevance' (singleSubstLift G t).symm pGt
  refine ⟨pGt', fun {σ'} hσ' hσσ' ↦ ?_⟩
  have pGt_σ' := substSSigma₁ (hSigma hΔ hσ').red (hF hΔ hσ').red (ht hΔ hσ').term
  exact irrelevanceEq'' (singleSubstLift G t).symm (singleSubstLift G t).symm pGt pGt'
    (substSSigma₂ (hSigma hΔ hσ).red ((hSigma hΔ hσ).eq hσ' hσσ')
      (hF hΔ hσ).red (hF hΔ hσ').red
      (ht hΔ hσ).term (ht hΔ hσ').term ((ht hΔ hσ).eq hσ' hσσ')
      pGt pGt_σ')

/-- Valid substitution of `Σ`-congruence (`substSΠEq BΣ`). -/
theorem substSSigmaEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G F' G' t u : Term}
    (hF : ValidType eqrel l Γ F)
    (hF' : ValidType eqrel l Γ F')
    (hSigma : ValidType eqrel l Γ (.sigma F G))
    (hSigma' : ValidType eqrel l Γ (.sigma F' G'))
    (hSigmaEq : ValidTypeEq hSigma (.sigma F' G'))
    (ht : ValidTerm hF t)
    (hu : ValidTerm hF' u)
    (htu : ValidTermEq hF t u) :
    ValidTypeEq (substSSigma hF hSigma ht) (subst0 G' u) := by
  intro Δ σ hΔ hσ
  have hGt : ValidType eqrel l Γ (subst0 G t) := substSSigma hF hSigma ht
  have pGt := substSSigma₁ (hSigma hΔ hσ).red (hF hΔ hσ).red (ht hΔ hσ).term
  have pG'u := substSSigma₁ (hSigma' hΔ hσ).red (hF' hΔ hσ).red (hu hΔ hσ).term
  exact irrelevanceEq'' (singleSubstLift G t).symm (singleSubstLift G' u).symm
    pGt (hGt hΔ hσ).red
    (substSSigma₂ (hSigma hΔ hσ).red (hSigmaEq hΔ hσ)
      (hF hΔ hσ).red (hF' hΔ hσ).red
      (ht hΔ hσ).term (hu hΔ hσ).term (htu hΔ hσ)
      pGt pG'u)

/-!
## `Π`-Type Introductions (`Definition/LogicalRelation/Substitution/Introductions/Pi.agda`)
-/

/-- Validity of `Π F ▹ G` (`Πᵛ`). -/
theorem piValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G) :
    ValidType eqrel l Γ (.pi F G) := by
  intro Δ σ hΔ hσ
  have pσF := (hF hΔ hσ).red
  have wfF : TypeWf Δ (subst σ F) := escape pσF
  have pσG := (hG (.cons hΔ wfF) (liftSubstS hΔ hF hσ)).red
  have wfG : TypeWf (subst σ F :: Δ) (subst (liftSubst σ) G) := escape pσG
  have wfPi : TypeWf Δ (.pi (subst σ F) (subst (liftSubst σ) G)) := .pi wfF wfG
  have hPiEq : eqrel.TypeEqRel Δ (.pi (subst σ F) (subst (liftSubst σ) G))
      (.pi (subst σ F) (subst (liftSubst σ) G)) :=
    eqrel.piCong wfF (escapeEq pσF (reflEq pσF)) (escapeEq pσG (reflEq pσG))
  let relF : Wk → Context → RedRel → Prop :=
    fun ρ Δ₁ rel ↦ LogRelAt eqrel l Δ₁ (wk ρ (subst σ F)) rel
  let relG : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ₁ a rel ↦ LogRelAt eqrel l Δ₁ (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) a) rel
  have pF_wk : ∀ {ρ Δ₁}, WkCtx ρ Δ₁ Δ → CtxWf Δ₁ → RedType eqrel l Δ₁ (wk ρ (subst σ F)) :=
    fun hρ hΔ₁ ↦ wkRed hρ hΔ₁ pσF
  have pG_wk : ∀ {ρ Δ₁ a} (hρ : WkCtx ρ Δ₁ Δ) (hΔ₁ : CtxWf Δ₁),
      RedTerm (pF_wk hρ hΔ₁) a →
      RedType eqrel l Δ₁ (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) a) := by
    intro ρ Δ₁ a hρ hΔ₁ ha
    have hρσ : ValidSubst eqrel Δ₁ (wkSubst ρ σ) Γ := wkSubstS hρ hΔ₁ hσ
    have ha' : RedTerm (hF hΔ₁ hρσ).red a :=
      irrelevanceTerm' (wk_subst F) (pF_wk hρ hΔ₁) (hF hΔ₁ hρσ).red ha
    have hρσa : ValidSubst eqrel Δ₁ (consSubst (wkSubst ρ σ) a) (F :: Γ) :=
      consSubstS hΔ₁ hρσ hF ha'
    exact irrelevance' (singleSubstWkComp a σ G).symm (hG hΔ₁ hρσa).red
  have hGext : ∀ {ρ Δ₁ a b} (hρ : WkCtx ρ Δ₁ Δ) (hΔ₁ : CtxWf Δ₁)
      (ha : RedTerm (pF_wk hρ hΔ₁) a) (hb : RedTerm (pF_wk hρ hΔ₁) b),
      RedTermEq (pF_wk hρ hΔ₁) a b →
      RedEq (pG_wk hρ hΔ₁ ha) (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) b) := by
    intro ρ Δ₁ a b hρ hΔ₁ ha hb hab
    have hρσ : ValidSubst eqrel Δ₁ (wkSubst ρ σ) Γ := wkSubstS hρ hΔ₁ hσ
    have ha' : RedTerm (hF hΔ₁ hρσ).red a :=
      irrelevanceTerm' (wk_subst F) (pF_wk hρ hΔ₁) (hF hΔ₁ hρσ).red ha
    have hb' : RedTerm (hF hΔ₁ hρσ).red b :=
      irrelevanceTerm' (wk_subst F) (pF_wk hρ hΔ₁) (hF hΔ₁ hρσ).red hb
    have hab' : RedTermEq (hF hΔ₁ hρσ).red a b :=
      irrelevanceEqTerm' (wk_subst F) (pF_wk hρ hΔ₁) (hF hΔ₁ hρσ).red hab
    have hρσa : ValidSubst eqrel Δ₁ (consSubst (wkSubst ρ σ) a) (F :: Γ) :=
      consSubstS hΔ₁ hρσ hF ha'
    have hρσb : ValidSubst eqrel Δ₁ (consSubst (wkSubst ρ σ) b) (F :: Γ) :=
      consSubstS hΔ₁ hρσ hF hb'
    have hρσab : ValidSubstEq eqrel Δ₁ (consSubst (wkSubst ρ σ) a) (consSubst (wkSubst ρ σ) b) (F :: Γ) :=
      ValidSubstEq.cons (reflSubst hρσ) (hF hΔ₁ hρσ).red hab'
    exact irrelevanceEq'' (singleSubstWkComp a σ G).symm (singleSubstWkComp b σ G).symm
      (hG hΔ₁ hρσa).red (pG_wk hρ hΔ₁ ha)
      ((hG hΔ₁ hρσa).eq hρσb hρσab)
  have hLogPi : LogRelAt eqrel l Δ (.pi (subst σ F) (subst (liftSubst σ) G))
      (RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF relG) :=
    .pi (idRedWf wfPi) wfF wfG hPiEq relF relG
      (fun hρ hΔ₁ ↦ pF_wk hρ hΔ₁)
      (fun _ _ _ hr ↦ hr)
      (fun hρ hΔ₁ ha ↦ pG_wk hρ hΔ₁ ha)
      (fun _ _ _ _ hs ↦ hs)
      (fun hρ hΔ₁ ha hb hab ↦ hGext hρ hΔ₁ ha hb hab)
  refine ⟨⟨RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF relG, hLogPi⟩,
    fun {σ'} hσ' hσσ' ↦ ?_⟩
  have pσ'F := (hF hΔ hσ').red
  have wfF' : TypeWf Δ (subst σ' F) := escape pσ'F
  have pσ'G := (hG (.cons hΔ wfF') (liftSubstS hΔ hF hσ')).red
  have wfG' : TypeWf (subst σ' F :: Δ) (subst (liftSubst σ') G) := escape pσ'G
  have wfPi' : TypeWf Δ (.pi (subst σ' F) (subst (liftSubst σ') G)) := .pi wfF' wfG'
  have wfΔF : CtxWf (subst σ F :: Δ) := .cons hΔ wfF
  have hwk1σ := wk1SubstS hΔ wfF hσ
  have hwk1σ' := wk1SubstS hΔ wfF hσ'
  have hwk1σσ' := wk1SubstSEq hΔ wfF hσσ'
  have pF_wk1σ := (hF wfΔF hwk1σ).red
  have pF_wk1σ' := (hF wfΔF hwk1σ').red
  have hLookup0 : Member 0 (subst (wk1Subst σ) F) (subst σ F :: Δ) :=
    member_here_wk1Subst σ F Δ
  have var0 : HasType (subst σ F :: Δ) (.var 0) (subst (wk1Subst σ) F) :=
    .var wfΔF hLookup0
  have var0' : HasType (subst σ F :: Δ) (.var 0) (subst (wk1Subst σ') F) :=
    .conv var0 (eqrel.typeToEq (escapeEq pF_wk1σ ((hF wfΔF hwk1σ).eq hwk1σ' hwk1σσ')))
  have hLiftσ'_in_ΔF : ValidSubst eqrel (subst σ F :: Δ) (liftSubst σ') (F :: Γ) :=
    ValidSubst.cons hwk1σ' pF_wk1σ'
      (neuTerm pF_wk1σ' (.var 0) var0' (eqrel.varRefl var0'))
  have hLiftσσ'_in_ΔF : ValidSubstEq eqrel (subst σ F :: Δ) (liftSubst σ) (liftSubst σ') (F :: Γ) :=
    ValidSubstEq.cons hwk1σσ' pF_wk1σ
      (neuEqTerm pF_wk1σ (.var 0) (.var 0) var0 var0 (eqrel.varRefl var0))
  have hPiEq_σσ' : eqrel.TypeEqRel Δ (.pi (subst σ F) (subst (liftSubst σ) G))
      (.pi (subst σ' F) (subst (liftSubst σ') G)) :=
    eqrel.piCong wfF
      (escapeEq pσF ((hF hΔ hσ).eq hσ' hσσ'))
      (escapeEq pσG ((hG wfΔF (liftSubstS hΔ hF hσ)).eq hLiftσ'_in_ΔF hLiftσσ'_in_ΔF))
  refine ⟨RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF relG, hLogPi,
    .mk (subst σ' F) (subst (liftSubst σ') G) (.refl wfPi') hPiEq_σσ'
      (fun hρ hΔ₁ ↦ wkRedEq hρ hΔ₁ pσF ((hF hΔ hσ).eq hσ' hσσ'))
      (fun {ρ Δ₁ a} hρ hΔ₁ ha ↦ ?_)⟩
  have hρσ : ValidSubst eqrel Δ₁ (wkSubst ρ σ) Γ := wkSubstS hρ hΔ₁ hσ
  have hρσ' : ValidSubst eqrel Δ₁ (wkSubst ρ σ') Γ := wkSubstS hρ hΔ₁ hσ'
  have hρσσ' : ValidSubstEq eqrel Δ₁ (wkSubst ρ σ) (wkSubst ρ σ') Γ :=
    wkSubstSEq hρ hΔ₁ hσσ'
  have ha' : RedTerm (hF hΔ₁ hρσ).red a :=
    irrelevanceTerm' (wk_subst F) (pF_wk hρ hΔ₁) (hF hΔ₁ hρσ).red ha
  have ha'' : RedTerm (hF hΔ₁ hρσ').red a :=
    convTerm₁ (hF hΔ₁ hρσ).red (hF hΔ₁ hρσ').red ((hF hΔ₁ hρσ).eq hρσ' hρσσ') ha'
  have hρσa : ValidSubst eqrel Δ₁ (consSubst (wkSubst ρ σ) a) (F :: Γ) :=
    consSubstS hΔ₁ hρσ hF ha'
  have hρσ'a : ValidSubst eqrel Δ₁ (consSubst (wkSubst ρ σ') a) (F :: Γ) :=
    consSubstS hΔ₁ hρσ' hF ha''
  have hρσa_eq : ValidSubstEq eqrel Δ₁ (consSubst (wkSubst ρ σ) a) (consSubst (wkSubst ρ σ') a) (F :: Γ) :=
    consSubstSEq hΔ₁ hρσ hρσσ' hF ha'
  exact irrelevanceEq'' (singleSubstWkComp a σ G).symm (singleSubstWkComp a σ' G).symm
    (hG hΔ₁ hρσa).red (pG_wk hρ hΔ₁ ha)
    ((hG hΔ₁ hρσa).eq hρσ'a hρσa_eq)

/-- Validity of `Π`-congruence (`Π-congᵛ`). -/
theorem piCongValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G H E : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (hH : ValidType eqrel l Γ H)
    (hE : ValidType eqrel l (H :: Γ) E)
    (hFH : ValidTypeEq hF H)
    (hGE : ValidTypeEq hG E) :
    ValidTypeEq (piValid hF hG) (.pi H E) := by
  intro Δ σ hΔ hσ
  have hPiValid : ValidType eqrel l Γ (.pi F G) := piValid hF hG
  have pPiFG := (hPiValid hΔ hσ).red
  rcases elimPiAt' (.refl (escape pPiFG)) pPiFG with ⟨l₀, piA⟩
  have pσF := (hF hΔ hσ).red
  have wfσF : TypeWf Δ (subst σ F) := escape pσF
  have pσG := (hG (.cons hΔ wfσF) (liftSubstS hΔ hF hσ)).red
  have wfσH : TypeWf Δ (subst σ H) := escape (hH hΔ hσ).red
  have wfσE : TypeWf (subst σ H :: Δ) (subst (liftSubst σ) E) :=
    escape (hE (.cons hΔ wfσH) (liftSubstS hΔ hH hσ)).red
  have hσFH : eqrel.TypeEqRel Δ (subst σ F) (subst σ H) :=
    escapeEq pσF (hFH hΔ hσ)
  have hσGE : eqrel.TypeEqRel (subst σ F :: Δ) (subst (liftSubst σ) G) (subst (liftSubst σ) E) :=
    escapeEq pσG (hGE (.cons hΔ wfσF) (liftSubstS hΔ hF hσ))
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ₁ rel ↦ LogRelAt eqrel l₀ Δ₁ (wk ρ (subst σ F)) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ₁ a rel ↦ LogRelAt eqrel l₀ Δ₁ (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) a) rel
  have hLogPi₀ : LogRelAt eqrel l₀ Δ (.pi (subst σ F) (subst (liftSubst σ) G))
      (RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀) :=
    .pi piA.D piA.hF piA.hG piA.AeqA relF₀ relG₀
      piA.redF (fun _ _ _ h ↦ h) piA.redG (fun _ _ _ _ h ↦ h) piA.Gext
  have pPiFG₀ : RedType eqrel l₀ Δ (.pi (subst σ F) (subst (liftSubst σ) G)) :=
    ⟨RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀, hLogPi₀⟩
  have hRes₀ : RedEq pPiFG₀ (.pi (subst σ H) (subst (liftSubst σ) E)) := by
    refine ⟨RedPiRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀, hLogPi₀,
      .mk (subst σ H) (subst (liftSubst σ) E) (.refl (.pi wfσH wfσE))
        (eqrel.piCong wfσF hσFH hσGE)
        (fun {ρ Δ₁} hρ hΔ₁ ↦ ?_)
        (fun {ρ Δ₁ a} hρ hΔ₁ ha ↦ ?_)⟩
    · have hρσ := wkSubstS hρ hΔ₁ hσ
      exact irrelevanceEq'' (wk_subst F).symm (wk_subst H).symm
        (hF hΔ₁ hρσ).red (piA.redF hρ hΔ₁) (hFH hΔ₁ hρσ)
    · have hρσ := wkSubstS hρ hΔ₁ hσ
      have ha' : RedTerm (hF hΔ₁ hρσ).red a :=
        irrelevanceTerm' (wk_subst F) (piA.redF hρ hΔ₁) (hF hΔ₁ hρσ).red ha
      have hρσa := consSubstS hΔ₁ hρσ hF ha'
      exact irrelevanceEq'' (singleSubstWkComp a σ G).symm (singleSubstWkComp a σ E).symm
        (hG hΔ₁ hρσa).red (piA.redG hρ hΔ₁ ha) (hGE hΔ₁ hρσa)
  exact irrelevanceEq pPiFG₀ pPiFG hRes₀

/-- Validity of `Π F ▹ G` as a term of `U` (`Πᵗᵛ`). -/
theorem piTermValid {eqrel : EqRelSet} {Γ : Context} {F G : Term}
    (hF : ValidType eqrel .one Γ F)
    (hU : ValidType eqrel .one (F :: Γ) .univ)
    (hFt : ValidTerm (UValid (eqrel := eqrel) (Γ := Γ)) F)
    (hGt : ValidTerm hU G) :
    ValidTerm (UValid (eqrel := eqrel) (Γ := Γ)) (.pi F G) := by
  intro Δ σ hΔ hσ
  have hLiftσ := liftSubstS hΔ hF hσ
  have wfF : TypeWf Δ (subst σ F) := escape (hF hΔ hσ).red
  have pUΔ : RedType eqrel .one Δ .univ := redUOne hΔ
  have wfFt : HasType Δ (subst σ F) .univ := escapeTerm pUΔ (hFt hΔ hσ).term
  have hFFt : eqrel.TermEqRel Δ (subst σ F) (subst σ F) .univ :=
    escapeTermEq pUΔ (reflEqTerm pUΔ (hFt hΔ hσ).term)
  have pU_ΔF := (hU (.cons hΔ wfF) hLiftσ).red
  have wfGt : HasType (subst σ F :: Δ) (subst (liftSubst σ) G) .univ :=
    escapeTerm pU_ΔF (hGt (.cons hΔ wfF) hLiftσ).term
  have hGGt : eqrel.TermEqRel (subst σ F :: Δ) (subst (liftSubst σ) G) (subst (liftSubst σ) G) .univ :=
    escapeTermEq pU_ΔF (reflEqTerm pU_ΔF (hGt (.cons hΔ wfF) hLiftσ).term)
  have hF₀ : ValidType eqrel .zero Γ F := univValid UValid hFt
  have hG₀ : ValidType eqrel .zero (F :: Γ) G := univValid hU hGt
  have hPi₀Valid : ValidType eqrel .zero Γ (.pi F G) := piValid hF₀ hG₀
  have hPiFG₀ := hPi₀Valid hΔ hσ
  have wfPit : HasType Δ (.pi (subst σ F) (subst (liftSubst σ) G)) .univ :=
    .pi wfFt wfGt
  rcases hPiFG₀.red with ⟨relPi₀, hLogPi₀⟩
  refine ⟨⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩,
      .mk (.pi (subst σ F) (subst (liftSubst σ) G)) (idRedTermWf wfPit)
        .pi (eqrel.piTermCong wfF hFFt hGGt) ⟨relPi₀, hLogPi₀⟩⟩,
    fun {σ'} hσ' hσσ' ↦ ?_⟩
  have hLiftσ' := liftSubstS hΔ hF hσ'
  have hwk1σ := wk1SubstS hΔ wfF hσ
  have hwk1σ' := wk1SubstS hΔ wfF hσ'
  have wfΔF : CtxWf (subst σ F :: Δ) := .cons hΔ wfF
  have hLookup0 : Member 0 (subst (wk1Subst σ) F) (subst σ F :: Δ) :=
    member_here_wk1Subst σ F Δ
  have var0 : HasType (subst σ F :: Δ) (.var 0) (subst (wk1Subst σ) F) :=
    .var wfΔF hLookup0
  have var0' : HasType (subst σ F :: Δ) (.var 0) (subst (wk1Subst σ') F) :=
    .conv var0 (eqrel.typeToEq (escapeEq (hF wfΔF hwk1σ).red
      ((hF wfΔF hwk1σ).eq hwk1σ' (wk1SubstSEq hΔ wfF hσσ'))))
  have hLiftσ'_in_ΔF : ValidSubst eqrel (subst σ F :: Δ) (liftSubst σ') (F :: Γ) :=
    ValidSubst.cons hwk1σ' (hF wfΔF hwk1σ').red
      (neuTerm (hF wfΔF hwk1σ').red (.var 0) var0' (eqrel.varRefl var0'))
  have wfF' : TypeWf Δ (subst σ' F) := escape (hF hΔ hσ').red
  have wfFt' : HasType Δ (subst σ' F) .univ := escapeTerm pUΔ (hFt hΔ hσ').term
  have wfGt' : HasType (subst σ' F :: Δ) (subst (liftSubst σ') G) .univ :=
    escapeTerm (hU (.cons hΔ wfF') hLiftσ').red (hGt (.cons hΔ wfF') hLiftσ').term
  have hFF't : eqrel.TermEqRel Δ (subst σ F) (subst σ' F) .univ :=
    escapeTermEq pUΔ ((hFt hΔ hσ).eq hσ' hσσ')
  have hGG't : eqrel.TermEqRel (subst σ F :: Δ) (subst (liftSubst σ) G) (subst (liftSubst σ') G) .univ :=
    escapeTermEq pU_ΔF ((hGt wfΔF hLiftσ).eq hLiftσ'_in_ΔF (liftSubstSEq hΔ hF hσ hσσ'))
  have hPiFG₀' := hPi₀Valid hΔ hσ'
  have hPiEq₀ := hPiFG₀.eq hσ' hσσ'
  rcases hPiEq₀ with ⟨rel₀, hLog₀, hEq₀⟩
  exact ⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩,
    .mk (.pi (subst σ F) (subst (liftSubst σ) G))
      (.pi (subst σ' F) (subst (liftSubst σ') G))
      (idRedTermWf wfPit) (idRedTermWf (.pi wfFt' wfGt'))
      .pi .pi (eqrel.piTermCong wfF hFF't hGG't)
      rel₀ hLog₀ hPiFG₀'.red hEq₀⟩

/-- Validity of `Π`-congruence as a term equality in `U` (`Π-congᵗᵛ`). -/
theorem piCongTermValid {eqrel : EqRelSet} {Γ : Context} {F G H E : Term}
    (hF : ValidType eqrel .one Γ F)
    (hH : ValidType eqrel .one Γ H)
    (hUF : ValidType eqrel .one (F :: Γ) .univ)
    (hUH : ValidType eqrel .one (H :: Γ) .univ)
    (hFt : ValidTerm (UValid (eqrel := eqrel) (Γ := Γ)) F)
    (hGt : ValidTerm hUF G)
    (hHt : ValidTerm (UValid (eqrel := eqrel) (Γ := Γ)) H)
    (hEt : ValidTerm hUH E)
    (hFHt : ValidTermEq (UValid (eqrel := eqrel) (Γ := Γ)) F H)
    (hGEt : ValidTermEq hUF G E) :
    ValidTermEq (UValid (eqrel := eqrel) (Γ := Γ)) (.pi F G) (.pi H E) := by
  intro Δ σ hΔ hσ
  have wfF : TypeWf Δ (subst σ F) := escape (hF hΔ hσ).red
  have wfH : TypeWf Δ (subst σ H) := escape (hH hΔ hσ).red
  have hLiftFσ := liftSubstS hΔ hF hσ
  have hLiftHσ := liftSubstS hΔ hH hσ
  have hF_u : ValidType eqrel .zero Γ F := univValid UValid hFt
  have hG_u : ValidType eqrel .zero (F :: Γ) G := univValid hUF hGt
  have hH_u : ValidType eqrel .zero Γ H := univValid UValid hHt
  have hE_u : ValidType eqrel .zero (H :: Γ) E := univValid hUH hEt
  have hFH_u : ValidTypeEq hF_u H := univEqValid UValid hF_u hFHt
  have hGE_u : ValidTypeEq hG_u E := univEqValid hUF hG_u hGEt
  have pUΔ : RedType eqrel .one Δ .univ := redUOne hΔ
  have wfPiFG : HasType Δ (.pi (subst σ F) (subst (liftSubst σ) G)) .univ :=
    .pi (escapeTerm pUΔ (hFt hΔ hσ).term)
      (escapeTerm (hUF (.cons hΔ wfF) hLiftFσ).red (hGt (.cons hΔ wfF) hLiftFσ).term)
  have wfPiHE : HasType Δ (.pi (subst σ H) (subst (liftSubst σ) E)) .univ :=
    .pi (escapeTerm pUΔ (hHt hΔ hσ).term)
      (escapeTerm (hUH (.cons hΔ wfH) hLiftHσ).red (hEt (.cons hΔ wfH) hLiftHσ).term)
  have hPiEq₀ := piCongValid hF_u hG_u hH_u hE_u hFH_u hGE_u hΔ hσ
  rcases hPiEq₀ with ⟨rel₀, hLog₀, hEq₀⟩
  have hPiH_u : ValidType eqrel .zero Γ (.pi H E) := piValid hH_u hE_u
  exact ⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩,
    .mk (.pi (subst σ F) (subst (liftSubst σ) G))
      (.pi (subst σ H) (subst (liftSubst σ) E))
      (idRedTermWf wfPiFG) (idRedTermWf wfPiHE)
      .pi .pi
      (eqrel.piTermCong wfF
        (escapeTermEq pUΔ (hFHt hΔ hσ))
        (escapeTermEq (hUF (.cons hΔ wfF) hLiftFσ).red (hGEt (.cons hΔ wfF) hLiftFσ)))
      rel₀ hLog₀ (hPiH_u hΔ hσ).red hEq₀⟩

/-- Validity of non-dependent function types `F ▹▹ G` (`▹▹ᵛ`). -/
theorem arrValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l Γ G) :
    ValidType eqrel l Γ (arr F G) :=
  piValid hF (wk1Valid hG)

/-- Validity of non-dependent function type congruence (`▹▹-congᵛ`). -/
theorem arrCongValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F F' G G' : Term}
    (hF : ValidType eqrel l Γ F)
    (hF' : ValidType eqrel l Γ F')
    (hFF' : ValidTypeEq hF F')
    (hG : ValidType eqrel l Γ G)
    (hG' : ValidType eqrel l Γ G')
    (hGG' : ValidTypeEq hG G') :
    ValidTypeEq (arrValid hF hG) (arr F' G') :=
  piCongValid hF (wk1Valid hG) hF' (wk1Valid hG') hFF' (wk1ValidEq hG hGG')

/-!
## Application Introductions (`Definition/LogicalRelation/Substitution/Introductions/Application.agda`)
-/

/-- Application of valid terms (`appᵛ`). -/
theorem appValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t u : Term}
    (hF : ValidType eqrel l Γ F)
    (hPi : ValidType eqrel l Γ (.pi F G))
    (ht : ValidTerm hPi t)
    (hu : ValidTerm hF u) :
    ValidTerm (substSPi hF hPi hu) (.app t u) := by
  intro Δ σ hΔ hσ
  have hGu : ValidType eqrel l Γ (subst0 G u) := substSPi hF hPi hu
  have pF := (hF hΔ hσ).red
  have pPi := (hPi hΔ hσ).red
  have pt := (ht hΔ hσ).term
  have pu := (hu hΔ hσ).term
  have pGu := (hGu hΔ hσ).red
  have pGu' : RedType eqrel l Δ (subst0 (subst (liftSubst σ) G) (subst σ u)) :=
    irrelevance' (singleSubstLift G u) pGu
  refine ⟨irrelevanceTerm' (singleSubstLift G u).symm pGu' pGu (appTerm pF pGu' pPi pt pu),
    fun {σ'} hσ' hσσ' ↦ ?_⟩
  have pu' : RedTerm pF (subst σ' u) :=
    convTerm₂ pF (hF hΔ hσ').red ((hF hΔ hσ).eq hσ' hσσ') (hu hΔ hσ').term
  exact irrelevanceEqTerm' (singleSubstLift G u).symm pGu' pGu
    (appCongTerm pF pGu' pPi ((ht hΔ hσ).eq hσ' hσσ') pu pu' ((hu hΔ hσ).eq hσ' hσσ'))

/-- Application congruence of valid terms (`app-congᵛ`). -/
theorem appCongValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t u a b : Term}
    (hF : ValidType eqrel l Γ F)
    (hPi : ValidType eqrel l Γ (.pi F G))
    (htu : ValidTermEq hPi t u)
    (ha : ValidTerm hF a)
    (hb : ValidTerm hF b)
    (hab : ValidTermEq hF a b) :
    ValidTermEq (substSPi hF hPi ha) (.app t a) (.app u b) := by
  intro Δ σ hΔ hσ
  have hGa : ValidType eqrel l Γ (subst0 G a) := substSPi hF hPi ha
  have pF := (hF hΔ hσ).red
  have pGa := (hGa hΔ hσ).red
  have pGa' : RedType eqrel l Δ (subst0 (subst (liftSubst σ) G) (subst σ a)) :=
    irrelevance' (singleSubstLift G a) pGa
  have pPi := (hPi hΔ hσ).red
  have pa := (ha hΔ hσ).term
  exact irrelevanceEqTerm' (singleSubstLift G a).symm pGa' pGa
    (appCongTerm pF pGa' pPi (htu hΔ hσ) pa (hb hΔ hσ).term (hab hΔ hσ))

/-!
## `Σ`-Type Introductions (`Definition/LogicalRelation/Substitution/Introductions/Pi.agda`)
-/

/-- Validity of `Σ F ▹ G` (`Σᵛ`). -/
theorem sigmaValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G) :
    ValidType eqrel l Γ (.sigma F G) := by
  intro Δ σ hΔ hσ
  have pσF := (hF hΔ hσ).red
  have wfF : TypeWf Δ (subst σ F) := escape pσF
  have pσG := (hG (.cons hΔ wfF) (liftSubstS hΔ hF hσ)).red
  have wfG : TypeWf (subst σ F :: Δ) (subst (liftSubst σ) G) := escape pσG
  have wfSigma : TypeWf Δ (.sigma (subst σ F) (subst (liftSubst σ) G)) := .sigma wfF wfG
  have hSigmaEq : eqrel.TypeEqRel Δ (.sigma (subst σ F) (subst (liftSubst σ) G))
      (.sigma (subst σ F) (subst (liftSubst σ) G)) :=
    eqrel.sigmaCong wfF (escapeEq pσF (reflEq pσF)) (escapeEq pσG (reflEq pσG))
  let relF : Wk → Context → RedRel → Prop :=
    fun ρ Δ₁ rel ↦ LogRelAt eqrel l Δ₁ (wk ρ (subst σ F)) rel
  let relG : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ₁ a rel ↦ LogRelAt eqrel l Δ₁ (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) a) rel
  have pF_wk : ∀ {ρ Δ₁}, WkCtx ρ Δ₁ Δ → CtxWf Δ₁ → RedType eqrel l Δ₁ (wk ρ (subst σ F)) :=
    fun hρ hΔ₁ ↦ wkRed hρ hΔ₁ pσF
  have pG_wk : ∀ {ρ Δ₁ a} (hρ : WkCtx ρ Δ₁ Δ) (hΔ₁ : CtxWf Δ₁),
      RedTerm (pF_wk hρ hΔ₁) a →
      RedType eqrel l Δ₁ (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) a) := by
    intro ρ Δ₁ a hρ hΔ₁ ha
    have hρσ : ValidSubst eqrel Δ₁ (wkSubst ρ σ) Γ := wkSubstS hρ hΔ₁ hσ
    have ha' : RedTerm (hF hΔ₁ hρσ).red a :=
      irrelevanceTerm' (wk_subst F) (pF_wk hρ hΔ₁) (hF hΔ₁ hρσ).red ha
    have hρσa : ValidSubst eqrel Δ₁ (consSubst (wkSubst ρ σ) a) (F :: Γ) :=
      consSubstS hΔ₁ hρσ hF ha'
    exact irrelevance' (singleSubstWkComp a σ G).symm (hG hΔ₁ hρσa).red
  have hGext : ∀ {ρ Δ₁ a b} (hρ : WkCtx ρ Δ₁ Δ) (hΔ₁ : CtxWf Δ₁)
      (ha : RedTerm (pF_wk hρ hΔ₁) a) (hb : RedTerm (pF_wk hρ hΔ₁) b),
      RedTermEq (pF_wk hρ hΔ₁) a b →
      RedEq (pG_wk hρ hΔ₁ ha) (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) b) := by
    intro ρ Δ₁ a b hρ hΔ₁ ha hb hab
    have hρσ : ValidSubst eqrel Δ₁ (wkSubst ρ σ) Γ := wkSubstS hρ hΔ₁ hσ
    have ha' : RedTerm (hF hΔ₁ hρσ).red a :=
      irrelevanceTerm' (wk_subst F) (pF_wk hρ hΔ₁) (hF hΔ₁ hρσ).red ha
    have hb' : RedTerm (hF hΔ₁ hρσ).red b :=
      irrelevanceTerm' (wk_subst F) (pF_wk hρ hΔ₁) (hF hΔ₁ hρσ).red hb
    have hab' : RedTermEq (hF hΔ₁ hρσ).red a b :=
      irrelevanceEqTerm' (wk_subst F) (pF_wk hρ hΔ₁) (hF hΔ₁ hρσ).red hab
    have hρσa : ValidSubst eqrel Δ₁ (consSubst (wkSubst ρ σ) a) (F :: Γ) :=
      consSubstS hΔ₁ hρσ hF ha'
    have hρσb : ValidSubst eqrel Δ₁ (consSubst (wkSubst ρ σ) b) (F :: Γ) :=
      consSubstS hΔ₁ hρσ hF hb'
    have hρσab : ValidSubstEq eqrel Δ₁ (consSubst (wkSubst ρ σ) a) (consSubst (wkSubst ρ σ) b) (F :: Γ) :=
      ValidSubstEq.cons (reflSubst hρσ) (hF hΔ₁ hρσ).red hab'
    exact irrelevanceEq'' (singleSubstWkComp a σ G).symm (singleSubstWkComp b σ G).symm
      (hG hΔ₁ hρσa).red (pG_wk hρ hΔ₁ ha)
      ((hG hΔ₁ hρσa).eq hρσb hρσab)
  have hLogSigma : LogRelAt eqrel l Δ (.sigma (subst σ F) (subst (liftSubst σ) G))
      (RedSigmaRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF relG) :=
    .sigma (idRedWf wfSigma) wfF wfG hSigmaEq relF relG
      (fun hρ hΔ₁ ↦ pF_wk hρ hΔ₁)
      (fun _ _ _ hr ↦ hr)
      (fun hρ hΔ₁ ha ↦ pG_wk hρ hΔ₁ ha)
      (fun _ _ _ _ hs ↦ hs)
      (fun hρ hΔ₁ ha hb hab ↦ hGext hρ hΔ₁ ha hb hab)
  refine ⟨⟨RedSigmaRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF relG, hLogSigma⟩,
    fun {σ'} hσ' hσσ' ↦ ?_⟩
  have pσ'F := (hF hΔ hσ').red
  have wfF' : TypeWf Δ (subst σ' F) := escape pσ'F
  have pσ'G := (hG (.cons hΔ wfF') (liftSubstS hΔ hF hσ')).red
  have wfG' : TypeWf (subst σ' F :: Δ) (subst (liftSubst σ') G) := escape pσ'G
  have wfSigma' : TypeWf Δ (.sigma (subst σ' F) (subst (liftSubst σ') G)) := .sigma wfF' wfG'
  have wfΔF : CtxWf (subst σ F :: Δ) := .cons hΔ wfF
  have hwk1σ := wk1SubstS hΔ wfF hσ
  have hwk1σ' := wk1SubstS hΔ wfF hσ'
  have hwk1σσ' := wk1SubstSEq hΔ wfF hσσ'
  have pF_wk1σ := (hF wfΔF hwk1σ).red
  have pF_wk1σ' := (hF wfΔF hwk1σ').red
  have hLookup0 : Member 0 (subst (wk1Subst σ) F) (subst σ F :: Δ) :=
    member_here_wk1Subst σ F Δ
  have var0 : HasType (subst σ F :: Δ) (.var 0) (subst (wk1Subst σ) F) :=
    .var wfΔF hLookup0
  have var0' : HasType (subst σ F :: Δ) (.var 0) (subst (wk1Subst σ') F) :=
    .conv var0 (eqrel.typeToEq (escapeEq pF_wk1σ ((hF wfΔF hwk1σ).eq hwk1σ' hwk1σσ')))
  have hLiftσ'_in_ΔF : ValidSubst eqrel (subst σ F :: Δ) (liftSubst σ') (F :: Γ) :=
    ValidSubst.cons hwk1σ' pF_wk1σ'
      (neuTerm pF_wk1σ' (.var 0) var0' (eqrel.varRefl var0'))
  have hLiftσσ'_in_ΔF : ValidSubstEq eqrel (subst σ F :: Δ) (liftSubst σ) (liftSubst σ') (F :: Γ) :=
    ValidSubstEq.cons hwk1σσ' pF_wk1σ
      (neuEqTerm pF_wk1σ (.var 0) (.var 0) var0 var0 (eqrel.varRefl var0))
  have hSigmaEq_σσ' : eqrel.TypeEqRel Δ (.sigma (subst σ F) (subst (liftSubst σ) G))
      (.sigma (subst σ' F) (subst (liftSubst σ') G)) :=
    eqrel.sigmaCong wfF
      (escapeEq pσF ((hF hΔ hσ).eq hσ' hσσ'))
      (escapeEq pσG ((hG wfΔF (liftSubstS hΔ hF hσ)).eq hLiftσ'_in_ΔF hLiftσσ'_in_ΔF))
  refine ⟨RedSigmaRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF relG, hLogSigma,
    .mk (subst σ' F) (subst (liftSubst σ') G) (.refl wfSigma') hSigmaEq_σσ'
      (fun hρ hΔ₁ ↦ wkRedEq hρ hΔ₁ pσF ((hF hΔ hσ).eq hσ' hσσ'))
      (fun {ρ Δ₁ a} hρ hΔ₁ ha ↦ ?_)⟩
  have hρσ : ValidSubst eqrel Δ₁ (wkSubst ρ σ) Γ := wkSubstS hρ hΔ₁ hσ
  have hρσ' : ValidSubst eqrel Δ₁ (wkSubst ρ σ') Γ := wkSubstS hρ hΔ₁ hσ'
  have hρσσ' : ValidSubstEq eqrel Δ₁ (wkSubst ρ σ) (wkSubst ρ σ') Γ :=
    wkSubstSEq hρ hΔ₁ hσσ'
  have ha' : RedTerm (hF hΔ₁ hρσ).red a :=
    irrelevanceTerm' (wk_subst F) (pF_wk hρ hΔ₁) (hF hΔ₁ hρσ).red ha
  have ha'' : RedTerm (hF hΔ₁ hρσ').red a :=
    convTerm₁ (hF hΔ₁ hρσ).red (hF hΔ₁ hρσ').red ((hF hΔ₁ hρσ).eq hρσ' hρσσ') ha'
  have hρσa : ValidSubst eqrel Δ₁ (consSubst (wkSubst ρ σ) a) (F :: Γ) :=
    consSubstS hΔ₁ hρσ hF ha'
  have hρσ'a : ValidSubst eqrel Δ₁ (consSubst (wkSubst ρ σ') a) (F :: Γ) :=
    consSubstS hΔ₁ hρσ' hF ha''
  have hρσa_eq : ValidSubstEq eqrel Δ₁ (consSubst (wkSubst ρ σ) a) (consSubst (wkSubst ρ σ') a) (F :: Γ) :=
    consSubstSEq hΔ₁ hρσ hρσσ' hF ha'
  exact irrelevanceEq'' (singleSubstWkComp a σ G).symm (singleSubstWkComp a σ' G).symm
    (hG hΔ₁ hρσa).red (pG_wk hρ hΔ₁ ha)
    ((hG hΔ₁ hρσa).eq hρσ'a hρσa_eq)

/-- Validity of `Σ`-congruence (`Σ-congᵛ`). -/
theorem sigmaCongValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G H E : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (hH : ValidType eqrel l Γ H)
    (hE : ValidType eqrel l (H :: Γ) E)
    (hFH : ValidTypeEq hF H)
    (hGE : ValidTypeEq hG E) :
    ValidTypeEq (sigmaValid hF hG) (.sigma H E) := by
  intro Δ σ hΔ hσ
  have hSigmaValid : ValidType eqrel l Γ (.sigma F G) := sigmaValid hF hG
  have pSigmaFG := (hSigmaValid hΔ hσ).red
  rcases elimSigmaAt' (.refl (escape pSigmaFG)) pSigmaFG with ⟨l₀, sigmaA⟩
  have pσF := (hF hΔ hσ).red
  have wfσF : TypeWf Δ (subst σ F) := escape pσF
  have pσG := (hG (.cons hΔ wfσF) (liftSubstS hΔ hF hσ)).red
  have wfσH : TypeWf Δ (subst σ H) := escape (hH hΔ hσ).red
  have wfσE : TypeWf (subst σ H :: Δ) (subst (liftSubst σ) E) :=
    escape (hE (.cons hΔ wfσH) (liftSubstS hΔ hH hσ)).red
  have hσFH : eqrel.TypeEqRel Δ (subst σ F) (subst σ H) :=
    escapeEq pσF (hFH hΔ hσ)
  have hσGE : eqrel.TypeEqRel (subst σ F :: Δ) (subst (liftSubst σ) G) (subst (liftSubst σ) E) :=
    escapeEq pσG (hGE (.cons hΔ wfσF) (liftSubstS hΔ hF hσ))
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ₁ rel ↦ LogRelAt eqrel l₀ Δ₁ (wk ρ (subst σ F)) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ₁ a rel ↦ LogRelAt eqrel l₀ Δ₁ (subst0 (wk (.lift ρ) (subst (liftSubst σ) G)) a) rel
  have hLogSigma₀ : LogRelAt eqrel l₀ Δ (.sigma (subst σ F) (subst (liftSubst σ) G))
      (RedSigmaRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀) :=
    .sigma sigmaA.D sigmaA.hF sigmaA.hG sigmaA.AeqA relF₀ relG₀
      sigmaA.redF (fun _ _ _ h ↦ h) sigmaA.redG (fun _ _ _ _ h ↦ h) sigmaA.Gext
  have pSigmaFG₀ : RedType eqrel l₀ Δ (.sigma (subst σ F) (subst (liftSubst σ) G)) :=
    ⟨RedSigmaRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀, hLogSigma₀⟩
  have hRes₀ : RedEq pSigmaFG₀ (.sigma (subst σ H) (subst (liftSubst σ) E)) := by
    refine ⟨RedSigmaRel eqrel Δ (subst σ F) (subst (liftSubst σ) G) relF₀ relG₀, hLogSigma₀,
      .mk (subst σ H) (subst (liftSubst σ) E) (.refl (.sigma wfσH wfσE))
        (eqrel.sigmaCong wfσF hσFH hσGE)
        (fun {ρ Δ₁} hρ hΔ₁ ↦ ?_)
        (fun {ρ Δ₁ a} hρ hΔ₁ ha ↦ ?_)⟩
    · have hρσ := wkSubstS hρ hΔ₁ hσ
      exact irrelevanceEq'' (wk_subst F).symm (wk_subst H).symm
        (hF hΔ₁ hρσ).red (sigmaA.redF hρ hΔ₁) (hFH hΔ₁ hρσ)
    · have hρσ := wkSubstS hρ hΔ₁ hσ
      have ha' : RedTerm (hF hΔ₁ hρσ).red a :=
        irrelevanceTerm' (wk_subst F) (sigmaA.redF hρ hΔ₁) (hF hΔ₁ hρσ).red ha
      have hρσa := consSubstS hΔ₁ hρσ hF ha'
      exact irrelevanceEq'' (singleSubstWkComp a σ G).symm (singleSubstWkComp a σ E).symm
        (hG hΔ₁ hρσa).red (sigmaA.redG hρ hΔ₁ ha) (hGE hΔ₁ hρσa)
  exact irrelevanceEq pSigmaFG₀ pSigmaFG hRes₀

/-- Validity of `Σ F ▹ G` as a term of `U` (`Σᵗᵛ`). -/
theorem sigmaTermValid {eqrel : EqRelSet} {Γ : Context} {F G : Term}
    (hF : ValidType eqrel .one Γ F)
    (hU : ValidType eqrel .one (F :: Γ) .univ)
    (hFt : ValidTerm (UValid (eqrel := eqrel) (Γ := Γ)) F)
    (hGt : ValidTerm hU G) :
    ValidTerm (UValid (eqrel := eqrel) (Γ := Γ)) (.sigma F G) := by
  intro Δ σ hΔ hσ
  have hLiftσ := liftSubstS hΔ hF hσ
  have wfF : TypeWf Δ (subst σ F) := escape (hF hΔ hσ).red
  have pUΔ : RedType eqrel .one Δ .univ := redUOne hΔ
  have wfFt : HasType Δ (subst σ F) .univ := escapeTerm pUΔ (hFt hΔ hσ).term
  have hFFt : eqrel.TermEqRel Δ (subst σ F) (subst σ F) .univ :=
    escapeTermEq pUΔ (reflEqTerm pUΔ (hFt hΔ hσ).term)
  have pU_ΔF := (hU (.cons hΔ wfF) hLiftσ).red
  have wfGt : HasType (subst σ F :: Δ) (subst (liftSubst σ) G) .univ :=
    escapeTerm pU_ΔF (hGt (.cons hΔ wfF) hLiftσ).term
  have hGGt : eqrel.TermEqRel (subst σ F :: Δ) (subst (liftSubst σ) G) (subst (liftSubst σ) G) .univ :=
    escapeTermEq pU_ΔF (reflEqTerm pU_ΔF (hGt (.cons hΔ wfF) hLiftσ).term)
  have hF₀ : ValidType eqrel .zero Γ F := univValid UValid hFt
  have hG₀ : ValidType eqrel .zero (F :: Γ) G := univValid hU hGt
  have hSigma₀Valid : ValidType eqrel .zero Γ (.sigma F G) := sigmaValid hF₀ hG₀
  have hSigmaFG₀ := hSigma₀Valid hΔ hσ
  have wfSigmat : HasType Δ (.sigma (subst σ F) (subst (liftSubst σ) G)) .univ :=
    .sigma wfFt wfGt
  rcases hSigmaFG₀.red with ⟨relSigma₀, hLogSigma₀⟩
  refine ⟨⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩,
      .mk (.sigma (subst σ F) (subst (liftSubst σ) G)) (idRedTermWf wfSigmat)
        .sigma (eqrel.sigmaTermCong wfF hFFt hGGt) ⟨relSigma₀, hLogSigma₀⟩⟩,
    fun {σ'} hσ' hσσ' ↦ ?_⟩
  have hLiftσ' := liftSubstS hΔ hF hσ'
  have hwk1σ := wk1SubstS hΔ wfF hσ
  have hwk1σ' := wk1SubstS hΔ wfF hσ'
  have wfΔF : CtxWf (subst σ F :: Δ) := .cons hΔ wfF
  have hLookup0 : Member 0 (subst (wk1Subst σ) F) (subst σ F :: Δ) :=
    member_here_wk1Subst σ F Δ
  have var0 : HasType (subst σ F :: Δ) (.var 0) (subst (wk1Subst σ) F) :=
    .var wfΔF hLookup0
  have var0' : HasType (subst σ F :: Δ) (.var 0) (subst (wk1Subst σ') F) :=
    .conv var0 (eqrel.typeToEq (escapeEq (hF wfΔF hwk1σ).red
      ((hF wfΔF hwk1σ).eq hwk1σ' (wk1SubstSEq hΔ wfF hσσ'))))
  have hLiftσ'_in_ΔF : ValidSubst eqrel (subst σ F :: Δ) (liftSubst σ') (F :: Γ) :=
    ValidSubst.cons hwk1σ' (hF wfΔF hwk1σ').red
      (neuTerm (hF wfΔF hwk1σ').red (.var 0) var0' (eqrel.varRefl var0'))
  have wfF' : TypeWf Δ (subst σ' F) := escape (hF hΔ hσ').red
  have wfFt' : HasType Δ (subst σ' F) .univ := escapeTerm pUΔ (hFt hΔ hσ').term
  have wfGt' : HasType (subst σ' F :: Δ) (subst (liftSubst σ') G) .univ :=
    escapeTerm (hU (.cons hΔ wfF') hLiftσ').red (hGt (.cons hΔ wfF') hLiftσ').term
  have hFF't : eqrel.TermEqRel Δ (subst σ F) (subst σ' F) .univ :=
    escapeTermEq pUΔ ((hFt hΔ hσ).eq hσ' hσσ')
  have hGG't : eqrel.TermEqRel (subst σ F :: Δ) (subst (liftSubst σ) G) (subst (liftSubst σ') G) .univ :=
    escapeTermEq pU_ΔF ((hGt wfΔF hLiftσ).eq hLiftσ'_in_ΔF (liftSubstSEq hΔ hF hσ hσσ'))
  have hSigmaFG₀' := hSigma₀Valid hΔ hσ'
  have hSigmaEq₀ := hSigmaFG₀.eq hσ' hσσ'
  rcases hSigmaEq₀ with ⟨rel₀, hLog₀, hEq₀⟩
  exact ⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩,
    .mk (.sigma (subst σ F) (subst (liftSubst σ) G))
      (.sigma (subst σ' F) (subst (liftSubst σ') G))
      (idRedTermWf wfSigmat) (idRedTermWf (.sigma wfFt' wfGt'))
      .sigma .sigma (eqrel.sigmaTermCong wfF hFF't hGG't)
      rel₀ hLog₀ hSigmaFG₀'.red hEq₀⟩

/-- Validity of `Σ`-congruence as a term equality in `U` (`Σ-congᵗᵛ`). -/
theorem sigmaCongTermValid {eqrel : EqRelSet} {Γ : Context} {F G H E : Term}
    (hF : ValidType eqrel .one Γ F)
    (hH : ValidType eqrel .one Γ H)
    (hUF : ValidType eqrel .one (F :: Γ) .univ)
    (hUH : ValidType eqrel .one (H :: Γ) .univ)
    (hFt : ValidTerm (UValid (eqrel := eqrel) (Γ := Γ)) F)
    (hGt : ValidTerm hUF G)
    (hHt : ValidTerm (UValid (eqrel := eqrel) (Γ := Γ)) H)
    (hEt : ValidTerm hUH E)
    (hFHt : ValidTermEq (UValid (eqrel := eqrel) (Γ := Γ)) F H)
    (hGEt : ValidTermEq hUF G E) :
    ValidTermEq (UValid (eqrel := eqrel) (Γ := Γ)) (.sigma F G) (.sigma H E) := by
  intro Δ σ hΔ hσ
  have wfF : TypeWf Δ (subst σ F) := escape (hF hΔ hσ).red
  have wfH : TypeWf Δ (subst σ H) := escape (hH hΔ hσ).red
  have hLiftFσ := liftSubstS hΔ hF hσ
  have hLiftHσ := liftSubstS hΔ hH hσ
  have hF_u : ValidType eqrel .zero Γ F := univValid UValid hFt
  have hG_u : ValidType eqrel .zero (F :: Γ) G := univValid hUF hGt
  have hH_u : ValidType eqrel .zero Γ H := univValid UValid hHt
  have hE_u : ValidType eqrel .zero (H :: Γ) E := univValid hUH hEt
  have hFH_u : ValidTypeEq hF_u H := univEqValid UValid hF_u hFHt
  have hGE_u : ValidTypeEq hG_u E := univEqValid hUF hG_u hGEt
  have pUΔ : RedType eqrel .one Δ .univ := redUOne hΔ
  have wfSigmaFG : HasType Δ (.sigma (subst σ F) (subst (liftSubst σ) G)) .univ :=
    .sigma (escapeTerm pUΔ (hFt hΔ hσ).term)
      (escapeTerm (hUF (.cons hΔ wfF) hLiftFσ).red (hGt (.cons hΔ wfF) hLiftFσ).term)
  have wfSigmaHE : HasType Δ (.sigma (subst σ H) (subst (liftSubst σ) E)) .univ :=
    .sigma (escapeTerm pUΔ (hHt hΔ hσ).term)
      (escapeTerm (hUH (.cons hΔ wfH) hLiftHσ).red (hEt (.cons hΔ wfH) hLiftHσ).term)
  have hSigmaEq₀ := sigmaCongValid hF_u hG_u hH_u hE_u hFH_u hGE_u hΔ hσ
  rcases hSigmaEq₀ with ⟨rel₀, hLog₀, hEq₀⟩
  have hSigmaH_u : ValidType eqrel .zero Γ (.sigma H E) := sigmaValid hH_u hE_u
  exact ⟨RedURel eqrel (logRelRec eqrel .one .zero .zeroLT) Δ, .U ⟨.zeroLT, hΔ⟩,
    .mk (.sigma (subst σ F) (subst (liftSubst σ) G))
      (.sigma (subst σ H) (subst (liftSubst σ) E))
      (idRedTermWf wfSigmaFG) (idRedTermWf wfSigmaHE)
      .sigma .sigma
      (eqrel.sigmaTermCong wfF
        (escapeTermEq pUΔ (hFHt hΔ hσ))
        (escapeTermEq (hUF (.cons hΔ wfF) hLiftFσ).red (hGEt (.cons hΔ wfF) hLiftFσ)))
      rel₀ hLog₀ (hSigmaH_u hΔ hσ).red hEq₀⟩

/-!
## First Projection Introductions (`Definition/LogicalRelation/Substitution/Introductions/Fst.agda`)
-/

/-- Reducibility of `fst` (`fst″`). -/
theorem fstTerm {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {F G t : Term}
    (pF : RedType eqrel l' Γ F)
    (pSigma : RedType eqrel l Γ (.sigma F G))
    (pt : RedTerm pSigma t) :
    RedTerm pF (.fst t) := by
  rcases elimSigmaAt' (.refl (escape pSigma)) pSigma with ⟨l₀, sigmaA⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ rel ↦ LogRelAt eqrel l₀ Δ (wk ρ F) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ a rel ↦ LogRelAt eqrel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel
  have hAt : LogRelAt eqrel l₀ Γ (.sigma F G) (RedSigmaRel eqrel Γ F G relF₀ relG₀) :=
    .sigma sigmaA.D sigmaA.hF sigmaA.hG sigmaA.AeqA relF₀ relG₀
      sigmaA.redF (fun _ _ _ h ↦ h) sigmaA.redG (fun _ _ _ _ h ↦ h) sigmaA.Gext
  have pSigma₀ : RedType eqrel l₀ Γ (.sigma F G) := ⟨_, hAt⟩
  have ht₀ : RedSigmaTerm eqrel Γ F G relF₀ relG₀ t :=
    (RedTerm_of_LogRelAt hAt pSigma₀).mp (irrelevanceTerm pSigma pSigma₀ pt)
  rcases ht₀ with ⟨p, d, _, _, hfstp, _⟩
  have wfΓ : CtxWf Γ := wfType sigmaA.hF
  have pF_id : RedType eqrel l₀ Γ (wk .id F) := sigmaA.redF .id wfΓ
  have hfstp' : RedTerm pF (.fst p) := irrelevanceTerm' (wk_id F) pF_id pF hfstp
  exact (redSubstStarTerm (Star.fst sigmaA.hF sigmaA.hG d.reduction) pF hfstp').1

/-- Reducibility of `fst` congruence (`fst-cong″`). -/
theorem fstCongTerm {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {F G t t' : Term}
    (pF : RedType eqrel l' Γ F)
    (pSigma : RedType eqrel l Γ (.sigma F G))
    (ptt' : RedTermEq pSigma t t') :
    RedTermEq pF (.fst t) (.fst t') := by
  rcases elimSigmaAt' (.refl (escape pSigma)) pSigma with ⟨l₀, sigmaA⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ rel ↦ LogRelAt eqrel l₀ Δ (wk ρ F) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ a rel ↦ LogRelAt eqrel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel
  have hAt : LogRelAt eqrel l₀ Γ (.sigma F G) (RedSigmaRel eqrel Γ F G relF₀ relG₀) :=
    .sigma sigmaA.D sigmaA.hF sigmaA.hG sigmaA.AeqA relF₀ relG₀
      sigmaA.redF (fun _ _ _ h ↦ h) sigmaA.redG (fun _ _ _ _ h ↦ h) sigmaA.Gext
  have pSigma₀ : RedType eqrel l₀ Γ (.sigma F G) := ⟨_, hAt⟩
  have htt'₀ : RedSigmaTermEq eqrel Γ F G relF₀ relG₀ t t' :=
    (RedTermEq_of_LogRelAt hAt pSigma₀).mp (irrelevanceEqTerm pSigma pSigma₀ ptt')
  rcases htt'₀ with ⟨p, p', d, d', _, _, _, _, _, hfstp, hfstp', hfstEq, _⟩
  have wfΓ : CtxWf Γ := wfType sigmaA.hF
  have pF_id : RedType eqrel l₀ Γ (wk .id F) := sigmaA.redF .id wfΓ
  have hfstp₁ : RedTerm pF (.fst p) := irrelevanceTerm' (wk_id F) pF_id pF hfstp
  have hfstp'₁ : RedTerm pF (.fst p') := irrelevanceTerm' (wk_id F) pF_id pF hfstp'
  have hfstEq₁ : RedTermEq pF (.fst p) (.fst p') :=
    irrelevanceEqTerm' (wk_id F) pF_id pF hfstEq
  have hfstt_p : RedTermEq pF (.fst t) (.fst p) :=
    (redSubstStarTerm (Star.fst sigmaA.hF sigmaA.hG d.reduction) pF hfstp₁).2
  have hfstt'_p' : RedTermEq pF (.fst t') (.fst p') :=
    (redSubstStarTerm (Star.fst sigmaA.hF sigmaA.hG d'.reduction) pF hfstp'₁).2
  exact transEqTerm pF hfstt_p (transEqTerm pF hfstEq₁ (symEqTerm pF hfstt'_p'))

/-- Validity of `fst` (`fstᵛ`). -/
theorem fstValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (ht : ValidTerm (sigmaValid hF hG) t) :
    ValidTerm hF (.fst t) := by
  intro Δ σ hΔ hσ
  have hSigma : ValidType eqrel l Γ (.sigma F G) := sigmaValid hF hG
  refine ⟨fstTerm (hF hΔ hσ).red (hSigma hΔ hσ).red (ht hΔ hσ).term,
    fun {σ'} hσ' hσσ' ↦ fstCongTerm (hF hΔ hσ).red (hSigma hΔ hσ).red ((ht hΔ hσ).eq hσ' hσσ')⟩

/-- Validity of `fst` congruence (`fst-congᵛ`). -/
theorem fstCongValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t t' : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (_ht : ValidTerm (sigmaValid hF hG) t)
    (_ht' : ValidTerm (sigmaValid hF hG) t')
    (htt' : ValidTermEq (sigmaValid hF hG) t t') :
    ValidTermEq hF (.fst t) (.fst t') := by
  intro Δ σ hΔ hσ
  have hSigma : ValidType eqrel l Γ (.sigma F G) := sigmaValid hF hG
  exact fstCongTerm (hF hΔ hσ).red (hSigma hΔ hσ).red (htt' hΔ hσ)

/-!
## Second Projection Introductions (`Definition/LogicalRelation/Substitution/Introductions/Snd.agda`)
-/

/-- Multi-step reduction congruence for `snd` (`snd-subst*`). -/
theorem sndSubstStar {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {F G t t'' : Term}
    (pF : RedType eqrel l Γ F)
    (pSigma : RedType eqrel l' Γ (.sigma F G))
    (pt'' : RedTerm pSigma t'')
    (d : Star Γ t t'' (.sigma F G)) :
    Star Γ (.snd t) (.snd t'') (subst0 G (.fst t)) := by
  rcases elimSigmaAt' (.refl (escape pSigma)) pSigma with ⟨l₀, sigmaA⟩
  generalize hs : Term.sigma F G = S at d
  induction d with
  | refl ht =>
      subst hs
      exact .refl (.snd sigmaA.hF sigmaA.hG ht)
  | @step _ t₀ t₁ t'' hStep dRest ih =>
      subst hs
      have dFull : Star Γ t₀ t'' (.sigma F G) := .step hStep dRest
      have pt₀ : RedTerm pSigma t₀ := (redSubstStarTerm dFull pSigma pt'').1
      have pt₁ : RedTerm pSigma t₁ := (redSubstStarTerm dRest pSigma pt'').1
      have pt₀t₁ : RedTermEq pSigma t₀ t₁ := (redSubstTerm hStep pSigma pt₁).2
      have hfstt₀ : RedTerm pF (.fst t₀) := fstTerm pF pSigma pt₀
      have hfstt₁ : RedTerm pF (.fst t₁) := fstTerm pF pSigma pt₁
      have pGfstt₀ : RedType eqrel l' Γ (subst0 G (.fst t₀)) := substSSigma₁ pSigma pF hfstt₀
      have pGfstt₁ : RedType eqrel l' Γ (subst0 G (.fst t₁)) := substSSigma₁ pSigma pF hfstt₁
      have hfstt₁t₀ : RedTermEq pF (.fst t₁) (.fst t₀) :=
        symEqTerm pF (fstCongTerm pF pSigma pt₀t₁)
      have hGfstEq : RedEq pGfstt₁ (subst0 G (.fst t₀)) :=
        substSSigma₂ pSigma (reflEq pSigma) pF pF hfstt₁ hfstt₀ hfstt₁t₀ pGfstt₁ pGfstt₀
      exact .step (.snd sigmaA.hF sigmaA.hG hStep)
        ((ih pt'' rfl).conv (eqrel.typeToEq (escapeEq pGfstt₁ hGfstEq)))

/-- Reducibility of `snd` (`snd″`). -/
theorem sndTerm {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {F G t : Term}
    (pSigma : RedType eqrel l Γ (.sigma F G))
    (pt : RedTerm pSigma t)
    (pGfst : RedType eqrel l' Γ (subst0 G (.fst t))) :
    RedTerm pGfst (.snd t) := by
  rcases elimSigmaAt' (.refl (escape pSigma)) pSigma with ⟨l₀, sigmaA⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ rel ↦ LogRelAt eqrel l₀ Δ (wk ρ F) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ a rel ↦ LogRelAt eqrel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel
  have hAt : LogRelAt eqrel l₀ Γ (.sigma F G) (RedSigmaRel eqrel Γ F G relF₀ relG₀) :=
    .sigma sigmaA.D sigmaA.hF sigmaA.hG sigmaA.AeqA relF₀ relG₀
      sigmaA.redF (fun _ _ _ h ↦ h) sigmaA.redG (fun _ _ _ _ h ↦ h) sigmaA.Gext
  have pSigma₀ : RedType eqrel l₀ Γ (.sigma F G) := ⟨_, hAt⟩
  have ht₀ : RedSigmaTerm eqrel Γ F G relF₀ relG₀ t :=
    (RedTerm_of_LogRelAt hAt pSigma₀).mp (irrelevanceTerm pSigma pSigma₀ pt)
  rcases ht₀ with ⟨p, d, pProd, pEqp, hfstp, hsndp⟩
  have wfΓ : CtxWf Γ := wfType sigmaA.hF
  have pp₀ : RedTerm pSigma₀ p :=
    ⟨_, hAt, .mk p (idRedTermWf d.target) pProd pEqp hfstp hsndp⟩
  have pF_id : RedType eqrel l₀ Γ (wk .id F) := sigmaA.redF .id wfΓ
  have pF₀ : RedType eqrel l₀ Γ F := irrelevance' (wk_id F) pF_id
  have dFst_wk : Star Γ (.fst t) (.fst p) (wk .id F) := by
    rw [wk_id F]
    exact Star.fst sigmaA.hF sigmaA.hG d.reduction
  rcases redSubstStarTerm dFst_wk pF_id hfstp with ⟨hfstt, hfstt_p⟩
  have pGfstt : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) (.fst t)) :=
    sigmaA.redG .id wfΓ hfstt
  have pGfstp : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) (.fst p)) :=
    sigmaA.redG .id wfΓ hfstp
  have hGfstt_p : RedEq pGfstt (subst0 (wk (.lift .id) G) (.fst p)) :=
    sigmaA.Gext .id wfΓ hfstt hfstp hfstt_p
  have hsndp' : RedTerm pGfstt (.snd p) :=
    convTerm₂ pGfstt pGfstp hGfstt_p hsndp
  have hGeq : subst0 (wk (.lift .id) G) (.fst t) = subst0 G (.fst t) := by
    rw [wk_lift_id]
  have hsndp'' : RedTerm pGfst (.snd p) :=
    irrelevanceTerm' hGeq pGfstt pGfst hsndp'
  exact (redSubstStarTerm (sndSubstStar pF₀ pSigma₀ pp₀ d.reduction) pGfst hsndp'').1

/-- Reducibility of `snd` congruence (`snd-cong″`). -/
theorem sndCongTerm {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {F G t t' : Term}
    (pSigma : RedType eqrel l Γ (.sigma F G))
    (pt : RedTerm pSigma t)
    (pt' : RedTerm pSigma t')
    (ptt' : RedTermEq pSigma t t')
    (pGfst : RedType eqrel l' Γ (subst0 G (.fst t))) :
    RedTermEq pGfst (.snd t) (.snd t') := by
  rcases elimSigmaAt' (.refl (escape pSigma)) pSigma with ⟨l₀, sigmaA⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ rel ↦ LogRelAt eqrel l₀ Δ (wk ρ F) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ a rel ↦ LogRelAt eqrel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel
  have hAt : LogRelAt eqrel l₀ Γ (.sigma F G) (RedSigmaRel eqrel Γ F G relF₀ relG₀) :=
    .sigma sigmaA.D sigmaA.hF sigmaA.hG sigmaA.AeqA relF₀ relG₀
      sigmaA.redF (fun _ _ _ h ↦ h) sigmaA.redG (fun _ _ _ _ h ↦ h) sigmaA.Gext
  have pSigma₀ : RedType eqrel l₀ Γ (.sigma F G) := ⟨_, hAt⟩
  have ht₀ : RedSigmaTerm eqrel Γ F G relF₀ relG₀ t :=
    (RedTerm_of_LogRelAt hAt pSigma₀).mp (irrelevanceTerm pSigma pSigma₀ pt)
  have ht'₀ : RedSigmaTerm eqrel Γ F G relF₀ relG₀ t' :=
    (RedTerm_of_LogRelAt hAt pSigma₀).mp (irrelevanceTerm pSigma pSigma₀ pt')
  have htt'₀ : RedSigmaTermEq eqrel Γ F G relF₀ relG₀ t t' :=
    (RedTermEq_of_LogRelAt hAt pSigma₀).mp (irrelevanceEqTerm pSigma pSigma₀ ptt')
  rcases ht₀ with ⟨p, d, pProd, pEqp, hfstp, hsndp⟩
  rcases ht'₀ with ⟨p', d', pProd', pEqp', hfstp', hsndp'⟩
  rcases htt'₀ with ⟨p₁, p'₁, d₁, d'₁, pProd₁, pProd'₁, _, _, _, hfstp₁, _, hfstEq, hsndEq⟩
  have hp_eq : p = p₁ :=
    whrDetStarTerm ⟨d.reduction, pProd.toWhnf⟩ ⟨d₁.reduction, pProd₁.toWhnf⟩
  have hp'_eq : p' = p'₁ :=
    whrDetStarTerm ⟨d'.reduction, pProd'.toWhnf⟩ ⟨d'₁.reduction, pProd'₁.toWhnf⟩
  subst hp_eq hp'_eq
  have wfΓ : CtxWf Γ := wfType sigmaA.hF
  have pp₀ : RedTerm pSigma₀ p :=
    ⟨_, hAt, .mk p (idRedTermWf d.target) pProd pEqp hfstp hsndp⟩
  have pp'₀ : RedTerm pSigma₀ p' :=
    ⟨_, hAt, .mk p' (idRedTermWf d'.target) pProd' pEqp' hfstp' hsndp'⟩
  have pF_id : RedType eqrel l₀ Γ (wk .id F) := sigmaA.redF .id wfΓ
  have pF₀ : RedType eqrel l₀ Γ F := irrelevance' (wk_id F) pF_id
  have dFst_wk : Star Γ (.fst t) (.fst p) (wk .id F) := by
    rw [wk_id F]
    exact Star.fst sigmaA.hF sigmaA.hG d.reduction
  rcases redSubstStarTerm dFst_wk pF_id hfstp with ⟨hfstt, hfstt_p⟩
  have pGfstt : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) (.fst t)) :=
    sigmaA.redG .id wfΓ hfstt
  have pGfstp : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) (.fst p)) :=
    sigmaA.redG .id wfΓ hfstp
  have hGfstt_p : RedEq pGfstt (subst0 (wk (.lift .id) G) (.fst p)) :=
    sigmaA.Gext .id wfΓ hfstt hfstp hfstt_p
  have hGeq : subst0 (wk (.lift .id) G) (.fst t) = subst0 G (.fst t) := by
    rw [wk_lift_id]
  have hsndp₁ : RedTerm pGfstt (.snd p) :=
    convTerm₂ pGfstt pGfstp hGfstt_p hsndp
  have hsndp₂ : RedTerm pGfst (.snd p) :=
    irrelevanceTerm' hGeq pGfstt pGfst hsndp₁
  have hsndt_p : RedTermEq pGfst (.snd t) (.snd p) :=
    (redSubstStarTerm (sndSubstStar pF₀ pSigma₀ pp₀ d.reduction) pGfst hsndp₂).2
  have hsndEq₁ : RedTermEq pGfstt (.snd p) (.snd p') :=
    convEqTerm₂ pGfstt (sigmaA.redG .id wfΓ hfstp₁) hGfstt_p hsndEq
  have hsndp_p' : RedTermEq pGfst (.snd p) (.snd p') :=
    irrelevanceEqTerm' hGeq pGfstt pGfst hsndEq₁
  have dFst'_wk : Star Γ (.fst t') (.fst p') (wk .id F) := by
    rw [wk_id F]
    exact Star.fst sigmaA.hF sigmaA.hG d'.reduction
  rcases redSubstStarTerm dFst'_wk pF_id hfstp' with ⟨hfstt', hfstt'_p'⟩
  have hfstt_t' : RedTermEq pF_id (.fst t) (.fst t') :=
    irrelevanceEqTerm' (wk_id F).symm pF₀ pF_id
      (fstCongTerm pF₀ pSigma₀ ⟨_, hAt,
        .mk p p' d₁ d'₁ pProd₁ pProd'₁ ‹_› ‹_› ‹_› hfstp₁ ‹_› hfstEq hsndEq⟩)
  have hfstt_p' : RedTermEq pF_id (.fst t) (.fst p') :=
    transEqTerm pF_id hfstt_t' hfstt'_p'
  have pGfstp' : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) (.fst p')) :=
    sigmaA.redG .id wfΓ hfstp'
  have hGfstt_p' : RedEq pGfstt (subst0 (wk (.lift .id) G) (.fst p')) :=
    sigmaA.Gext .id wfΓ hfstt hfstp' hfstt_p'
  have hsndp'₁ : RedTerm pGfstt (.snd p') :=
    convTerm₂ pGfstt pGfstp' hGfstt_p' hsndp'
  have hsndp'₂ : RedTerm pGfst (.snd p') :=
    irrelevanceTerm' hGeq pGfstt pGfst hsndp'₁
  have pGfstt₀ : RedType eqrel l₀ Γ (subst0 G (.fst t)) :=
    irrelevance' hGeq pGfstt
  have hGeq' : subst0 (wk (.lift .id) G) (.fst t') = subst0 G (.fst t') := by
    rw [wk_lift_id]
  have hGfstt_t' : RedEq pGfstt₀ (subst0 G (.fst t')) :=
    irrelevanceEq'' hGeq hGeq' pGfstt pGfstt₀
      (sigmaA.Gext .id wfΓ hfstt hfstt' hfstt_t')
  have dSnd' : Star Γ (.snd t') (.snd p') (subst0 G (.fst t)) :=
    (sndSubstStar pF₀ pSigma₀ pp'₀ d'.reduction).conv
      (eqrel.typeToEq (eqrel.symmType (escapeEq pGfstt₀ hGfstt_t')))
  have hsndt'_p' : RedTermEq pGfst (.snd t') (.snd p') :=
    (redSubstStarTerm dSnd' pGfst hsndp'₂).2
  exact transEqTerm pGfst hsndt_p
    (transEqTerm pGfst hsndp_p' (symEqTerm pGfst hsndt'_p'))

/-- Validity of `snd` (`sndᵛ`). -/
theorem sndValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (ht : ValidTerm (sigmaValid hF hG) t) :
    ValidTerm (substS hF hG (fstValid hF hG ht)) (.snd t) := by
  intro Δ σ hΔ hσ
  have hSigma : ValidType eqrel l Γ (.sigma F G) := sigmaValid hF hG
  have hGfst : ValidType eqrel l Γ (subst0 G (.fst t)) := substS hF hG (fstValid hF hG ht)
  have pSigma := (hSigma hΔ hσ).red
  have pt := (ht hΔ hσ).term
  have pGfst := (hGfst hΔ hσ).red
  have pGfst' : RedType eqrel l Δ (subst0 (subst (liftSubst σ) G) (subst σ (.fst t))) :=
    irrelevance' (singleSubstLift G (.fst t)) pGfst
  refine ⟨irrelevanceTerm' (singleSubstLift G (.fst t)).symm pGfst' pGfst
      (sndTerm pSigma pt pGfst'),
    fun {σ'} hσ' hσσ' ↦ ?_⟩
  have pSigma' := (hSigma hΔ hσ').red
  have pSigmaEq := (hSigma hΔ hσ).eq hσ' hσσ'
  have pt' : RedTerm pSigma (subst σ' t) :=
    convTerm₂ pSigma pSigma' pSigmaEq (ht hΔ hσ').term
  exact irrelevanceEqTerm' (singleSubstLift G (.fst t)).symm pGfst' pGfst
    (sndCongTerm pSigma pt pt' ((ht hΔ hσ).eq hσ' hσσ') pGfst')

/-- Validity of `snd` congruence (`snd-congᵛ`). -/
theorem sndCongValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t t' : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (ht : ValidTerm (sigmaValid hF hG) t)
    (ht' : ValidTerm (sigmaValid hF hG) t')
    (htt' : ValidTermEq (sigmaValid hF hG) t t') :
    ValidTermEq (substS hF hG (fstValid hF hG ht)) (.snd t) (.snd t') := by
  intro Δ σ hΔ hσ
  have hSigma : ValidType eqrel l Γ (.sigma F G) := sigmaValid hF hG
  have hGfst : ValidType eqrel l Γ (subst0 G (.fst t)) := substS hF hG (fstValid hF hG ht)
  have pSigma := (hSigma hΔ hσ).red
  have pt := (ht hΔ hσ).term
  have pt' := (ht' hΔ hσ).term
  have pGfst := (hGfst hΔ hσ).red
  have pGfst' : RedType eqrel l Δ (subst0 (subst (liftSubst σ) G) (subst σ (.fst t))) :=
    irrelevance' (singleSubstLift G (.fst t)) pGfst
  exact irrelevanceEqTerm' (singleSubstLift G (.fst t)).symm pGfst' pGfst
    (sndCongTerm pSigma pt pt' (htt' hΔ hσ) pGfst')

/-!
## Product Term Introductions (`Definition/LogicalRelation/Substitution/Introductions/Prod.agda`)
-/

/-- Reducibility of `prod t u` (`prod″`). -/
theorem prodTerm {eqrel : EqRelSet} {l l' l'' : TypeLevel} {Γ : Context} {F G t u : Term}
    (pF : RedType eqrel l Γ F)
    (pt : RedTerm pF t)
    (pGt : RedType eqrel l'' Γ (subst0 G t))
    (pu : RedTerm pGt u)
    (pSigma : RedType eqrel l' Γ (.sigma F G)) :
    RedTerm pSigma (.prod t u) := by
  rcases elimSigmaAt' (.refl (escape pSigma)) pSigma with ⟨l₀, sigmaA⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ rel ↦ LogRelAt eqrel l₀ Δ (wk ρ F) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ a rel ↦ LogRelAt eqrel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel
  have hAt : LogRelAt eqrel l₀ Γ (.sigma F G) (RedSigmaRel eqrel Γ F G relF₀ relG₀) :=
    .sigma sigmaA.D sigmaA.hF sigmaA.hG sigmaA.AeqA relF₀ relG₀
      sigmaA.redF (fun _ _ _ h ↦ h) sigmaA.redG (fun _ _ _ _ h ↦ h) sigmaA.Gext
  have pSigma₀ : RedType eqrel l₀ Γ (.sigma F G) := ⟨_, hAt⟩
  have wft : HasType Γ t F := escapeTerm pF pt
  have wfu : HasType Γ u (subst0 G t) := escapeTerm pGt pu
  have wfΓ : CtxWf Γ := wfType sigmaA.hF
  have pF_id : RedType eqrel l₀ Γ (wk .id F) := sigmaA.redF .id wfΓ
  have hStep1 : Step Γ (.fst (.prod t u)) t F :=
    .sigmaBeta1 sigmaA.hF sigmaA.hG wft wfu
  rcases redSubstTerm hStep1 pF pt with ⟨hfstprod, hfstprod_t⟩
  have hfstprod' : RedTerm pF_id (.fst (.prod t u)) :=
    irrelevanceTerm' (wk_id F).symm pF pF_id hfstprod
  have hGeq : subst0 (wk (.lift .id) G) (.fst (.prod t u)) = subst0 G (.fst (.prod t u)) := by
    rw [wk_lift_id]
  have hGteq : subst0 (wk (.lift .id) G) t = subst0 G t := by
    rw [wk_lift_id]
  have pGfst : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) (.fst (.prod t u))) :=
    sigmaA.redG .id wfΓ hfstprod'
  have pGfst' : RedType eqrel l₀ Γ (subst0 G (.fst (.prod t u))) :=
    irrelevance' hGeq pGfst
  have pt_id : RedTerm pF_id t :=
    irrelevanceTerm' (wk_id F).symm pF pF_id pt
  have hfstprod_t_id : RedTermEq pF_id (.fst (.prod t u)) t :=
    irrelevanceEqTerm' (wk_id F).symm pF pF_id hfstprod_t
  have hGfst_Gt : RedEq pGfst' (subst0 G t) :=
    irrelevanceEq'' hGeq hGteq pGfst pGfst'
      (sigmaA.Gext .id wfΓ hfstprod' pt_id hfstprod_t_id)
  have pu_fst : RedTerm pGfst' u :=
    convTerm₂ pGfst' pGt hGfst_Gt pu
  have hStep2 : Step Γ (.snd (.prod t u)) u (subst0 G (.fst (.prod t u))) :=
    .sigmaBeta2 sigmaA.hF sigmaA.hG wft wfu
  rcases redSubstTerm hStep2 pGfst' pu_fst with ⟨hsndprod, hsndprod_u⟩
  have wfProd : HasType Γ (.prod t u) (.sigma F G) :=
    .prod sigmaA.hF sigmaA.hG wft wfu
  have hfstRefl : RedTermEq pF (.fst (.prod t u)) (.fst (.prod t u)) :=
    transEqTerm pF hfstprod_t (symEqTerm pF hfstprod_t)
  have hsndRefl : RedTermEq pGfst' (.snd (.prod t u)) (.snd (.prod t u)) :=
    transEqTerm pGfst' hsndprod_u (symEqTerm pGfst' hsndprod_u)
  have hProd₀ : RedSigmaTerm eqrel Γ F G relF₀ relG₀ (.prod t u) :=
    .mk (.prod t u) (idRedTermWf wfProd) .prod
      (eqrel.sigmaEta sigmaA.hF sigmaA.hG wfProd wfProd .prod .prod
        (escapeTermEq pF hfstRefl) (escapeTermEq pGfst' hsndRefl))
      hfstprod'
      (irrelevanceTerm' hGeq.symm pGfst' pGfst hsndprod)
  exact irrelevanceTerm pSigma₀ pSigma ⟨_, hAt, hProd₀⟩

/-- Reducibility of `prod` congruence (`prod-cong″`). -/
theorem prodCongTerm {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {F G t t' u u' : Term}
    (pF : RedType eqrel l Γ F)
    (pt : RedTerm pF t)
    (pt' : RedTerm pF t')
    (ptt' : RedTermEq pF t t')
    (pGt : RedType eqrel l Γ (subst0 G t))
    (pu : RedTerm pGt u)
    (pu' : RedTerm pGt u')
    (puu' : RedTermEq pGt u u')
    (pSigma : RedType eqrel l' Γ (.sigma F G)) :
    RedTermEq pSigma (.prod t u) (.prod t' u') := by
  rcases elimSigmaAt' (.refl (escape pSigma)) pSigma with ⟨l₀, sigmaA⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ rel ↦ LogRelAt eqrel l₀ Δ (wk ρ F) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ a rel ↦ LogRelAt eqrel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel
  have hAt : LogRelAt eqrel l₀ Γ (.sigma F G) (RedSigmaRel eqrel Γ F G relF₀ relG₀) :=
    .sigma sigmaA.D sigmaA.hF sigmaA.hG sigmaA.AeqA relF₀ relG₀
      sigmaA.redF (fun _ _ _ h ↦ h) sigmaA.redG (fun _ _ _ _ h ↦ h) sigmaA.Gext
  have pSigma₀ : RedType eqrel l₀ Γ (.sigma F G) := ⟨_, hAt⟩
  have hProd : RedSigmaTerm eqrel Γ F G relF₀ relG₀ (.prod t u) :=
    (RedTerm_of_LogRelAt hAt pSigma₀).mp (prodTerm pF pt pGt pu pSigma₀)
  have wfΓ : CtxWf Γ := wfType sigmaA.hF
  have pF_id : RedType eqrel l₀ Γ (wk .id F) := sigmaA.redF .id wfΓ
  have pt_id : RedTerm pF_id t := irrelevanceTerm' (wk_id F).symm pF pF_id pt
  have pt'_id : RedTerm pF_id t' := irrelevanceTerm' (wk_id F).symm pF pF_id pt'
  have ptt'_id : RedTermEq pF_id t t' := irrelevanceEqTerm' (wk_id F).symm pF pF_id ptt'
  have pGt_id : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) t) :=
    sigmaA.redG .id wfΓ pt_id
  have pGt'_id : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) t') :=
    sigmaA.redG .id wfΓ pt'_id
  have hGt_Gt'_id : RedEq pGt_id (subst0 (wk (.lift .id) G) t') :=
    sigmaA.Gext .id wfΓ pt_id pt'_id ptt'_id
  have hGteq : subst0 (wk (.lift .id) G) t = subst0 G t := by rw [wk_lift_id]
  have hGt'eq : subst0 (wk (.lift .id) G) t' = subst0 G t' := by rw [wk_lift_id]
  have pGt' : RedType eqrel l₀ Γ (subst0 G t') := irrelevance' hGt'eq pGt'_id
  have hGt_Gt' : RedEq pGt (subst0 G t') :=
    irrelevanceEq'' hGteq hGt'eq pGt_id pGt hGt_Gt'_id
  have pu'_Gt' : RedTerm pGt' u' := convTerm₁ pGt pGt' hGt_Gt' pu'
  have hProd' : RedSigmaTerm eqrel Γ F G relF₀ relG₀ (.prod t' u') :=
    (RedTerm_of_LogRelAt hAt pSigma₀).mp (prodTerm pF pt' pGt' pu'_Gt' pSigma₀)
  have wft : HasType Γ t F := escapeTerm pF pt
  have wft' : HasType Γ t' F := escapeTerm pF pt'
  have wfu : HasType Γ u (subst0 G t) := escapeTerm pGt pu
  have wfu' : HasType Γ u' (subst0 G t') := escapeTerm pGt' pu'_Gt'
  rcases redSubstTerm (.sigmaBeta1 sigmaA.hF sigmaA.hG wft wfu) pF pt with ⟨hfst, hfst_t⟩
  rcases redSubstTerm (.sigmaBeta1 sigmaA.hF sigmaA.hG wft' wfu') pF pt' with ⟨hfst', hfst_t'⟩
  have hfst_t_id : RedTermEq pF_id (.fst (.prod t u)) t :=
    irrelevanceEqTerm' (wk_id F).symm pF pF_id hfst_t
  have hfst_t'_id : RedTermEq pF_id (.fst (.prod t' u')) t' :=
    irrelevanceEqTerm' (wk_id F).symm pF pF_id hfst_t'
  have hfst_id : RedTerm pF_id (.fst (.prod t u)) :=
    irrelevanceTerm' (wk_id F).symm pF pF_id hfst
  have hfst'_id : RedTerm pF_id (.fst (.prod t' u')) :=
    irrelevanceTerm' (wk_id F).symm pF pF_id hfst'
  have hfst_fst' : RedTermEq pF (.fst (.prod t u)) (.fst (.prod t' u')) :=
    transEqTerm pF hfst_t (transEqTerm pF ptt' (symEqTerm pF hfst_t'))
  have hfst_fst'_id : RedTermEq pF_id (.fst (.prod t u)) (.fst (.prod t' u')) :=
    irrelevanceEqTerm' (wk_id F).symm pF pF_id hfst_fst'
  have hGfst_eq : subst0 (wk (.lift .id) G) (.fst (.prod t u)) = subst0 G (.fst (.prod t u)) := by
    rw [wk_lift_id]
  have pGfst_id : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) (.fst (.prod t u))) :=
    sigmaA.redG .id wfΓ hfst_id
  have pGfst : RedType eqrel l₀ Γ (subst0 G (.fst (.prod t u))) :=
    irrelevance' hGfst_eq pGfst_id
  have hGfst_Gt : RedEq pGfst (subst0 G t) :=
    irrelevanceEq'' hGfst_eq hGteq pGfst_id pGfst
      (sigmaA.Gext .id wfΓ hfst_id pt_id hfst_t_id)
  have pu_fst : RedTerm pGfst u := convTerm₂ pGfst pGt hGfst_Gt pu
  rcases redSubstTerm (.sigmaBeta2 sigmaA.hF sigmaA.hG wft wfu) pGfst pu_fst with ⟨_, hsnd_u⟩
  have huu'_fst : RedTermEq pGfst u u' := convEqTerm₂ pGfst pGt hGfst_Gt puu'
  have hGfst'_eq : subst0 (wk (.lift .id) G) (.fst (.prod t' u')) = subst0 G (.fst (.prod t' u')) := by
    rw [wk_lift_id]
  have pGfst'_id : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) (.fst (.prod t' u'))) :=
    sigmaA.redG .id wfΓ hfst'_id
  have pGfst' : RedType eqrel l₀ Γ (subst0 G (.fst (.prod t' u'))) :=
    irrelevance' hGfst'_eq pGfst'_id
  have hGfst'_Gt' : RedEq pGfst' (subst0 G t') :=
    irrelevanceEq'' hGfst'_eq hGt'eq pGfst'_id pGfst'
      (sigmaA.Gext .id wfΓ hfst'_id pt'_id hfst_t'_id)
  have pu'_fst' : RedTerm pGfst' u' := convTerm₂ pGfst' pGt' hGfst'_Gt' pu'_Gt'
  have hsnd'_u'_fst' : RedTermEq pGfst' (.snd (.prod t' u')) u' :=
    (redSubstTerm (.sigmaBeta2 sigmaA.hF sigmaA.hG wft' wfu') pGfst' pu'_fst').2
  have hGfst_Gfst' : RedEq pGfst (subst0 G (.fst (.prod t' u'))) :=
    irrelevanceEq'' hGfst_eq hGfst'_eq pGfst_id pGfst
      (sigmaA.Gext .id wfΓ hfst_id hfst'_id hfst_fst'_id)
  have hsnd'_u'_fst : RedTermEq pGfst (.snd (.prod t' u')) u' :=
    convEqTerm₂ pGfst pGfst' hGfst_Gfst' hsnd'_u'_fst'
  have hsnd_snd' : RedTermEq pGfst (.snd (.prod t u)) (.snd (.prod t' u')) :=
    transEqTerm pGfst hsnd_u (transEqTerm pGfst huu'_fst (symEqTerm pGfst hsnd'_u'_fst))
  have hsnd_snd'_id : RedTermEq pGfst_id (.snd (.prod t u)) (.snd (.prod t' u')) :=
    irrelevanceEqTerm' hGfst_eq.symm pGfst pGfst_id hsnd_snd'
  have wfProd : HasType Γ (.prod t u) (.sigma F G) := .prod sigmaA.hF sigmaA.hG wft wfu
  have wfProd' : HasType Γ (.prod t' u') (.sigma F G) := .prod sigmaA.hF sigmaA.hG wft' wfu'
  exact irrelevanceEqTerm pSigma₀ pSigma ⟨_, hAt,
    .mk (.prod t u) (.prod t' u')
      (idRedTermWf wfProd) (idRedTermWf wfProd')
      .prod .prod
      (eqrel.sigmaEta sigmaA.hF sigmaA.hG wfProd wfProd' .prod .prod
        (escapeTermEq pF hfst_fst') (escapeTermEq pGfst hsnd_snd'))
      hProd hProd' hfst_id hfst'_id hfst_fst'_id hsnd_snd'_id⟩

/-- Validity of `prod t u` (`prodᵛ`). -/
theorem prodValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t u : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (ht : ValidTerm hF t)
    (hu : ValidTerm (substS hF hG ht) u) :
    ValidTerm (sigmaValid hF hG) (.prod t u) := by
  intro Δ σ hΔ hσ
  have hGt : ValidType eqrel l Γ (subst0 G t) := substS hF hG ht
  have hSigma : ValidType eqrel l Γ (.sigma F G) := sigmaValid hF hG
  have pF := (hF hΔ hσ).red
  have pt := (ht hΔ hσ).term
  have pGt' := (hGt hΔ hσ).red
  have pGt : RedType eqrel l Δ (subst0 (subst (liftSubst σ) G) (subst σ t)) :=
    irrelevance' (singleSubstLift G t) pGt'
  have pu : RedTerm pGt (subst σ u) :=
    irrelevanceTerm' (singleSubstLift G t) pGt' pGt (hu hΔ hσ).term
  have pSigma := (hSigma hΔ hσ).red
  refine ⟨prodTerm pF pt pGt pu pSigma, fun {σ'} hσ' hσσ' ↦ ?_⟩
  have pF' := (hF hΔ hσ').red
  have pt' : RedTerm pF (subst σ' t) :=
    convTerm₂ pF pF' ((hF hΔ hσ).eq hσ' hσσ') (ht hΔ hσ').term
  have pGt'_σ' := (hGt hΔ hσ').red
  have pu'_conv : RedTerm pGt' (subst σ' u) :=
    convTerm₂ pGt' pGt'_σ' ((hGt hΔ hσ).eq hσ' hσσ') (hu hΔ hσ').term
  have pu' : RedTerm pGt (subst σ' u) :=
    irrelevanceTerm' (singleSubstLift G t) pGt' pGt pu'_conv
  have puu' : RedTermEq pGt (subst σ u) (subst σ' u) :=
    irrelevanceEqTerm' (singleSubstLift G t) pGt' pGt ((hu hΔ hσ).eq hσ' hσσ')
  exact prodCongTerm pF pt pt' ((ht hΔ hσ).eq hσ' hσσ') pGt pu pu' puu' pSigma

/-- Validity of `prod` congruence (`prod-congᵛ`). -/
theorem prodCongValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t t' u u' : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (ht : ValidTerm hF t)
    (ht' : ValidTerm hF t')
    (htt' : ValidTermEq hF t t')
    (hu : ValidTerm (substS hF hG ht) u)
    (hu' : ValidTerm (substS hF hG ht') u')
    (huu' : ValidTermEq (substS hF hG ht) u u') :
    ValidTermEq (sigmaValid hF hG) (.prod t u) (.prod t' u') := by
  intro Δ σ hΔ hσ
  have hGt : ValidType eqrel l Γ (subst0 G t) := substS hF hG ht
  have hGt' : ValidType eqrel l Γ (subst0 G t') := substS hF hG ht'
  have hSigma : ValidType eqrel l Γ (.sigma F G) := sigmaValid hF hG
  have pF := (hF hΔ hσ).red
  have pt := (ht hΔ hσ).term
  have pt' := (ht' hΔ hσ).term
  have pGt₁ := (hGt hΔ hσ).red
  have pGt : RedType eqrel l Δ (subst0 (subst (liftSubst σ) G) (subst σ t)) :=
    irrelevance' (singleSubstLift G t) pGt₁
  have pu : RedTerm pGt (subst σ u) :=
    irrelevanceTerm' (singleSubstLift G t) pGt₁ pGt (hu hΔ hσ).term
  have hGt_Gt' : ValidTypeEq hGt (subst0 G t') :=
    substSEq hF hF (reflValid hF) hG hG (reflValid hG) ht ht' htt'
  have pGt'₁ := (hGt' hΔ hσ).red
  have pu'₁ : RedTerm pGt₁ (subst σ u') :=
    convTerm₂ pGt₁ pGt'₁ (hGt_Gt' hΔ hσ) (hu' hΔ hσ).term
  have pu' : RedTerm pGt (subst σ u') :=
    irrelevanceTerm' (singleSubstLift G t) pGt₁ pGt pu'₁
  have puu' : RedTermEq pGt (subst σ u) (subst σ u') :=
    irrelevanceEqTerm' (singleSubstLift G t) pGt₁ pGt (huu' hΔ hσ)
  exact prodCongTerm pF pt pt' (htt' hΔ hσ) pGt pu pu' puu' (hSigma hΔ hσ).red

/-!
## `Σ`-β/η Introductions (`Definition/LogicalRelation/Substitution/Introductions/ProdBetaEta.agda`)
-/

/-- Validity of `Σ-β₁` (`Σ-β₁ᵛ`). -/
theorem sigmaBeta1Valid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t u : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (ht : ValidTerm hF t)
    (hu : ValidTerm (substS hF hG ht) u) :
    ValidTermEq hF (.fst (.prod t u)) t := by
  intro Δ σ hΔ hσ
  have hGt : ValidType eqrel l Γ (subst0 G t) := substS hF hG ht
  have pσF := (hF hΔ hσ).red
  have wfσF : TypeWf Δ (subst σ F) := escape pσF
  have hLiftσ := liftSubstS hΔ hF hσ
  have wfσG : TypeWf (subst σ F :: Δ) (subst (liftSubst σ) G) :=
    escape (hG (.cons hΔ wfσF) hLiftσ).red
  have wfσt : HasType Δ (subst σ t) (subst σ F) := escapeTerm pσF (ht hΔ hσ).term
  have pσGt₁ := (hGt hΔ hσ).red
  have pσGt : RedType eqrel l Δ (subst0 (subst (liftSubst σ) G) (subst σ t)) :=
    irrelevance' (singleSubstLift G t) pσGt₁
  have pσu : RedTerm pσGt (subst σ u) :=
    irrelevanceTerm' (singleSubstLift G t) pσGt₁ pσGt (hu hΔ hσ).term
  have wfσu : HasType Δ (subst σ u) (subst0 (subst (liftSubst σ) G) (subst σ t)) :=
    escapeTerm pσGt pσu
  exact (redSubstTerm (.sigmaBeta1 wfσF wfσG wfσt wfσu) pσF (ht hΔ hσ).term).2

/-- Validity of `Σ-β₂` (`Σ-β₂ᵛ`). -/
theorem sigmaBeta2Valid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G t u : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (ht : ValidTerm hF t)
    (hu : ValidTerm (substS hF hG ht) u) :
    ValidTermEq (substS hF hG (fstValid hF hG (prodValid hF hG ht hu)))
      (.snd (.prod t u)) u := by
  intro Δ σ hΔ hσ
  have hGt : ValidType eqrel l Γ (subst0 G t) := substS hF hG ht
  have hProd : ValidTerm (sigmaValid hF hG) (.prod t u) := prodValid hF hG ht hu
  have hFst : ValidTerm hF (.fst (.prod t u)) := fstValid hF hG hProd
  have hGfst : ValidType eqrel l Γ (subst0 G (.fst (.prod t u))) := substS hF hG hFst
  have hFst_t : ValidTermEq hF (.fst (.prod t u)) t := sigmaBeta1Valid hF hG ht hu
  have hGfst_Gt : ValidTypeEq hGfst (subst0 G t) :=
    substSEq hF hF (reflValid hF) hG hG (reflValid hG) hFst ht hFst_t
  have hu_Gfst : ValidTerm hGfst u := conv2Valid hGfst hGt hGfst_Gt hu
  have pσF := (hF hΔ hσ).red
  have wfσF : TypeWf Δ (subst σ F) := escape pσF
  have hLiftσ := liftSubstS hΔ hF hσ
  have wfσG : TypeWf (subst σ F :: Δ) (subst (liftSubst σ) G) :=
    escape (hG (.cons hΔ wfσF) hLiftσ).red
  have wfσt : HasType Δ (subst σ t) (subst σ F) := escapeTerm pσF (ht hΔ hσ).term
  have pσGt₁ := (hGt hΔ hσ).red
  have pσGt : RedType eqrel l Δ (subst0 (subst (liftSubst σ) G) (subst σ t)) :=
    irrelevance' (singleSubstLift G t) pσGt₁
  have pσu : RedTerm pσGt (subst σ u) :=
    irrelevanceTerm' (singleSubstLift G t) pσGt₁ pσGt (hu hΔ hσ).term
  have wfσu : HasType Δ (subst σ u) (subst0 (subst (liftSubst σ) G) (subst σ t)) :=
    escapeTerm pσGt pσu
  have hStep : Step Δ (subst σ (.snd (.prod t u))) (subst σ u)
      (subst0 (subst (liftSubst σ) G) (subst σ (.fst (.prod t u)))) :=
    .sigmaBeta2 wfσF wfσG wfσt wfσu
  have hEq : TypeEq Δ
      (subst0 (subst (liftSubst σ) G) (subst σ (.fst (.prod t u))))
      (subst σ (subst0 G (.fst (.prod t u)))) := by
    rw [← singleSubstLift G (.fst (.prod t u))]
    exact .refl (escape (hGfst hΔ hσ).red)
  exact (redSubstTerm (.conv hStep hEq) (hGfst hΔ hσ).red (hu_Gfst hΔ hσ).term).2

/-- Reducibility of `Σ-η` (`Σ-η″`). -/
theorem sigmaEtaTerm {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {F G p r : Term}
    (pF : RedType eqrel l' Γ F)
    (pGfstp : RedType eqrel l' Γ (subst0 G (.fst p)))
    (pSigma : RedType eqrel l Γ (.sigma F G))
    (hp : RedTerm pSigma p)
    (hr : RedTerm pSigma r)
    (hfstEq : RedTermEq pF (.fst p) (.fst r))
    (hsndEq : RedTermEq pGfstp (.snd p) (.snd r)) :
    RedTermEq pSigma p r := by
  rcases elimSigmaAt' (.refl (escape pSigma)) pSigma with ⟨l₀, sigmaA⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ rel ↦ LogRelAt eqrel l₀ Δ (wk ρ F) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ a rel ↦ LogRelAt eqrel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel
  have hAt : LogRelAt eqrel l₀ Γ (.sigma F G) (RedSigmaRel eqrel Γ F G relF₀ relG₀) :=
    .sigma sigmaA.D sigmaA.hF sigmaA.hG sigmaA.AeqA relF₀ relG₀
      sigmaA.redF (fun _ _ _ h ↦ h) sigmaA.redG (fun _ _ _ _ h ↦ h) sigmaA.Gext
  have pSigma₀ : RedType eqrel l₀ Γ (.sigma F G) := ⟨_, hAt⟩
  have hp₀ : RedSigmaTerm eqrel Γ F G relF₀ relG₀ p :=
    (RedTerm_of_LogRelAt hAt pSigma₀).mp (irrelevanceTerm pSigma pSigma₀ hp)
  have hr₀ : RedSigmaTerm eqrel Γ F G relF₀ relG₀ r :=
    (RedTerm_of_LogRelAt hAt pSigma₀).mp (irrelevanceTerm pSigma pSigma₀ hr)
  rcases hp₀ with ⟨p', dp, p'Prod, p'Eqp', hfstp', hsndp'⟩
  rcases hr₀ with ⟨r', dr, r'Prod, r'Eqr', hfstr', hsndr'⟩
  have wfΓ : CtxWf Γ := wfType sigmaA.hF
  have pF_id : RedType eqrel l₀ Γ (wk .id F) := sigmaA.redF .id wfΓ
  have pGfstp'_id : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) (.fst p')) :=
    sigmaA.redG .id wfΓ hfstp'
  have dFstp : Star Γ (.fst p) (.fst p') (wk .id F) := by
    rw [wk_id F]
    exact Star.fst sigmaA.hF sigmaA.hG dp.reduction
  have dFstr : Star Γ (.fst r) (.fst r') (wk .id F) := by
    rw [wk_id F]
    exact Star.fst sigmaA.hF sigmaA.hG dr.reduction
  rcases redSubstStarTerm dFstp pF_id hfstp' with ⟨hfstp_id, hfstp_p'_id⟩
  rcases redSubstStarTerm dFstr pF_id hfstr' with ⟨hfstr_id, hfstr_r'_id⟩
  have hfstEq_id : RedTermEq pF_id (.fst p) (.fst r) :=
    irrelevanceEqTerm' (wk_id F).symm pF pF_id hfstEq
  have hfst'_Eq_id : RedTermEq pF_id (.fst p') (.fst r') :=
    transEqTerm pF_id (symEqTerm pF_id hfstp_p'_id)
      (transEqTerm pF_id hfstEq_id hfstr_r'_id)
  have hp'₀ : RedTerm pSigma₀ p' :=
    ⟨_, hAt, .mk p' (idRedTermWf dp.target) p'Prod p'Eqp' hfstp' hsndp'⟩
  have hr'₀ : RedTerm pSigma₀ r' :=
    ⟨_, hAt, .mk r' (idRedTermWf dr.target) r'Prod r'Eqr' hfstr' hsndr'⟩
  have dSndp₁ : Star Γ (.snd p) (.snd p') (subst0 G (.fst p)) :=
    sndSubstStar pF pSigma₀ hp'₀ dp.reduction
  have dSndr₁ : Star Γ (.snd r) (.snd r') (subst0 G (.fst r)) :=
    sndSubstStar pF pSigma₀ hr'₀ dr.reduction
  have pGfstp_id : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) (.fst p)) :=
    sigmaA.redG .id wfΓ hfstp_id
  have pGfstr_id : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) (.fst r)) :=
    sigmaA.redG .id wfΓ hfstr_id
  have hGfstr_eq : subst0 (wk (.lift .id) G) (.fst r) = subst0 G (.fst r) := by
    rw [wk_lift_id]
  have hGfstp_eq : subst0 (wk (.lift .id) G) (.fst p) = subst0 G (.fst p) := by
    rw [wk_lift_id]
  have pGfstr : RedType eqrel l₀ Γ (subst0 G (.fst r)) :=
    irrelevance' hGfstr_eq pGfstr_id
  have pGfstr'_id : RedType eqrel l₀ Γ (subst0 (wk (.lift .id) G) (.fst r')) :=
    sigmaA.redG .id wfΓ hfstr'
  have hGfstp_p'_id : RedEq pGfstp (subst0 (wk (.lift .id) G) (.fst p')) :=
    irrelevanceEq' hGfstp_eq pGfstp_id pGfstp
      (sigmaA.Gext .id wfΓ hfstp_id hfstp' hfstp_p'_id)
  have hGfstr_p : RedEq pGfstr (subst0 G (.fst p)) :=
    irrelevanceEq'' hGfstr_eq hGfstp_eq pGfstr_id pGfstr
      (symEq pGfstp_id pGfstr_id (sigmaA.Gext .id wfΓ hfstp_id hfstr_id hfstEq_id))
  have hGfstr_p'_id : RedEq pGfstr (subst0 (wk (.lift .id) G) (.fst p')) :=
    transEq pGfstr pGfstp pGfstp'_id hGfstr_p hGfstp_p'_id
  have hGfstr'_p'_id : RedEq pGfstr'_id (subst0 (wk (.lift .id) G) (.fst p')) :=
    sigmaA.Gext .id wfΓ hfstr' hfstp' (symEqTerm pF_id hfst'_Eq_id)
  have dSndp : Star Γ (.snd p) (.snd p') (subst0 (wk (.lift .id) G) (.fst p')) :=
    dSndp₁.conv (eqrel.typeToEq (escapeEq pGfstp hGfstp_p'_id))
  have dSndr : Star Γ (.snd r) (.snd r') (subst0 (wk (.lift .id) G) (.fst p')) :=
    dSndr₁.conv (eqrel.typeToEq (escapeEq pGfstr hGfstr_p'_id))
  have hsndp_p'_id : RedTermEq pGfstp'_id (.snd p) (.snd p') :=
    (redSubstStarTerm dSndp pGfstp'_id hsndp').2
  have hsndr_r'_id : RedTermEq pGfstp'_id (.snd r) (.snd r') :=
    (redSubstStarTerm dSndr pGfstp'_id
      (convTerm₁ pGfstr'_id pGfstp'_id hGfstr'_p'_id hsndr')).2
  have hsndEq_id : RedTermEq pGfstp'_id (.snd p) (.snd r) :=
    convEqTerm₁ pGfstp pGfstp'_id hGfstp_p'_id hsndEq
  have hsnd'_Eq_id : RedTermEq pGfstp'_id (.snd p') (.snd r') :=
    transEqTerm pGfstp'_id (symEqTerm pGfstp'_id hsndp_p'_id)
      (transEqTerm pGfstp'_id hsndEq_id hsndr_r'_id)
  have hFstRel : eqrel.TermEqRel Γ (.fst p') (.fst r') F := by
    have h := escapeTermEq pF_id hfst'_Eq_id
    rw [wk_id F] at h
    exact h
  have hSndRel : eqrel.TermEqRel Γ (.snd p') (.snd r') (subst0 G (.fst p')) := by
    have h := escapeTermEq pGfstp'_id hsnd'_Eq_id
    rw [wk_lift_id G] at h
    exact h
  have hp'r'_Rel : eqrel.TermEqRel Γ p' r' (.sigma F G) :=
    eqrel.sigmaEta sigmaA.hF sigmaA.hG dp.target dr.target p'Prod r'Prod hFstRel hSndRel
  exact irrelevanceEqTerm pSigma₀ pSigma ⟨_, hAt,
    .mk p' r' dp dr p'Prod r'Prod hp'r'_Rel
      (.mk p' dp p'Prod p'Eqp' hfstp' hsndp')
      (.mk r' dr r'Prod r'Eqr' hfstr' hsndr')
      hfstp' hfstr' hfst'_Eq_id hsnd'_Eq_id⟩

/-- Validity of `Σ-η` (`Σ-ηᵛ`). -/
theorem sigmaEtaValid {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G p r : Term}
    (hF : ValidType eqrel l Γ F)
    (hG : ValidType eqrel l (F :: Γ) G)
    (hp : ValidTerm (sigmaValid hF hG) p)
    (hr : ValidTerm (sigmaValid hF hG) r)
    (hfstEq : ValidTermEq hF (.fst p) (.fst r))
    (hsndEq : ValidTermEq (substS hF hG (fstValid hF hG hp)) (.snd p) (.snd r)) :
    ValidTermEq (sigmaValid hF hG) p r := by
  intro Δ σ hΔ hσ
  have hSigma : ValidType eqrel l Γ (.sigma F G) := sigmaValid hF hG
  have hGfst : ValidType eqrel l Γ (subst0 G (.fst p)) := substS hF hG (fstValid hF hG hp)
  have pσF := (hF hΔ hσ).red
  have pσGfst₁ := (hGfst hΔ hσ).red
  have pσGfst : RedType eqrel l Δ (subst0 (subst (liftSubst σ) G) (subst σ (.fst p))) :=
    irrelevance' (singleSubstLift G (.fst p)) pσGfst₁
  have σsndEq : RedTermEq pσGfst (subst σ (.snd p)) (subst σ (.snd r)) :=
    irrelevanceEqTerm' (singleSubstLift G (.fst p)) pσGfst₁ pσGfst (hsndEq hΔ hσ)
  exact sigmaEtaTerm pσF pσGfst (hSigma hΔ hσ).red (hp hΔ hσ).term (hr hΔ hσ).term
    (hfstEq hΔ hσ) σsndEq

/-!
## Emptyrec Introductions (`Definition/LogicalRelation/Substitution/Introductions/Emptyrec.agda`)
-/

/-- Reducibility of `emptyrec A n` (`emptyrecTerm`). -/
theorem emptyrecTerm {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A n : Term}
    (pEmpty : RedType eqrel l Γ .empty)
    (pA : RedType eqrel l' Γ A)
    (pn : RedTerm pEmpty n) :
    RedTerm pA (.emptyrec A n) := by
  have pEmpty₀ : RedType eqrel l Γ .empty := redEmpty (escape pEmpty |> wfType)
  have hn : RedEmptyTerm eqrel Γ n :=
    (RedTerm_of_LogRelAt (.empty (idRedWf (.empty (escape pEmpty |> wfType)))) pEmpty₀).mp
      (irrelevanceTerm pEmpty pEmpty₀ pn)
  rcases hn with ⟨n', d, _, neN'⟩
  rcases neN' with ⟨neN', _, n'Eqn'⟩
  have wfA : TypeWf Γ A := escape pA
  have wfEr : HasType Γ (.emptyrec A n') A := .emptyrec wfA d.target
  have neEr : RedTerm pA (.emptyrec A n') :=
    neuTerm pA (.emptyrec neN') wfEr
      (eqrel.emptyrecCong (escapeEq pA (reflEq pA)) n'Eqn')
  exact (redSubstStarTerm (Star.emptyrec wfA d.reduction) pA neEr).1

/-- Reducibility of `emptyrec` congruence (`emptyrec-congTerm`). -/
theorem emptyrecCongTerm {eqrel : EqRelSet} {l l' l'' : TypeLevel} {Γ : Context} {A A' n n' : Term}
    (pEmpty : RedType eqrel l Γ .empty)
    (pA : RedType eqrel l' Γ A)
    (pA' : RedType eqrel l'' Γ A')
    (pAA' : RedEq pA A')
    (pnn' : RedTermEq pEmpty n n') :
    RedTermEq pA (.emptyrec A n) (.emptyrec A' n') := by
  have pEmpty₀ : RedType eqrel l Γ .empty := redEmpty (escape pEmpty |> wfType)
  have hnn' : RedEmptyTermEq eqrel Γ n n' :=
    (RedTermEq_of_LogRelAt (.empty (idRedWf (.empty (escape pEmpty |> wfType)))) pEmpty₀).mp
      (irrelevanceEqTerm pEmpty pEmpty₀ pnn')
  rcases hnn' with ⟨k, k', d, d', _, neKK'⟩
  rcases neKK' with ⟨neK, neK', kEqk'⟩
  have wfA : TypeWf Γ A := escape pA
  have wfA' : TypeWf Γ A' := escape pA'
  have hAA' : eqrel.TypeEqRel Γ A A' := escapeEq pA pAA'
  have wfEr : HasType Γ (.emptyrec A k) A := .emptyrec wfA d.target
  have wfEr' : HasType Γ (.emptyrec A' k') A' := .emptyrec wfA' d'.target
  have wfEr'_A : HasType Γ (.emptyrec A' k') A :=
    .conv wfEr' (.symm (eqrel.typeToEq hAA'))
  have neEr : RedTerm pA (.emptyrec A k) :=
    neuTerm pA (.emptyrec neK) wfEr
      (eqrel.emptyrecCong (escapeEq pA (reflEq pA))
        (eqrel.transNe kEqk' (eqrel.symmNe kEqk')))
  have neEr' : RedTerm pA' (.emptyrec A' k') :=
    neuTerm pA' (.emptyrec neK') wfEr'
      (eqrel.emptyrecCong (escapeEq pA' (reflEq pA'))
        (eqrel.transNe (eqrel.symmNe kEqk') kEqk'))
  have hErEq : RedTermEq pA (.emptyrec A n) (.emptyrec A k) :=
    (redSubstStarTerm (Star.emptyrec wfA d.reduction) pA neEr).2
  have hEr'Eq_A' : RedTermEq pA' (.emptyrec A' n') (.emptyrec A' k') :=
    (redSubstStarTerm (Star.emptyrec wfA' d'.reduction) pA' neEr').2
  have hEr'Eq : RedTermEq pA (.emptyrec A' n') (.emptyrec A' k') :=
    convEqTerm₂ pA pA' pAA' hEr'Eq_A'
  have hKK'Eq : RedTermEq pA (.emptyrec A k) (.emptyrec A' k') :=
    neuEqTerm pA (.emptyrec neK) (.emptyrec neK') wfEr wfEr'_A
      (eqrel.emptyrecCong hAA' kEqk')
  exact transEqTerm pA hErEq (transEqTerm pA hKK'Eq (symEqTerm pA hEr'Eq))

/-- Validity of `emptyrec A e` (`emptyrecᵛ`). -/
theorem emptyrecValid {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A n : Term}
    (hEmpty : ValidType eqrel l' Γ .empty)
    (hA : ValidType eqrel l Γ A)
    (hn : ValidTerm hEmpty n) :
    ValidTerm hA (.emptyrec A n) := by
  intro Δ σ hΔ hσ
  refine ⟨emptyrecTerm (hEmpty hΔ hσ).red (hA hΔ hσ).red (hn hΔ hσ).term,
    fun {σ'} hσ' hσσ' ↦ emptyrecCongTerm (hEmpty hΔ hσ).red
      (hA hΔ hσ).red (hA hΔ hσ').red ((hA hΔ hσ).eq hσ' hσσ') ((hn hΔ hσ).eq hσ' hσσ')⟩

/-- Validity of `emptyrec` congruence (`emptyrec-congᵛ`). -/
theorem emptyrecCongValid {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A A' n n' : Term}
    (hEmpty : ValidType eqrel l' Γ .empty)
    (hA : ValidType eqrel l Γ A)
    (hA' : ValidType eqrel l Γ A')
    (hAA' : ValidTypeEq hA A')
    (hn : ValidTermEq hEmpty n n') :
    ValidTermEq hA (.emptyrec A n) (.emptyrec A' n') := by
  intro Δ σ hΔ hσ
  exact emptyrecCongTerm (hEmpty hΔ hσ).red
    (hA hΔ hσ).red (hA' hΔ hσ).red (hAA' hΔ hσ) (hn hΔ hσ)

end LogrelMLTT
