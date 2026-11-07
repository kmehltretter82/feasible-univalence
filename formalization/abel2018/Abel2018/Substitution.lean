import Abel2018.LogicalRelationProperties

namespace Abel2018

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

end Abel2018
