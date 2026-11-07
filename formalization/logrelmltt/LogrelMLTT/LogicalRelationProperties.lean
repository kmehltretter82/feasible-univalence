/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/LogicalRelation/Weakening.agda,
Definition/LogicalRelation/Properties/Conversion.agda,
Definition/LogicalRelation/Properties/Symmetry.agda,
Definition/LogicalRelation/Properties/Transitivity.agda,
Definition/LogicalRelation/Properties/Universe.agda,
Definition/LogicalRelation/Properties/Neutral.agda,
Definition/LogicalRelation/Properties/Reduction.agda,
Definition/LogicalRelation/Properties/Successor.agda,
Definition/LogicalRelation/Application.agda.
-/
import LogrelMLTT.LogicalRelation

namespace LogrelMLTT

/-!
## Weakening of the Logical Relation (`Definition/LogicalRelation/Weakening.agda`)
-/

theorem wkTermNe {eqrel : EqRelSet} {ρ : Wk} {Γ Δ : Context} {k A : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (nf : RedNeNf eqrel Γ k A) :
    RedNeNf eqrel Δ (wk ρ k) (wk ρ A) :=
  ⟨nf.neK.wk ρ, wkHasType hρ hΔ nf.hk, eqrel.wkNe hρ hΔ nf.keqk⟩

theorem wkEqTermNe {eqrel : EqRelSet} {ρ : Wk} {Γ Δ : Context} {k m A : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (nf : RedNeNfEq eqrel Γ k m A) :
    RedNeNfEq eqrel Δ (wk ρ k) (wk ρ m) (wk ρ A) :=
  ⟨nf.neK.wk ρ, nf.neM.wk ρ, eqrel.wkNe hρ hΔ nf.keqm⟩

theorem wkTermNat {eqrel : EqRelSet} {ρ : Wk} {Γ Δ : Context} {t : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (ht : RedNatTerm eqrel Γ t) :
    RedNatTerm eqrel Δ (wk ρ t) :=
  @RedNatTerm.rec eqrel Γ
    (fun t _ ↦ RedNatTerm eqrel Δ (wk ρ t))
    (fun n _ ↦ NaturalProp eqrel Δ (wk ρ n))
    (fun t n d neqn _ ih ↦
      .mk (wk ρ t) (wk ρ n) (wkStarWf hρ hΔ d) (eqrel.wkTerm hρ hΔ neqn) ih)
    (fun _ ih ↦ .suc ih)
    .zero
    (fun nf ↦ .ne (wkTermNe hρ hΔ nf))
    t ht

theorem wkNaturalProp {eqrel : EqRelSet} {ρ : Wk} {Γ Δ : Context} {n : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (hn : NaturalProp eqrel Γ n) :
    NaturalProp eqrel Δ (wk ρ n) :=
  @NaturalProp.rec eqrel Γ
    (fun t _ ↦ RedNatTerm eqrel Δ (wk ρ t))
    (fun n _ ↦ NaturalProp eqrel Δ (wk ρ n))
    (fun t n d neqn _ ih ↦
      .mk (wk ρ t) (wk ρ n) (wkStarWf hρ hΔ d) (eqrel.wkTerm hρ hΔ neqn) ih)
    (fun _ ih ↦ .suc ih)
    .zero
    (fun nf ↦ .ne (wkTermNe hρ hΔ nf))
    n hn

theorem wkEqTermNat {eqrel : EqRelSet} {ρ : Wk} {Γ Δ : Context} {t u : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (htu : RedNatTermEq eqrel Γ t u) :
    RedNatTermEq eqrel Δ (wk ρ t) (wk ρ u) :=
  @RedNatTermEq.rec eqrel Γ
    (fun t u _ ↦ RedNatTermEq eqrel Δ (wk ρ t) (wk ρ u))
    (fun k k' _ ↦ NaturalEqProp eqrel Δ (wk ρ k) (wk ρ k'))
    (fun t u k k' d d' keqk' _ ih ↦
      .mk (wk ρ t) (wk ρ u) (wk ρ k) (wk ρ k')
        (wkStarWf hρ hΔ d) (wkStarWf hρ hΔ d')
        (eqrel.wkTerm hρ hΔ keqk') ih)
    (fun _ ih ↦ .suc ih)
    .zero
    (fun nf ↦ .ne (wkEqTermNe hρ hΔ nf))
    t u htu

theorem wkNaturalEqProp {eqrel : EqRelSet} {ρ : Wk} {Γ Δ : Context} {k k' : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (hk : NaturalEqProp eqrel Γ k k') :
    NaturalEqProp eqrel Δ (wk ρ k) (wk ρ k') :=
  @NaturalEqProp.rec eqrel Γ
    (fun t u _ ↦ RedNatTermEq eqrel Δ (wk ρ t) (wk ρ u))
    (fun k k' _ ↦ NaturalEqProp eqrel Δ (wk ρ k) (wk ρ k'))
    (fun t u k k' d d' keqk' _ ih ↦
      .mk (wk ρ t) (wk ρ u) (wk ρ k) (wk ρ k')
        (wkStarWf hρ hΔ d) (wkStarWf hρ hΔ d')
        (eqrel.wkTerm hρ hΔ keqk') ih)
    (fun _ ih ↦ .suc ih)
    .zero
    (fun nf ↦ .ne (wkEqTermNe hρ hΔ nf))
    k k' hk

/-- Single-level weakening step for `LogRelAt`. -/
theorem wkLogRel_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {ρ Γ Δ A rel},
      WkCtx ρ Δ Γ → CtxWf Δ →
      logRelRec eqrel l l' hlt Γ A rel →
      ∃ rel', logRelRec eqrel l l' hlt Δ (wk ρ A) rel' ∧
        (∀ {B}, rel.eqType B → rel'.eqType (wk ρ B)) ∧
        (∀ {t}, rel.hasTerm t → rel'.hasTerm (wk ρ t)) ∧
        (∀ {t u}, rel.eqTerm t u → rel'.eqTerm (wk ρ t) (wk ρ u)))
    {Γ : Context} {A : Term} {rel : RedRel}
    (hA : LogRelAt eqrel l Γ A rel) :
    ∀ {ρ : Wk} {Δ : Context}, WkCtx ρ Δ Γ → CtxWf Δ →
      ∃ rel', LogRelAt eqrel l Δ (wk ρ A) rel' ∧
        (∀ {B}, rel.eqType B → rel'.eqType (wk ρ B)) ∧
        (∀ {t}, rel.hasTerm t → rel'.hasTerm (wk ρ t)) ∧
        (∀ {t u}, rel.eqTerm t u → rel'.eqTerm (wk ρ t) (wk ρ u)) := by
  induction hA with
  | @U Γ l' hU =>
      intro ρ Δ hρ hΔ
      refine ⟨RedURel eqrel (logRelRec eqrel l l' hU.lt) Δ, .U ⟨hU.lt, hΔ⟩, ?_, ?_, ?_⟩
      · intro B hB
        change B = .univ at hB
        subst hB
        rfl
      · rintro t ⟨A₀, d, typeA, AeqA, relt, ht⟩
        rcases ihRec l' hU.lt hρ hΔ ht with ⟨relt', ht', _, _, _⟩
        exact ⟨wk ρ A₀, wkStarWf hρ hΔ d, typeA.wk ρ,
          eqrel.wkTerm hρ hΔ AeqA, ⟨relt', ht'⟩⟩
      · rintro t u ⟨A₀, B₀, d, d', typeA, typeB, AeqB, relt, ht, ⟨relu, hu⟩, tequ⟩
        rcases ihRec l' hU.lt hρ hΔ ht with ⟨relt', ht', hEq, _, _⟩
        rcases ihRec l' hU.lt hρ hΔ hu with ⟨relu', hu', _, _, _⟩
        exact ⟨wk ρ A₀, wk ρ B₀, wkStarWf hρ hΔ d, wkStarWf hρ hΔ d',
          typeA.wk ρ, typeB.wk ρ,
          eqrel.wkTerm hρ hΔ AeqB, relt', ht', ⟨relu', hu'⟩, hEq tequ⟩
  | @nat Γ A D =>
      intro ρ Δ hρ hΔ
      refine ⟨RedNatRel eqrel Δ, .nat (wkTypeStarWf hρ hΔ D), ?_, ?_, ?_⟩
      · intro B hB
        exact wkTypeStar hρ hΔ hB
      · intro t ht
        exact wkTermNat hρ hΔ ht
      · intro t u htu
        exact wkEqTermNat hρ hΔ htu
  | @ne Γ A K neA =>
      intro ρ Δ hρ hΔ
      refine ⟨RedNeRel eqrel Δ (wk ρ K),
        .ne ⟨wkTypeStarWf hρ hΔ neA.D, neA.neK.wk ρ, eqrel.wkNe hρ hΔ neA.KeqK⟩,
        ?_, ?_, ?_⟩
      · rintro B ⟨M, D', neM, KeqM⟩
        exact ⟨wk ρ M, wkTypeStarWf hρ hΔ D', neM.wk ρ, eqrel.wkNe hρ hΔ KeqM⟩
      · rintro t ⟨k, d, nf⟩
        exact ⟨wk ρ k, wkStarWf hρ hΔ d, wkTermNe hρ hΔ nf⟩
      · rintro t u ⟨k, m, d, d', nf⟩
        exact ⟨wk ρ k, wk ρ m, wkStarWf hρ hΔ d, wkStarWf hρ hΔ d',
          wkEqTermNe hρ hΔ nf⟩
  | @pi Γ A F G D hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext _ihF _ihG =>
      intro ρ Δ hρ hΔ
      have hρF : TypeWf Δ (wk ρ F) := wkTypeWf hρ hΔ hF
      have hρG : TypeWf (wk ρ F :: Δ) (wk (.lift ρ) G) :=
        wkTypeWf (.lift hρ) (.cons hΔ hρF) hG
      let relF' : Wk → Context → RedRel → Prop :=
        fun ρ₁ Δ₁ rel ↦ relF (compWk ρ₁ ρ) Δ₁ rel
      let relG' : Wk → Context → Term → RedRel → Prop :=
        fun ρ₁ Δ₁ a rel ↦ relG (compWk ρ₁ ρ) Δ₁ a rel
      refine ⟨RedPiRel eqrel Δ (wk ρ F) (wk (.lift ρ) G) relF' relG',
        .pi (wkTypeStarWf hρ hΔ D) hρF hρG (eqrel.wkType hρ hΔ AeqA)
          relF' relG'
          (fun hρ₁ hΔ₁ ↦ hF_ex (hρ₁.comp hρ) hΔ₁)
          (fun hρ₁ hΔ₁ r hr ↦ by
            rw [wk_comp]
            exact derivF (hρ₁.comp hρ) hΔ₁ r hr)
          (fun hρ₁ hΔ₁ ha ↦ hG_ex (hρ₁.comp hρ) hΔ₁ ha)
          (fun {ρ₁ Δ₁ a} hρ₁ hΔ₁ ha s hs ↦ by
            rw [← wk_comp_subst]
            exact derivG (hρ₁.comp hρ) hΔ₁ ha s hs)
          (fun {ρ₁ Δ₁ a b} hρ₁ hΔ₁ ha hb hab ↦ by
            rw [← wk_comp_subst]
            exact Gext (hρ₁.comp hρ) hΔ₁ ha hb hab),
        ?_, ?_, ?_⟩
      · rintro B ⟨F', G', D', AeqB, FeqF', GeqG'⟩
        refine ⟨wk ρ F', wk (.lift ρ) G', wkTypeStar hρ hΔ D', eqrel.wkType hρ hΔ AeqB,
          fun {ρ₁ Δ₁} hρ₁ hΔ₁ ↦ ?_,
          fun {ρ₁ Δ₁ a} hρ₁ hΔ₁ ha ↦ ?_⟩
        · rw [wk_comp]
          exact FeqF' (hρ₁.comp hρ) hΔ₁
        · rw [← wk_comp_subst]
          exact GeqG' (hρ₁.comp hρ) hΔ₁ ha
      · rintro t ⟨f, d, funcF, feqf, appEq, appTerm⟩
        refine ⟨wk ρ f, wkStarWf hρ hΔ d, funcF.wk ρ,
          eqrel.wkTerm hρ hΔ feqf,
          fun {ρ₁ Δ₁ a b} hρ₁ hΔ₁ ha hb hab ↦ ?_,
          fun {ρ₁ Δ₁ a} hρ₁ hΔ₁ ha ↦ ?_⟩
        · rw [wk_comp]
          exact appEq (hρ₁.comp hρ) hΔ₁ ha hb hab
        · rw [wk_comp]
          exact appTerm (hρ₁.comp hρ) hΔ₁ ha
      · rintro t u ⟨f, g, d, d', funcF, funcG, feqg, ht, hu, appEq⟩
        have hPiTerm : ∀ {t},
            RedPiTerm eqrel Γ F G relF relG t →
            RedPiTerm eqrel Δ (wk ρ F) (wk (.lift ρ) G) relF' relG' (wk ρ t) := by
          rintro t ⟨f₀, d₀, funcF₀, feqf₀, appEq₀, appTerm₀⟩
          refine ⟨wk ρ f₀, wkStarWf hρ hΔ d₀, funcF₀.wk ρ,
            eqrel.wkTerm hρ hΔ feqf₀,
            fun {ρ₁ Δ₁ a b} hρ₁ hΔ₁ ha hb hab ↦ ?_,
            fun {ρ₁ Δ₁ a} hρ₁ hΔ₁ ha ↦ ?_⟩
          · rw [wk_comp]
            exact appEq₀ (hρ₁.comp hρ) hΔ₁ ha hb hab
          · rw [wk_comp]
            exact appTerm₀ (hρ₁.comp hρ) hΔ₁ ha
        refine ⟨wk ρ f, wk ρ g, wkStarWf hρ hΔ d, wkStarWf hρ hΔ d',
          funcF.wk ρ, funcG.wk ρ,
          eqrel.wkTerm hρ hΔ feqg, hPiTerm ht, hPiTerm hu,
          fun {ρ₁ Δ₁ a} hρ₁ hΔ₁ ha ↦ ?_⟩
        rw [wk_comp, wk_comp]
        exact appEq (hρ₁.comp hρ) hΔ₁ ha
  | @emb Γ A l' rel hlt hA =>
      intro ρ Δ hρ hΔ
      rcases ihRec l' hlt hρ hΔ hA with ⟨rel', hA', hEq, hTerm, hEqTerm⟩
      exact ⟨rel', .emb hlt hA', hEq, hTerm, hEqTerm⟩

theorem wkLogRelAt {eqrel : EqRelSet} {l : TypeLevel} {ρ : Wk} {Γ Δ : Context} {A : Term}
    {rel : RedRel} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ)
    (hA : LogRelAt eqrel l Γ A rel) :
    ∃ rel', LogRelAt eqrel l Δ (wk ρ A) rel' ∧
      (∀ {B}, rel.eqType B → rel'.eqType (wk ρ B)) ∧
      (∀ {t}, rel.hasTerm t → rel'.hasTerm (wk ρ t)) ∧
      (∀ {t u}, rel.eqTerm t u → rel'.eqTerm (wk ρ t) (wk ρ u)) := by
  have h0 : ∀ {ρ Γ Δ A rel}, WkCtx ρ Δ Γ → CtxWf Δ →
      LogRelAt eqrel .zero Γ A rel →
      ∃ rel', LogRelAt eqrel .zero Δ (wk ρ A) rel' ∧
        (∀ {B}, rel.eqType B → rel'.eqType (wk ρ B)) ∧
        (∀ {t}, rel.hasTerm t → rel'.hasTerm (wk ρ t)) ∧
        (∀ {t u}, rel.eqTerm t u → rel'.eqTerm (wk ρ t) (wk ρ u)) :=
    fun hρ hΔ hA₀ ↦
      wkLogRel_step (l := .zero) (fun _ hlt ↦ nomatch hlt) hA₀ hρ hΔ
  cases l with
  | zero => exact h0 hρ hΔ hA
  | one =>
      exact wkLogRel_step (l := .one)
        (fun _ hlt _ _ _ _ _ hρ' hΔ' hA₀ ↦ by
          cases hlt
          exact h0 hρ' hΔ' hA₀)
        hA hρ hΔ

/-- Weakening of reducible types (`wk`). -/
theorem wkRed {eqrel : EqRelSet} {l : TypeLevel} {ρ : Wk} {Γ Δ : Context} {A : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (p : RedType eqrel l Γ A) :
    RedType eqrel l Δ (wk ρ A) := by
  rcases p with ⟨rel, hA⟩
  rcases wkLogRelAt hρ hΔ hA with ⟨rel', hA', _⟩
  exact ⟨rel', hA'⟩

/-- Weakening of reducible type equality (`wkEq`). -/
theorem wkRedEq {eqrel : EqRelSet} {l : TypeLevel} {ρ : Wk} {Γ Δ : Context} {A B : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (p : RedType eqrel l Γ A)
    (hAB : RedEq p B) : RedEq (wkRed hρ hΔ p) (wk ρ B) := by
  rcases hAB with ⟨rel, hA, hB⟩
  rcases wkLogRelAt hρ hΔ hA with ⟨rel', hA', hEq, _, _⟩
  exact ⟨rel', hA', hEq hB⟩

/-- Weakening of reducible terms (`wkTerm`). -/
theorem wkRedTerm {eqrel : EqRelSet} {l : TypeLevel} {ρ : Wk} {Γ Δ : Context} {A t : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (p : RedType eqrel l Γ A)
    (ht : RedTerm p t) : RedTerm (wkRed hρ hΔ p) (wk ρ t) := by
  rcases ht with ⟨rel, hA, ht⟩
  rcases wkLogRelAt hρ hΔ hA with ⟨rel', hA', _, hTerm, _⟩
  exact ⟨rel', hA', hTerm ht⟩

/-- Weakening of reducible term equality (`wkEqTerm`). -/
theorem wkRedTermEq {eqrel : EqRelSet} {l : TypeLevel} {ρ : Wk} {Γ Δ : Context} {A t u : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (p : RedType eqrel l Γ A)
    (htu : RedTermEq p t u) : RedTermEq (wkRed hρ hΔ p) (wk ρ t) (wk ρ u) := by
  rcases htu with ⟨rel, hA, htu⟩
  rcases wkLogRelAt hρ hΔ hA with ⟨rel', hA', _, _, hEqTerm⟩
  exact ⟨rel', hA', hEqTerm htu⟩

/-!
## Conversion of the Logical Relation (`Definition/LogicalRelation/Properties/Conversion.agda`)
-/

/-- Conversion of syntactic multi-step term reduction closures (`convRed:*:`). -/
theorem convStarWf {Γ : Context} {t u A B : Term}
    (d : StarWf Γ t u A) (hAB : TypeEq Γ A B) : StarWf Γ t u B :=
  ⟨.conv d.source hAB, .conv d.target hAB, d.reduction.conv hAB⟩

/-- Single-level conversion step for `LogRelAt`. -/
theorem convLogRel_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A B relA relB},
      logRelRec eqrel l l' hlt Γ A relA → LogRelShape eqrel Γ B relB → relA.eqType B →
      (∀ {t}, (relA.hasTerm t ↔ relB.hasTerm t)) ∧
      (∀ {t u}, (relA.eqTerm t u ↔ relB.eqTerm t u)))
    {Γ : Context} {A : Term} {relA : RedRel}
    (hA : LogRelAt eqrel l Γ A relA) :
    ∀ {B : Term} {relB : RedRel},
      LogRelShape eqrel Γ B relB →
      relA.eqType B →
      (∀ {t}, (relA.hasTerm t ↔ relB.hasTerm t)) ∧
      (∀ {t u}, (relA.eqTerm t u ↔ relB.eqTerm t u)) := by
  induction hA with
  | @U Γ l₁ hU =>
      intro B relB hB hAB
      change B = .univ at hAB
      subst hAB
      cases hB with
      | U hU₂ =>
          rw [logRelRec_eq hU.lt hU₂.lt]
          exact ⟨fun {_} ↦ Iff.rfl, fun {_ _} ↦ Iff.rfl⟩
      | nat D =>
          have h := whnfRedStar D.reduction .univ
          cases h
      | ne neB =>
          have h := whnfRedStar neB.D.reduction .univ
          subst h
          cases neB.neK
      | pi D =>
          have h := whnfRedStar D.reduction .univ
          cases h
  | @nat Γ A D₁ =>
      intro B relB hB hAB
      change TypeStar Γ B .nat at hAB
      cases hB with
      | U _ =>
          have h := whnfRedStar hAB .univ
          cases h
      | nat _ =>
          exact ⟨fun {_} ↦ Iff.rfl, fun {_ _} ↦ Iff.rfl⟩
      | ne neB =>
          have h := whrDetStar ⟨hAB, .nat⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ =>
          have h := whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .pi⟩
          cases h
  | @ne Γ A K₁ neA =>
      intro B relB hB hAB
      rcases hAB with ⟨M, D', neM, KeqM⟩
      cases hB with
      | U _ =>
          have h := whnfRedStar D'.reduction .univ
          subst h
          cases neM
      | nat D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D'.reduction, .neutral neM⟩
          subst h
          cases neM
      | @ne _ _ K₂ neB =>
          have hMK₂ : M = K₂ :=
            whrDetStar ⟨D'.reduction, .neutral neM⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst hMK₂
          have hK₁K₂ : TypeEq Γ K₁ M := eqrel.typeToEq (eqrel.neToType KeqM)
          refine ⟨?_, ?_⟩
          · intro t
            constructor
            · rintro ⟨k, d, nf⟩
              exact ⟨k, convStarWf d hK₁K₂,
                ⟨nf.neK, .conv nf.hk hK₁K₂, eqrel.convNe nf.keqk hK₁K₂⟩⟩
            · rintro ⟨k, d, nf⟩
              exact ⟨k, convStarWf d (.symm hK₁K₂),
                ⟨nf.neK, .conv nf.hk (.symm hK₁K₂), eqrel.convNe nf.keqk (.symm hK₁K₂)⟩⟩
          · intro t u
            constructor
            · rintro ⟨k, m, d, d'', nf⟩
              exact ⟨k, m, convStarWf d hK₁K₂, convStarWf d'' hK₁K₂,
                ⟨nf.neK, nf.neM, eqrel.convNe nf.keqm hK₁K₂⟩⟩
            · rintro ⟨k, m, d, d'', nf⟩
              exact ⟨k, m, convStarWf d (.symm hK₁K₂), convStarWf d'' (.symm hK₁K₂),
                ⟨nf.neK, nf.neM, eqrel.convNe nf.keqm (.symm hK₁K₂)⟩⟩
      | pi D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D'.reduction, .neutral neM⟩
          subst h
          cases neM
  | @pi Γ A F₁ G₁ D₁ _hF₁ _hG₁ _AeqA₁ relF₁ relG₁ hF_ex₁ derivF₁ hG_ex₁ derivG₁ _Gext₁ ihF ihG =>
      intro B relB hB hAB
      rcases hAB with ⟨F', G', D', AeqB, FeqF', GeqG'⟩
      cases hB with
      | U _ =>
          have h := whnfRedStar D' .univ
          cases h
      | nat D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D', .pi⟩
          cases h
      | ne neB =>
          have h := whrDetStar ⟨D', .pi⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | @pi l₂ _ _ F₂ G₂ D₂ _ _ _ relF₂ relG₂ hF_ex₂ derivF₂ hG_ex₂ derivG₂ _ =>
          have hPi : Term.pi F₂ G₂ = Term.pi F' G' :=
            whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D', .pi⟩
          injection hPi with hF₂ hG₂
          subst hF₂ hG₂
          have hPiEq : TypeEq Γ (.pi F₁ G₁) (.pi F₂ G₂) := eqrel.typeToEq AeqB
          have hF_conv : ∀ {ρ Δ} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ),
              (∀ {a}, RelFHasTerm relF₁ ρ Δ a ↔ RelFHasTerm relF₂ ρ Δ a) ∧
              (∀ {a b}, RelFEqTerm relF₁ ρ Δ a b ↔ RelFEqTerm relF₂ ρ Δ a b) := by
            intro ρ Δ hρ hΔ
            rcases FeqF' hρ hΔ with ⟨r₁, hr₁, hF₁₂⟩
            rcases hF_ex₂ hρ hΔ with ⟨r₂, hr₂⟩
            have hAt₁ := derivF₁ hρ hΔ r₁ hr₁
            have hAt₂ := derivF₂ hρ hΔ r₂ hr₂
            have hConv := ihF hρ hΔ r₁ hr₁ (logRelShape_of_LogRelAt hAt₂) hF₁₂
            refine ⟨?_, ?_⟩
            · intro a
              constructor
              · rintro ⟨r₁', hr₁', ha⟩
                have ha₁ := (irrelLogRel (derivF₁ hρ hΔ r₁' hr₁') hAt₁).2.1.mp ha
                exact ⟨r₂, hr₂, hConv.1.mp ha₁⟩
              · rintro ⟨r₂', hr₂', ha⟩
                have ha₂ := (irrelLogRel (derivF₂ hρ hΔ r₂' hr₂') hAt₂).2.1.mp ha
                exact ⟨r₁, hr₁, hConv.1.mpr ha₂⟩
            · intro a b
              constructor
              · rintro ⟨r₁', hr₁', hab⟩
                have hab₁ := (irrelLogRel (derivF₁ hρ hΔ r₁' hr₁') hAt₁).2.2.mp hab
                exact ⟨r₂, hr₂, hConv.2.mp hab₁⟩
              · rintro ⟨r₂', hr₂', hab⟩
                have hab₂ := (irrelLogRel (derivF₂ hρ hΔ r₂' hr₂') hAt₂).2.2.mp hab
                exact ⟨r₁, hr₁, hConv.2.mpr hab₂⟩
          have hG_conv : ∀ {ρ Δ a} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ)
              (ha₁ : RelFHasTerm relF₁ ρ Δ a),
              (∀ {t}, RelGHasTerm relG₁ ρ Δ a t ↔ RelGHasTerm relG₂ ρ Δ a t) ∧
              (∀ {t u}, RelGEqTerm relG₁ ρ Δ a t u ↔ RelGEqTerm relG₂ ρ Δ a t u) := by
            intro ρ Δ a hρ hΔ ha₁
            have ha₂ : RelFHasTerm relF₂ ρ Δ a := (hF_conv hρ hΔ).1.mp ha₁
            rcases GeqG' hρ hΔ ha₁ with ⟨s₁, hs₁, hG₁₂⟩
            rcases hG_ex₂ hρ hΔ ha₂ with ⟨s₂, hs₂⟩
            have hAt₁ := derivG₁ hρ hΔ ha₁ s₁ hs₁
            have hAt₂ := derivG₂ hρ hΔ ha₂ s₂ hs₂
            have hConv := ihG hρ hΔ ha₁ s₁ hs₁ (logRelShape_of_LogRelAt hAt₂) hG₁₂
            refine ⟨?_, ?_⟩
            · intro t
              constructor
              · rintro ⟨s₁', hs₁', ht⟩
                have ht₁ := (irrelLogRel (derivG₁ hρ hΔ ha₁ s₁' hs₁') hAt₁).2.1.mp ht
                exact ⟨s₂, hs₂, hConv.1.mp ht₁⟩
              · rintro ⟨s₂', hs₂', ht⟩
                have ht₂ := (irrelLogRel (derivG₂ hρ hΔ ha₂ s₂' hs₂') hAt₂).2.1.mp ht
                exact ⟨s₁, hs₁, hConv.1.mpr ht₂⟩
            · intro t u
              constructor
              · rintro ⟨s₁', hs₁', htu⟩
                have htu₁ := (irrelLogRel (derivG₁ hρ hΔ ha₁ s₁' hs₁') hAt₁).2.2.mp htu
                exact ⟨s₂, hs₂, hConv.2.mp htu₁⟩
              · rintro ⟨s₂', hs₂', htu⟩
                have htu₂ := (irrelLogRel (derivG₂ hρ hΔ ha₂ s₂' hs₂') hAt₂).2.2.mp htu
                exact ⟨s₁, hs₁, hConv.2.mpr htu₂⟩
          have hPiTermIff : ∀ {t},
              RedPiTerm eqrel Γ F₁ G₁ relF₁ relG₁ t ↔ RedPiTerm eqrel Γ F₂ G₂ relF₂ relG₂ t := by
            intro t
            constructor
            · rintro ⟨f, d, funcF, feqf, appEq, appTerm⟩
              refine ⟨f, convStarWf d hPiEq, funcF, eqrel.convTerm feqf hPiEq,
                fun {ρ Δ a b} hρ hΔ ha₂ hb₂ hab₂ ↦ ?_,
                fun {ρ Δ a} hρ hΔ ha₂ ↦ ?_⟩
              · have ha₁ := (hF_conv hρ hΔ).1.mpr ha₂
                have hb₁ := (hF_conv hρ hΔ).1.mpr hb₂
                have hab₁ := (hF_conv hρ hΔ).2.mpr hab₂
                exact (hG_conv hρ hΔ ha₁).2.mp (appEq hρ hΔ ha₁ hb₁ hab₁)
              · have ha₁ := (hF_conv hρ hΔ).1.mpr ha₂
                exact (hG_conv hρ hΔ ha₁).1.mp (appTerm hρ hΔ ha₁)
            · rintro ⟨f, d, funcF, feqf, appEq, appTerm⟩
              refine ⟨f, convStarWf d (.symm hPiEq), funcF, eqrel.convTerm feqf (.symm hPiEq),
                fun {ρ Δ a b} hρ hΔ ha₁ hb₁ hab₁ ↦ ?_,
                fun {ρ Δ a} hρ hΔ ha₁ ↦ ?_⟩
              · have ha₂ := (hF_conv hρ hΔ).1.mp ha₁
                have hb₂ := (hF_conv hρ hΔ).1.mp hb₁
                have hab₂ := (hF_conv hρ hΔ).2.mp hab₁
                exact (hG_conv hρ hΔ ha₁).2.mpr (appEq hρ hΔ ha₂ hb₂ hab₂)
              · have ha₂ := (hF_conv hρ hΔ).1.mp ha₁
                exact (hG_conv hρ hΔ ha₁).1.mpr (appTerm hρ hΔ ha₂)
          refine ⟨hPiTermIff, ?_⟩
          intro t u
          constructor
          · rintro ⟨f, g, d, d'', funcF, funcG, feqg, ht, hu, appEq⟩
            refine ⟨f, g, convStarWf d hPiEq, convStarWf d'' hPiEq, funcF, funcG,
              eqrel.convTerm feqg hPiEq, hPiTermIff.mp ht, hPiTermIff.mp hu,
              fun {ρ Δ a} hρ hΔ ha₂ ↦ ?_⟩
            have ha₁ := (hF_conv hρ hΔ).1.mpr ha₂
            exact (hG_conv hρ hΔ ha₁).2.mp (appEq hρ hΔ ha₁)
          · rintro ⟨f, g, d, d'', funcF, funcG, feqg, ht, hu, appEq⟩
            refine ⟨f, g, convStarWf d (.symm hPiEq), convStarWf d'' (.symm hPiEq), funcF, funcG,
              eqrel.convTerm feqg (.symm hPiEq), hPiTermIff.mpr ht, hPiTermIff.mpr hu,
              fun {ρ Δ a} hρ hΔ ha₁ ↦ ?_⟩
            have ha₂ := (hF_conv hρ hΔ).1.mp ha₁
            exact (hG_conv hρ hΔ ha₁).2.mpr (appEq hρ hΔ ha₂)
  | @emb Γ A l' relA hlt hA =>
      intro B relB hB hAB
      exact ihRec l' hlt hA hB hAB

theorem convLogRelAt {eqrel : EqRelSet} {l₁ l₂ : TypeLevel} {Γ : Context} {A B : Term}
    {relA relB : RedRel}
    (hA : LogRelAt eqrel l₁ Γ A relA)
    (hB : LogRelAt eqrel l₂ Γ B relB)
    (hAB : relA.eqType B) :
    (∀ {t}, (relA.hasTerm t ↔ relB.hasTerm t)) ∧
    (∀ {t u}, (relA.eqTerm t u ↔ relB.eqTerm t u)) := by
  have h0 : ∀ {Γ A B relA relB},
      LogRelAt eqrel .zero Γ A relA → LogRelShape eqrel Γ B relB → relA.eqType B →
      (∀ {t}, (relA.hasTerm t ↔ relB.hasTerm t)) ∧
      (∀ {t u}, (relA.eqTerm t u ↔ relB.eqTerm t u)) :=
    fun hA₀ hBs hAB₀ ↦
      convLogRel_step (l := .zero) (fun _ hlt ↦ nomatch hlt) hA₀ hBs hAB₀
  cases l₁ with
  | zero => exact h0 hA (logRelShape_of_LogRelAt hB) hAB
  | one =>
      exact convLogRel_step (l := .one)
        (fun _ hlt _ _ _ _ _ hA₀ hBs hAB₀ ↦ by cases hlt; exact h0 hA₀ hBs hAB₀)
        hA (logRelShape_of_LogRelAt hB) hAB

/-- Left-to-right term conversion (`convTerm₁`). -/
theorem convTerm₁ {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B t : Term}
    (pA : RedType eqrel l Γ A) (pB : RedType eqrel l' Γ B)
    (hAB : RedEq pA B) (ht : RedTerm pA t) : RedTerm pB t := by
  rcases hAB with ⟨relA, hA, hEqB⟩
  rcases pB with ⟨relB, hB⟩
  rcases ht with ⟨relA', hA', ht⟩
  have htA : relA.hasTerm t := (irrelLogRel hA' hA).2.1.mp ht
  exact ⟨relB, hB, (convLogRelAt hA hB hEqB).1.mp htA⟩

/-- Right-to-left term conversion (`convTerm₂`). -/
theorem convTerm₂ {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B t : Term}
    (pA : RedType eqrel l Γ A) (pB : RedType eqrel l' Γ B)
    (hAB : RedEq pA B) (ht : RedTerm pB t) : RedTerm pA t := by
  rcases hAB with ⟨relA, hA, hEqB⟩
  rcases ht with ⟨relB, hB, ht⟩
  exact ⟨relA, hA, (convLogRelAt hA hB hEqB).1.mpr ht⟩

/-- Right-to-left term conversion with propositionally equal right types (`convTerm₂′`). -/
theorem convTerm₂' {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B B' t : Term}
    (hBB' : B = B') (pA : RedType eqrel l Γ A) (pB : RedType eqrel l' Γ B)
    (hAB' : RedEq pA B') (ht : RedTerm pB t) : RedTerm pA t := by
  subst hBB'
  exact convTerm₂ pA pB hAB' ht

/-- Left-to-right term equality conversion (`convEqTerm₁`). -/
theorem convEqTerm₁ {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B t u : Term}
    (pA : RedType eqrel l Γ A) (pB : RedType eqrel l' Γ B)
    (hAB : RedEq pA B) (htu : RedTermEq pA t u) : RedTermEq pB t u := by
  rcases hAB with ⟨relA, hA, hEqB⟩
  rcases pB with ⟨relB, hB⟩
  rcases htu with ⟨relA', hA', htu⟩
  have htuA : relA.eqTerm t u := (irrelLogRel hA' hA).2.2.mp htu
  exact ⟨relB, hB, (convLogRelAt hA hB hEqB).2.mp htuA⟩

/-- Right-to-left term equality conversion (`convEqTerm₂`). -/
theorem convEqTerm₂ {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B t u : Term}
    (pA : RedType eqrel l Γ A) (pB : RedType eqrel l' Γ B)
    (hAB : RedEq pA B) (htu : RedTermEq pB t u) : RedTermEq pA t u := by
  rcases hAB with ⟨relA, hA, hEqB⟩
  rcases htu with ⟨relB, hB, htu⟩
  exact ⟨relA, hA, (convLogRelAt hA hB hEqB).2.mpr htu⟩

/-!
## Symmetry of the Logical Relation (`Definition/LogicalRelation/Properties/Symmetry.agda`)
-/

/-- Single-level symmetry step for `LogRelAt` type equality. -/
theorem symLogRel_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A B relA relB},
      logRelRec eqrel l l' hlt Γ A relA → LogRelShape eqrel Γ B relB →
      relA.eqType B → relB.eqType A)
    {Γ : Context} {A : Term} {relA : RedRel}
    (hA : LogRelAt eqrel l Γ A relA) :
    ∀ {B : Term} {relB : RedRel},
      LogRelShape eqrel Γ B relB → relA.eqType B → relB.eqType A := by
  induction hA with
  | @U Γ l₁ hU =>
      intro B relB hB hAB
      change B = .univ at hAB
      subst hAB
      cases hB with
      | U _ => rfl
      | nat D => cases whnfRedStar D.reduction .univ
      | ne neB =>
          have h := whnfRedStar neB.D.reduction .univ
          subst h
          cases neB.neK
      | pi D => cases whnfRedStar D.reduction .univ
  | @nat Γ A D₁ =>
      intro B relB hB hAB
      change TypeStar Γ B .nat at hAB
      cases hB with
      | U _ => cases whnfRedStar hAB .univ
      | nat _ => exact D₁.reduction
      | ne neB =>
          have h := whrDetStar ⟨hAB, .nat⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ => cases whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .pi⟩
  | @ne Γ A K₁ neA =>
      intro B relB hB hAB
      rcases hAB with ⟨M, D', neM, KeqM⟩
      cases hB with
      | U _ =>
          have h := whnfRedStar D'.reduction .univ
          subst h
          cases neM
      | nat D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D'.reduction, .neutral neM⟩
          subst h
          cases neM
      | @ne _ _ K₂ neB =>
          have hMK₂ : M = K₂ :=
            whrDetStar ⟨D'.reduction, .neutral neM⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst hMK₂
          exact ⟨K₁, neA.D, neA.neK, eqrel.symmNe KeqM⟩
      | pi D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D'.reduction, .neutral neM⟩
          subst h
          cases neM
  | @pi Γ A F₁ G₁ D₁ _hF₁ _hG₁ _AeqA₁ relF₁ relG₁ _hF_ex₁ derivF₁ _hG_ex₁ _derivG₁ _Gext₁ ihF ihG =>
      intro B relB hB hAB
      rcases hAB with ⟨F', G', D', AeqB, FeqF', GeqG'⟩
      cases hB with
      | U _ => cases whnfRedStar D' .univ
      | nat D₂ => cases whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D', .pi⟩
      | ne neB =>
          have h := whrDetStar ⟨D', .pi⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | @pi l₂ _ _ F₂ G₂ D₂ _ _ _ relF₂ relG₂ hF_ex₂ derivF₂ hG_ex₂ derivG₂ _ =>
          have hPi : Term.pi F₂ G₂ = Term.pi F' G' :=
            whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D', .pi⟩
          injection hPi with hF₂ hG₂
          subst hF₂ hG₂
          refine ⟨F₁, G₁, D₁.reduction, eqrel.symmType AeqB,
            fun {ρ Δ} hρ hΔ ↦ ?_,
            fun {ρ Δ a} hρ hΔ ha₂ ↦ ?_⟩
          · rcases FeqF' hρ hΔ with ⟨r₁, hr₁, hF₁₂⟩
            rcases hF_ex₂ hρ hΔ with ⟨r₂, hr₂⟩
            have hAt₂ := derivF₂ hρ hΔ r₂ hr₂
            exact ⟨r₂, hr₂, ihF hρ hΔ r₁ hr₁ (logRelShape_of_LogRelAt hAt₂) hF₁₂⟩
          · rcases FeqF' hρ hΔ with ⟨r₁, hr₁, hF₁₂⟩
            rcases ha₂ with ⟨r₂, hr₂, ha₂'⟩
            have hAt₁ := derivF₁ hρ hΔ r₁ hr₁
            have hAt₂ := derivF₂ hρ hΔ r₂ hr₂
            have ha₁ : RelFHasTerm relF₁ ρ Δ a :=
              ⟨r₁, hr₁, (convLogRelAt hAt₁ hAt₂ hF₁₂).1.mpr ha₂'⟩
            rcases GeqG' hρ hΔ ha₁ with ⟨s₁, hs₁, hG₁₂⟩
            rcases hG_ex₂ hρ hΔ ⟨r₂, hr₂, ha₂'⟩ with ⟨s₂, hs₂⟩
            have hGAt₂ := derivG₂ hρ hΔ ⟨r₂, hr₂, ha₂'⟩ s₂ hs₂
            exact ⟨s₂, hs₂, ihG hρ hΔ ha₁ s₁ hs₁ (logRelShape_of_LogRelAt hGAt₂) hG₁₂⟩
  | @emb Γ A l' relA hlt hA =>
      intro B relB hB hAB
      exact ihRec l' hlt hA hB hAB

theorem symLogRelAt {eqrel : EqRelSet} {l₁ l₂ : TypeLevel} {Γ : Context} {A B : Term}
    {relA relB : RedRel}
    (hA : LogRelAt eqrel l₁ Γ A relA)
    (hB : LogRelAt eqrel l₂ Γ B relB)
    (hAB : relA.eqType B) : relB.eqType A := by
  have h0 : ∀ {Γ A B relA relB},
      LogRelAt eqrel .zero Γ A relA → LogRelShape eqrel Γ B relB →
      relA.eqType B → relB.eqType A :=
    fun hA₀ hBs hAB₀ ↦
      symLogRel_step (l := .zero) (fun _ hlt ↦ nomatch hlt) hA₀ hBs hAB₀
  cases l₁ with
  | zero => exact h0 hA (logRelShape_of_LogRelAt hB) hAB
  | one =>
      exact symLogRel_step (l := .one)
        (fun _ hlt _ _ _ _ _ hA₀ hBs hAB₀ ↦ by cases hlt; exact h0 hA₀ hBs hAB₀)
        hA (logRelShape_of_LogRelAt hB) hAB

/-- Symmetry of reducible type equality (`symEq`). -/
theorem symEq {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B : Term}
    (pA : RedType eqrel l Γ A) (pB : RedType eqrel l' Γ B)
    (hAB : RedEq pA B) : RedEq pB A := by
  rcases hAB with ⟨relA, hA, hEqB⟩
  rcases pB with ⟨relB, hB⟩
  exact ⟨relB, hB, symLogRelAt hA hB hEqB⟩

theorem symNeutralTerm {eqrel : EqRelSet} {Γ : Context} {k m A : Term}
    (nf : RedNeNfEq eqrel Γ k m A) : RedNeNfEq eqrel Γ m k A :=
  ⟨nf.neM, nf.neK, eqrel.symmNe nf.keqm⟩

theorem symEqTermNat {eqrel : EqRelSet} {Γ : Context} {t u : Term}
    (htu : RedNatTermEq eqrel Γ t u) : RedNatTermEq eqrel Γ u t :=
  @RedNatTermEq.rec eqrel Γ
    (fun t u _ ↦ RedNatTermEq eqrel Γ u t)
    (fun k k' _ ↦ NaturalEqProp eqrel Γ k' k)
    (fun t u k k' d d' keqk' _ ih ↦
      .mk u t k' k d' d (eqrel.symmTerm keqk') ih)
    (fun _ ih ↦ .suc ih)
    .zero
    (fun nf ↦ .ne (symNeutralTerm nf))
    t u htu

theorem symNaturalProp {eqrel : EqRelSet} {Γ : Context} {k k' : Term}
    (hk : NaturalEqProp eqrel Γ k k') : NaturalEqProp eqrel Γ k' k :=
  @NaturalEqProp.rec eqrel Γ
    (fun t u _ ↦ RedNatTermEq eqrel Γ u t)
    (fun k k' _ ↦ NaturalEqProp eqrel Γ k' k)
    (fun t u k k' d d' keqk' _ ih ↦
      .mk u t k' k d' d (eqrel.symmTerm keqk') ih)
    (fun _ ih ↦ .suc ih)
    .zero
    (fun nf ↦ .ne (symNeutralTerm nf))
    k k' hk

theorem symEqTerm_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A rel t u},
      logRelRec eqrel l l' hlt Γ A rel → rel.eqTerm t u → rel.eqTerm u t)
    (hSymType : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A B relA relB},
      logRelRec eqrel l l' hlt Γ A relA → logRelRec eqrel l l' hlt Γ B relB →
      relA.eqType B → relB.eqType A)
    {Γ : Context} {A : Term} {rel : RedRel}
    (hA : LogRelAt eqrel l Γ A rel) :
    ∀ {t u : Term}, rel.eqTerm t u → rel.eqTerm u t := by
  induction hA with
  | @U Γ l' hU =>
      rintro t u ⟨A₀, B₀, d, d', typeA, typeB, AeqB, relt, ht, ⟨relu, hu⟩, tequ⟩
      exact ⟨B₀, A₀, d', d, typeB, typeA, eqrel.symmTerm AeqB, relu, hu, ⟨relt, ht⟩,
        hSymType l' hU.lt ht hu tequ⟩
  | @nat Γ A _ =>
      intro t u htu
      exact symEqTermNat htu
  | @ne Γ A K _ =>
      rintro t u ⟨k, m, d, d', nf⟩
      exact ⟨m, k, d', d, symNeutralTerm nf⟩
  | @pi Γ A F G _ _ _ _ relF relG _ _ _ _ _ _ihF ihG =>
      rintro t u ⟨f, g, d, d', funcF, funcG, feqg, ht, hu, appEq⟩
      refine ⟨g, f, d', d, funcG, funcF, eqrel.symmTerm feqg, hu, ht,
        fun {ρ Δ a} hρ hΔ ha ↦ ?_⟩
      rcases appEq hρ hΔ ha with ⟨s, hs, hfg⟩
      exact ⟨s, hs, ihG hρ hΔ ha s hs hfg⟩
  | @emb Γ A l' rel hlt hA =>
      intro t u htu
      exact ihRec l' hlt hA htu

/-- Symmetry of reducible term equality (`symEqTerm`). -/
theorem symEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u : Term}
    (pA : RedType eqrel l Γ A) (htu : RedTermEq pA t u) : RedTermEq pA u t := by
  rcases htu with ⟨rel, hA, htu⟩
  have h0 : ∀ {Γ A rel t u},
      LogRelAt eqrel .zero Γ A rel → rel.eqTerm t u → rel.eqTerm u t :=
    fun hA₀ htu₀ ↦
      symEqTerm_step (l := .zero) (fun _ hlt ↦ nomatch hlt) (fun _ hlt ↦ nomatch hlt) hA₀ htu₀
  cases l with
  | zero => exact ⟨rel, hA, h0 hA htu⟩
  | one =>
      refine ⟨rel, hA, symEqTerm_step (l := .one) ?_ ?_ hA htu⟩
      · intro _ hlt _ _ _ _ _ hA₀ htu₀
        cases hlt
        exact h0 hA₀ htu₀
      · intro _ hlt _ _ _ _ _ hA₀ hB₀ hAB₀
        cases hlt
        exact symLogRelAt (l₁ := .zero) (l₂ := .zero) hA₀ hB₀ hAB₀

/-!
## Transitivity of the Logical Relation (`Definition/LogicalRelation/Properties/Transitivity.agda`)
-/

/-- Single-level transitivity step for `LogRelAt` type equality. -/
theorem transLogRel_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A B C relA relB},
      logRelRec eqrel l l' hlt Γ A relA → LogRelShape eqrel Γ B relB →
      relA.eqType B → relB.eqType C → relA.eqType C)
    {Γ : Context} {A : Term} {relA : RedRel}
    (hA : LogRelAt eqrel l Γ A relA) :
    ∀ {B C : Term} {relB : RedRel},
      LogRelShape eqrel Γ B relB → relA.eqType B → relB.eqType C → relA.eqType C := by
  induction hA with
  | @U Γ l₁ _ =>
      intro B C relB hB hAB hBC
      change B = .univ at hAB
      subst hAB
      cases hB with
      | U _ => exact hBC
      | nat D => cases whnfRedStar D.reduction .univ
      | ne neB =>
          have h := whnfRedStar neB.D.reduction .univ
          subst h
          cases neB.neK
      | pi D => cases whnfRedStar D.reduction .univ
  | @nat Γ A _ =>
      intro B C relB hB hAB hBC
      change TypeStar Γ B .nat at hAB
      cases hB with
      | U _ => cases whnfRedStar hAB .univ
      | nat _ => exact hBC
      | ne neB =>
          have h := whrDetStar ⟨hAB, .nat⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ => cases whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .pi⟩
  | @ne Γ A K₁ _ =>
      intro B C relB hB hAB hBC
      rcases hAB with ⟨M, D', neM, KeqM⟩
      cases hB with
      | U _ =>
          have h := whnfRedStar D'.reduction .univ
          subst h
          cases neM
      | nat D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D'.reduction, .neutral neM⟩
          subst h
          cases neM
      | @ne _ _ K₂ neB =>
          have hMK₂ : M = K₂ :=
            whrDetStar ⟨D'.reduction, .neutral neM⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst hMK₂
          rcases hBC with ⟨M₁, D'', neM₁, K₂eqM₁⟩
          exact ⟨M₁, D'', neM₁, eqrel.transNe KeqM K₂eqM₁⟩
      | pi D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D'.reduction, .neutral neM⟩
          subst h
          cases neM
  | @pi Γ A F₁ G₁ _ _hF₁ _hG₁ _AeqA₁ relF₁ relG₁ _hF_ex₁ derivF₁ _hG_ex₁ _derivG₁ _Gext₁ ihF ihG =>
      intro B C relB hB hAB hBC
      rcases hAB with ⟨F', G', D', AeqB, FeqF', GeqG'⟩
      cases hB with
      | U _ => cases whnfRedStar D' .univ
      | nat D₂ => cases whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D', .pi⟩
      | ne neB =>
          have h := whrDetStar ⟨D', .pi⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | @pi l₂ _ _ F₂ G₂ D₂ _ _ _ relF₂ relG₂ _hF_ex₂ derivF₂ _hG_ex₂ derivG₂ _ =>
          have hPi : Term.pi F₂ G₂ = Term.pi F' G' :=
            whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D', .pi⟩
          injection hPi with hF₂ hG₂
          subst hF₂ hG₂
          rcases hBC with ⟨F'', G'', D'', BeqC, FeqF'', GeqG''⟩
          refine ⟨F'', G'', D'', eqrel.transType AeqB BeqC,
            fun {ρ Δ} hρ hΔ ↦ ?_,
            fun {ρ Δ a} hρ hΔ ha₁ ↦ ?_⟩
          · rcases FeqF' hρ hΔ with ⟨r₁, hr₁, hF₁₂⟩
            rcases FeqF'' hρ hΔ with ⟨r₂, hr₂, hF₂₃⟩
            have hAt₂ := derivF₂ hρ hΔ r₂ hr₂
            exact ⟨r₁, hr₁, ihF hρ hΔ r₁ hr₁ (logRelShape_of_LogRelAt hAt₂) hF₁₂ hF₂₃⟩
          · rcases FeqF' hρ hΔ with ⟨r₁, hr₁, hF₁₂⟩
            rcases FeqF'' hρ hΔ with ⟨r₂, hr₂, _⟩
            rcases ha₁ with ⟨r₁', hr₁', ha₁'⟩
            have hAt₁ := derivF₁ hρ hΔ r₁ hr₁
            have hAt₁' := derivF₁ hρ hΔ r₁' hr₁'
            have hAt₂ := derivF₂ hρ hΔ r₂ hr₂
            have ha₁_r₁ : r₁.hasTerm a := (irrelLogRel hAt₁' hAt₁).2.1.mp ha₁'
            have ha₂ : RelFHasTerm relF₂ ρ Δ a :=
              ⟨r₂, hr₂, (convLogRelAt hAt₁ hAt₂ hF₁₂).1.mp ha₁_r₁⟩
            rcases GeqG' hρ hΔ ⟨r₁', hr₁', ha₁'⟩ with ⟨s₁, hs₁, hG₁₂⟩
            rcases GeqG'' hρ hΔ ha₂ with ⟨s₂, hs₂, hG₂₃⟩
            have hGAt₂ := derivG₂ hρ hΔ ha₂ s₂ hs₂
            exact ⟨s₁, hs₁, ihG hρ hΔ ⟨r₁', hr₁', ha₁'⟩ s₁ hs₁ (logRelShape_of_LogRelAt hGAt₂) hG₁₂ hG₂₃⟩
  | @emb Γ A l' relA hlt hA =>
      intro B C relB hB hAB hBC
      exact ihRec l' hlt hA hB hAB hBC

theorem transLogRelAt {eqrel : EqRelSet} {l₁ l₂ : TypeLevel} {Γ : Context} {A B C : Term}
    {relA relB : RedRel}
    (hA : LogRelAt eqrel l₁ Γ A relA)
    (hB : LogRelAt eqrel l₂ Γ B relB)
    (hAB : relA.eqType B)
    (hBC : relB.eqType C) : relA.eqType C := by
  have h0 : ∀ {Γ A B C relA relB},
      LogRelAt eqrel .zero Γ A relA → LogRelShape eqrel Γ B relB →
      relA.eqType B → relB.eqType C → relA.eqType C :=
    fun hA₀ hBs hAB₀ hBC₀ ↦
      transLogRel_step (l := .zero) (fun _ hlt ↦ nomatch hlt) hA₀ hBs hAB₀ hBC₀
  cases l₁ with
  | zero => exact h0 hA (logRelShape_of_LogRelAt hB) hAB hBC
  | one =>
      exact transLogRel_step (l := .one)
        (fun _ hlt _ _ _ _ _ _ hA₀ hBs hAB₀ hBC₀ ↦ by cases hlt; exact h0 hA₀ hBs hAB₀ hBC₀)
        hA (logRelShape_of_LogRelAt hB) hAB hBC

/-- Transitivity of reducible type equality (`transEq`). -/
theorem transEq {eqrel : EqRelSet} {l l' l'' : TypeLevel} {Γ : Context} {A B C : Term}
    (pA : RedType eqrel l Γ A) (pB : RedType eqrel l' Γ B) (_pC : RedType eqrel l'' Γ C)
    (hAB : RedEq pA B) (hBC : RedEq pB C) : RedEq pA C := by
  rcases hAB with ⟨relA, hA, hEqB⟩
  rcases hBC with ⟨relB, hB, hEqC⟩
  exact ⟨relA, hA, transLogRelAt hA hB hEqB hEqC⟩

/-- Transitivity of reducible type equality with propositionally equal types (`transEq′`). -/
theorem transEq' {eqrel : EqRelSet} {l l' l'' : TypeLevel} {Γ : Context} {A B B' C C' : Term}
    (hBB' : B = B') (hCC' : C = C')
    (pA : RedType eqrel l Γ A) (pB : RedType eqrel l' Γ B) (pC : RedType eqrel l'' Γ C)
    (hAB' : RedEq pA B') (hBC' : RedEq pB C') : RedEq pA C := by
  subst hBB' hCC'
  exact transEq pA pB pC hAB' hBC'

theorem transEqTermNe {eqrel : EqRelSet} {Γ : Context} {n n' n'' A : Term}
    (nf₁ : RedNeNfEq eqrel Γ n n' A) (nf₂ : RedNeNfEq eqrel Γ n' n'' A) :
    RedNeNfEq eqrel Γ n n'' A :=
  ⟨nf₁.neK, nf₂.neM, eqrel.transNe nf₁.keqm nf₂.keqm⟩

theorem transEqTermNat {eqrel : EqRelSet} {Γ : Context} {n n' n'' : Term}
    (h₁ : RedNatTermEq eqrel Γ n n') (h₂ : RedNatTermEq eqrel Γ n' n'') :
    RedNatTermEq eqrel Γ n n'' :=
  @RedNatTermEq.rec eqrel Γ
    (fun n n' _ ↦ ∀ {n''}, RedNatTermEq eqrel Γ n' n'' → RedNatTermEq eqrel Γ n n'')
    (fun k k' _ ↦ ∀ {k''}, NaturalEqProp eqrel Γ k' k'' → NaturalEqProp eqrel Γ k k'')
    (fun t u k k' d d' keqk' prop ih {n''} h₂ ↦ by
      cases h₂ with
      | mk _ _ k₁ k'' d₁ d'' k₁eqk'' prop₁ =>
          have ⟨_, natK'⟩ := split_of_NaturalEqProp prop
          have ⟨natK₁, _⟩ := split_of_NaturalEqProp prop₁
          have hk₁ : k₁ = k' :=
            whrDetStarTerm ⟨d₁.reduction, natK₁.toWhnf⟩ ⟨d'.reduction, natK'.toWhnf⟩
          subst hk₁
          exact .mk t n'' k k'' d d'' (eqrel.transTerm keqk' k₁eqk'') (ih prop₁))
    (fun {a b} _ ih {k''} hk₂ ↦ by
      cases hk₂ with
      | suc h₂' => exact .suc (ih h₂')
      | ne nf => cases nf.neK)
    (fun {k''} hk₂ ↦ hk₂)
    (fun {a b} nf₁ {k''} hk₂ ↦ by
      cases hk₂ with
      | suc _ => cases nf₁.neM
      | zero => exact .ne nf₁
      | ne nf₂ => exact .ne (transEqTermNe nf₁ nf₂))
    n n' h₁ (n'' := n'') h₂

theorem transNaturalProp {eqrel : EqRelSet} {Γ : Context} {k k' k'' : Term}
    (h₁ : NaturalEqProp eqrel Γ k k') (h₂ : NaturalEqProp eqrel Γ k' k'') :
    NaturalEqProp eqrel Γ k k'' := by
  cases h₁ with
  | suc h₁' =>
      cases h₂ with
      | suc h₂' => exact .suc (transEqTermNat h₁' h₂')
      | ne nf => cases nf.neK
  | zero => exact h₂
  | ne nf₁ =>
      cases h₂ with
      | suc _ => cases nf₁.neM
      | zero => exact .ne nf₁
      | ne nf₂ => exact .ne (transEqTermNe nf₁ nf₂)

theorem transEqTerm_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A rel t u v},
      logRelRec eqrel l l' hlt Γ A rel → rel.eqTerm t u → rel.eqTerm u v → rel.eqTerm t v)
    (hTransType : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A B C relA relB relB'},
      logRelRec eqrel l l' hlt Γ A relA →
      logRelRec eqrel l l' hlt Γ B relB →
      logRelRec eqrel l l' hlt Γ B relB' →
      relA.eqType B → relB'.eqType C → relA.eqType C)
    {Γ : Context} {A : Term} {rel : RedRel}
    (hA : LogRelAt eqrel l Γ A rel) :
    ∀ {t u v : Term}, rel.eqTerm t u → rel.eqTerm u v → rel.eqTerm t v := by
  induction hA with
  | @U Γ l' hU =>
      rintro t u v
        ⟨A₀, B₀, d, d', typeA, typeB, AeqB, relt, ht, ⟨relu, hu⟩, tequ⟩
        ⟨A₁, B₁, d₁, d₁', typeA₁, typeB₁, A₁eqB₁, relu', hu', ⟨relv, hv⟩, ueqv⟩
      have hBA₁ : B₀ = A₁ :=
        whrDetStarTerm ⟨d'.reduction, typeB.toWhnf⟩ ⟨d₁.reduction, typeA₁.toWhnf⟩
      subst hBA₁
      exact ⟨A₀, B₁, d, d₁', typeA, typeB₁, eqrel.transTerm AeqB A₁eqB₁,
        relt, ht, ⟨relv, hv⟩, hTransType l' hU.lt ht hu hu' tequ ueqv⟩
  | @nat Γ A _ =>
      intro t u v htu huv
      exact transEqTermNat htu huv
  | @ne Γ A K _ =>
      rintro t u v ⟨k, m, d, d', nf₁⟩ ⟨k₁, m₁, d₁, d'', nf₂⟩
      have hk₁m : k₁ = m :=
        whrDetStarTerm ⟨d₁.reduction, .neutral nf₂.neK⟩ ⟨d'.reduction, .neutral nf₁.neM⟩
      subst hk₁m
      exact ⟨k, m₁, d, d'', transEqTermNe nf₁ nf₂⟩
  | @pi Γ A F G _ _ _ _ relF relG _ _ _ derivG _ _ihF ihG =>
      rintro t u v
        ⟨f, g, d, d', funcF, funcG, feqg, ht, _hu, appEq₁⟩
        ⟨f₁, g₁, d₁, d₁', funcF₁, funcG₁, f₁eqg₁, _hu', hv, appEq₂⟩
      have hf₁g : f₁ = g :=
        whrDetStarTerm ⟨d₁.reduction, funcF₁.toWhnf⟩ ⟨d'.reduction, funcG.toWhnf⟩
      subst hf₁g
      refine ⟨f, g₁, d, d₁', funcF, funcG₁, eqrel.transTerm feqg f₁eqg₁, ht, hv,
        fun {ρ Δ a} hρ hΔ ha ↦ ?_⟩
      rcases appEq₁ hρ hΔ ha with ⟨s₁, hs₁, hfg⟩
      rcases appEq₂ hρ hΔ ha with ⟨s₂, hs₂, hgg₁⟩
      have hGAt₁ := derivG hρ hΔ ha s₁ hs₁
      have hGAt₂ := derivG hρ hΔ ha s₂ hs₂
      have hgg₁' : s₁.eqTerm (.app (wk ρ f₁) a) (.app (wk ρ g₁) a) :=
        (irrelLogRel hGAt₂ hGAt₁).2.2.mp hgg₁
      exact ⟨s₁, hs₁, ihG hρ hΔ ha s₁ hs₁ hfg hgg₁'⟩
  | @emb Γ A l' rel hlt hA =>
      intro t u v htu huv
      exact ihRec l' hlt hA htu huv

/-- Transitivity of reducible term equality (`transEqTerm`). -/
theorem transEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u v : Term}
    (pA : RedType eqrel l Γ A)
    (htu : RedTermEq pA t u) (huv : RedTermEq pA u v) : RedTermEq pA t v := by
  rcases htu with ⟨rel, hA, htu⟩
  rcases huv with ⟨rel', hA', huv⟩
  have huv_rel : rel.eqTerm u v := (irrelLogRel hA' hA).2.2.mp huv
  have h0 : ∀ {Γ A rel t u v},
      LogRelAt eqrel .zero Γ A rel → rel.eqTerm t u → rel.eqTerm u v → rel.eqTerm t v :=
    fun hA₀ htu₀ huv₀ ↦
      transEqTerm_step (l := .zero) (fun _ hlt ↦ nomatch hlt) (fun _ hlt ↦ nomatch hlt)
        hA₀ htu₀ huv₀
  cases l with
  | zero => exact ⟨rel, hA, h0 hA htu huv_rel⟩
  | one =>
      refine ⟨rel, hA, transEqTerm_step (l := .one) ?_ ?_ hA htu huv_rel⟩
      · intro _ hlt _ _ _ _ _ _ hA₀ htu₀ huv₀
        cases hlt
        exact h0 hA₀ htu₀ huv₀
      · intro _ hlt _ _ _ _ _ _ _ hA₀ hB₀ hB₀' hAB₀ hBC₀
        cases hlt
        have hBC₀' := (irrelLogRel (l₁ := .zero) (l₂ := .zero) hB₀' hB₀).1.mp hBC₀
        exact transLogRelAt (l₁ := .zero) (l₂ := .zero) hA₀ hB₀ hAB₀ hBC₀'

/-!
## Universe Properties (`Definition/LogicalRelation/Properties/Universe.agda`)
-/

/-- Reducible terms of type `U` are reducible types at level `⁰` (`univEq`). -/
theorem univEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (pU : RedType eqrel l Γ .univ) (hA : RedTerm pU A) : RedType eqrel .zero Γ A := by
  rcases hA with ⟨rel, hU, hA⟩
  cases logRelShape_of_LogRelAt hU with
  | @U l' l₀ _ hUAt =>
      rcases hA with ⟨A₀, _d, _typeA, _AeqA, relA, hrelA⟩
      cases hUAt.lt
      exact ⟨relA, hrelA⟩
  | nat D => cases whnfRedStar D.reduction .univ
  | ne neA =>
      have h := whnfRedStar neA.D.reduction .univ
      subst h
      cases neA.neK
  | pi D => cases whnfRedStar D.reduction .univ

/-- Reducible term equality of type `U` is reducible type equality (`univEqEq`). -/
theorem univEqEq {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B : Term}
    (pU : RedType eqrel l Γ .univ) (pA : RedType eqrel l' Γ A)
    (hAB : RedTermEq pU A B) : RedEq pA B := by
  rcases hAB with ⟨rel, hU, hAB⟩
  cases logRelShape_of_LogRelAt hU with
  | @U l₁ l₀ _ hUAt =>
      rcases hAB with ⟨A₀, B₀, _d, _d', _typeA, _typeB, _AeqB, relt, ht, _hu, tequ⟩
      cases hUAt.lt
      exact irrelevanceEq ⟨relt, ht⟩ pA ⟨relt, ht, tequ⟩
  | nat D => cases whnfRedStar D.reduction .univ
  | ne neA =>
      have h := whnfRedStar neA.D.reduction .univ
      subst h
      cases neA.neK
  | pi D => cases whnfRedStar D.reduction .univ

/-!
## Neutral Properties (`Definition/LogicalRelation/Properties/Neutral.agda`)
-/

/-- Neutral reflexive types are reducible (`neu`). -/
theorem neu {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (neA : Neutral A) (hA : TypeWf Γ A) (AeqA : eqrel.NeEqRel Γ A A .univ) :
    RedType eqrel l Γ A :=
  RedType.ne ⟨A, idRedWf hA, neA, AeqA⟩

/-- Neutrally equal types are of reducible equality (`neuEq`). -/
theorem neuEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B : Term}
    (pA : RedType eqrel l Γ A) (neA : Neutral A) (neB : Neutral B)
    (hA : TypeWf Γ A) (hB : TypeWf Γ B) (AeqB : eqrel.NeEqRel Γ A B .univ) :
    RedEq pA B := by
  have neA_at : RedNeAt eqrel Γ A A := elimNeAt' (.refl hA) neA pA
  have hAt : LogRelAt eqrel l Γ A (RedNeRel eqrel Γ A) := .ne neA_at
  exact (RedEq_of_LogRelAt hAt pA).mpr ⟨B, idRedWf hB, neB, AeqB⟩

/-- Single-level neutral term / neutral term equality reflection step. -/
theorem neuLogRel_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A rel},
      logRelRec eqrel l l' hlt Γ A rel →
      (∀ {n}, Neutral n → HasType Γ n A → eqrel.NeEqRel Γ n n A → rel.hasTerm n) ∧
      (∀ {n n'}, Neutral n → Neutral n' → HasType Γ n A → HasType Γ n' A →
        eqrel.NeEqRel Γ n n' A → rel.eqTerm n n'))
    {Γ : Context} {A : Term} {rel : RedRel}
    (hA : LogRelAt eqrel l Γ A rel) :
    (∀ {n}, Neutral n → HasType Γ n A → eqrel.NeEqRel Γ n n A → rel.hasTerm n) ∧
    (∀ {n n'}, Neutral n → Neutral n' → HasType Γ n A → HasType Γ n' A →
      eqrel.NeEqRel Γ n n' A → rel.eqTerm n n') := by
  induction hA with
  | @U Γ l' hU =>
      refine ⟨?_, ?_⟩
      · intro n neN hn n_eq_n
        cases hU.lt
        exact ⟨n, idRedTermWf hn, .neutral neN, eqrel.neToTerm n_eq_n,
          ⟨RedNeRel eqrel Γ n, .ne ⟨idRedWf (.fromUniv hn), neN, n_eq_n⟩⟩⟩
      · intro n n' neN neN' hn hn' n_eq_n'
        cases hU.lt
        have n_eq_n := eqrel.transNe n_eq_n' (eqrel.symmNe n_eq_n')
        have n'_eq_n' := eqrel.transNe (eqrel.symmNe n_eq_n') n_eq_n'
        have hn_rel : LogRelAt eqrel .zero Γ n (RedNeRel eqrel Γ n) :=
          .ne ⟨idRedWf (.fromUniv hn), neN, n_eq_n⟩
        have hn'_rel : LogRelAt eqrel .zero Γ n' (RedNeRel eqrel Γ n') :=
          .ne ⟨idRedWf (.fromUniv hn'), neN', n'_eq_n'⟩
        exact ⟨n, n', idRedTermWf hn, idRedTermWf hn',
          .neutral neN, .neutral neN', eqrel.neToTerm n_eq_n',
          RedNeRel eqrel Γ n, hn_rel, ⟨RedNeRel eqrel Γ n', hn'_rel⟩,
          ⟨n', idRedWf (.fromUniv hn'), neN', n_eq_n'⟩⟩
  | @nat Γ A D =>
      have hANat : TypeEq Γ A .nat := subsetStar D.reduction
      refine ⟨?_, ?_⟩
      · intro n neN hn n_eq_n
        have hn' : HasType Γ n .nat := .conv hn hANat
        have n_eq_n' : eqrel.NeEqRel Γ n n .nat := eqrel.convNe n_eq_n hANat
        exact .mk n n (idRedTermWf hn') (eqrel.neToTerm n_eq_n')
          (.ne ⟨neN, hn', n_eq_n'⟩)
      · intro n n' neN neN' hn hn' n_eq_n'
        have hn_nat : HasType Γ n .nat := .conv hn hANat
        have hn'_nat : HasType Γ n' .nat := .conv hn' hANat
        have n_eq_n'_nat : eqrel.NeEqRel Γ n n' .nat := eqrel.convNe n_eq_n' hANat
        exact .mk n n' n n' (idRedTermWf hn_nat) (idRedTermWf hn'_nat)
          (eqrel.neToTerm n_eq_n'_nat) (.ne ⟨neN, neN', n_eq_n'_nat⟩)
  | @ne Γ A K neA =>
      have hAK : TypeEq Γ A K := subsetStar neA.D.reduction
      refine ⟨?_, ?_⟩
      · intro n neN hn n_eq_n
        have hn' : HasType Γ n K := .conv hn hAK
        exact ⟨n, idRedTermWf hn', ⟨neN, hn', eqrel.convNe n_eq_n hAK⟩⟩
      · intro n n' neN neN' hn hn' n_eq_n'
        exact ⟨n, n', idRedTermWf (.conv hn hAK), idRedTermWf (.conv hn' hAK),
          ⟨neN, neN', eqrel.convNe n_eq_n' hAK⟩⟩
  | @pi Γ A F G D _hF _hG _AeqA relF relG _hF_ex derivF hG_ex derivG Gext _ihF ihG =>
      have hAPi : TypeEq Γ A (.pi F G) := subsetStar D.reduction
      have hNeuTerm : ∀ {n}, Neutral n → HasType Γ n A → eqrel.NeEqRel Γ n n A →
          RedPiTerm eqrel Γ F G relF relG n := by
        intro n neN hn n_eq_n
        have hnPi : HasType Γ n (.pi F G) := .conv hn hAPi
        have neqPi : eqrel.NeEqRel Γ n n (.pi F G) := eqrel.convNe n_eq_n hAPi
        refine ⟨n, idRedTermWf hnPi, .neutral neN, eqrel.neToTerm neqPi,
          fun {ρ Δ a b} hρ hΔ ha hb hab ↦ ?_,
          fun {ρ Δ a} hρ hΔ ha ↦ ?_⟩
        · rcases ha with ⟨r_a, hr_a, ha_term⟩
          rcases hb with ⟨r_b, hr_b, hb_term⟩
          rcases hab with ⟨r_ab, hr_ab, hab_eq⟩
          have hFAt_a := derivF hρ hΔ r_a hr_a
          have hFAt_b := derivF hρ hΔ r_b hr_b
          have hFAt_ab := derivF hρ hΔ r_ab hr_ab
          have ha_syn : HasType Δ a (wk ρ F) :=
            escapeTerm ⟨r_a, hFAt_a⟩ ⟨r_a, hFAt_a, ha_term⟩
          have hb_syn : HasType Δ b (wk ρ F) :=
            escapeTerm ⟨r_b, hFAt_b⟩ ⟨r_b, hFAt_b, hb_term⟩
          have hab_syn : eqrel.TermEqRel Δ a b (wk ρ F) :=
            escapeTermEq ⟨r_ab, hFAt_ab⟩ ⟨r_ab, hFAt_ab, hab_eq⟩
          rcases hG_ex hρ hΔ ⟨r_a, hr_a, ha_term⟩ with ⟨s_a, hs_a⟩
          rcases hG_ex hρ hΔ ⟨r_b, hr_b, hb_term⟩ with ⟨s_b, hs_b⟩
          have hGAt_a := derivG hρ hΔ ⟨r_a, hr_a, ha_term⟩ s_a hs_a
          have hGAt_b := derivG hρ hΔ ⟨r_b, hr_b, hb_term⟩ s_b hs_b
          have hGext := Gext hρ hΔ ⟨r_a, hr_a, ha_term⟩ ⟨r_b, hr_b, hb_term⟩ ⟨r_ab, hr_ab, hab_eq⟩
          rcases hGext with ⟨s_ext, hs_ext, hGaGb⟩
          have hGAt_ext := derivG hρ hΔ ⟨r_a, hr_a, ha_term⟩ s_ext hs_ext
          have hGbGa : s_b.eqType (subst0 (wk (.lift ρ) G) a) :=
            symLogRelAt hGAt_ext hGAt_b hGaGb
          have hGbGa_syn : TypeEq Δ (subst0 (wk (.lift ρ) G) b) (subst0 (wk (.lift ρ) G) a) :=
            eqrel.typeToEq (escapeEq ⟨s_b, hGAt_b⟩ ⟨s_b, hGAt_b, hGbGa⟩)
          have hρn : HasType Δ (wk ρ n) (.pi (wk ρ F) (wk (.lift ρ) G)) :=
            wkHasType hρ hΔ hnPi
          have hAppA : HasType Δ (.app (wk ρ n) a) (subst0 (wk (.lift ρ) G) a) :=
            .app hρn ha_syn
          have hAppB : HasType Δ (.app (wk ρ n) b) (subst0 (wk (.lift ρ) G) a) :=
            .conv (.app hρn hb_syn) hGbGa_syn
          have hNeApp : eqrel.NeEqRel Δ (.app (wk ρ n) a) (.app (wk ρ n) b)
              (subst0 (wk (.lift ρ) G) a) :=
            eqrel.appCong (eqrel.wkNe hρ hΔ neqPi) hab_syn
          exact ⟨s_a, hs_a,
            (ihG hρ hΔ ⟨r_a, hr_a, ha_term⟩ s_a hs_a).2
              (.app (neN.wk ρ)) (.app (neN.wk ρ))
              hAppA hAppB hNeApp⟩
        · rcases ha with ⟨r_a, hr_a, ha_term⟩
          have hFAt_a := derivF hρ hΔ r_a hr_a
          have ha_syn : HasType Δ a (wk ρ F) :=
            escapeTerm ⟨r_a, hFAt_a⟩ ⟨r_a, hFAt_a, ha_term⟩
          have haa_syn : eqrel.TermEqRel Δ a a (wk ρ F) :=
            escapeTermEq ⟨r_a, hFAt_a⟩ (reflEqTerm ⟨r_a, hFAt_a⟩ ⟨r_a, hFAt_a, ha_term⟩)
          rcases hG_ex hρ hΔ ⟨r_a, hr_a, ha_term⟩ with ⟨s_a, hs_a⟩
          have hρn : HasType Δ (wk ρ n) (.pi (wk ρ F) (wk (.lift ρ) G)) :=
            wkHasType hρ hΔ hnPi
          have hAppA : HasType Δ (.app (wk ρ n) a) (subst0 (wk (.lift ρ) G) a) :=
            .app hρn ha_syn
          have hNeApp : eqrel.NeEqRel Δ (.app (wk ρ n) a) (.app (wk ρ n) a)
              (subst0 (wk (.lift ρ) G) a) :=
            eqrel.appCong (eqrel.wkNe hρ hΔ neqPi) haa_syn
          exact ⟨s_a, hs_a,
            (ihG hρ hΔ ⟨r_a, hr_a, ha_term⟩ s_a hs_a).1
              (.app (neN.wk ρ)) hAppA hNeApp⟩
      refine ⟨hNeuTerm, ?_⟩
      intro n n' neN neN' hn hn' n_eq_n'
      have hnPi : HasType Γ n (.pi F G) := .conv hn hAPi
      have hn'Pi : HasType Γ n' (.pi F G) := .conv hn' hAPi
      have neqPi : eqrel.NeEqRel Γ n n' (.pi F G) := eqrel.convNe n_eq_n' hAPi
      have n_eq_n : eqrel.NeEqRel Γ n n A :=
        eqrel.transNe n_eq_n' (eqrel.symmNe n_eq_n')
      have n'_eq_n' : eqrel.NeEqRel Γ n' n' A :=
        eqrel.transNe (eqrel.symmNe n_eq_n') n_eq_n'
      refine ⟨n, n', idRedTermWf hnPi, idRedTermWf hn'Pi,
        .neutral neN, .neutral neN', eqrel.neToTerm neqPi,
        hNeuTerm neN hn n_eq_n, hNeuTerm neN' hn' n'_eq_n',
        fun {ρ Δ a} hρ hΔ ha ↦ ?_⟩
      rcases ha with ⟨r_a, hr_a, ha_term⟩
      have hFAt_a := derivF hρ hΔ r_a hr_a
      have ha_syn : HasType Δ a (wk ρ F) :=
        escapeTerm ⟨r_a, hFAt_a⟩ ⟨r_a, hFAt_a, ha_term⟩
      have haa_syn : eqrel.TermEqRel Δ a a (wk ρ F) :=
        escapeTermEq ⟨r_a, hFAt_a⟩ (reflEqTerm ⟨r_a, hFAt_a⟩ ⟨r_a, hFAt_a, ha_term⟩)
      rcases hG_ex hρ hΔ ⟨r_a, hr_a, ha_term⟩ with ⟨s_a, hs_a⟩
      have hρn : HasType Δ (wk ρ n) (.pi (wk ρ F) (wk (.lift ρ) G)) := wkHasType hρ hΔ hnPi
      have hρn' : HasType Δ (wk ρ n') (.pi (wk ρ F) (wk (.lift ρ) G)) := wkHasType hρ hΔ hn'Pi
      exact ⟨s_a, hs_a,
        (ihG hρ hΔ ⟨r_a, hr_a, ha_term⟩ s_a hs_a).2
          (.app (neN.wk ρ)) (.app (neN'.wk ρ))
          (.app hρn ha_syn) (.app hρn' ha_syn)
          (eqrel.appCong (eqrel.wkNe hρ hΔ neqPi) haa_syn)⟩
  | @emb Γ A l' rel hlt hA =>
      exact ihRec l' hlt hA

theorem neuLogRelAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term} {rel : RedRel}
    (hA : LogRelAt eqrel l Γ A rel) :
    (∀ {n}, Neutral n → HasType Γ n A → eqrel.NeEqRel Γ n n A → rel.hasTerm n) ∧
    (∀ {n n'}, Neutral n → Neutral n' → HasType Γ n A → HasType Γ n' A →
      eqrel.NeEqRel Γ n n' A → rel.eqTerm n n') := by
  have h0 : ∀ {Γ A rel},
      LogRelAt eqrel .zero Γ A rel →
      (∀ {n}, Neutral n → HasType Γ n A → eqrel.NeEqRel Γ n n A → rel.hasTerm n) ∧
      (∀ {n n'}, Neutral n → Neutral n' → HasType Γ n A → HasType Γ n' A →
        eqrel.NeEqRel Γ n n' A → rel.eqTerm n n') :=
    fun hA₀ ↦ neuLogRel_step (l := .zero) (fun _ hlt ↦ nomatch hlt) hA₀
  cases l with
  | zero => exact h0 hA
  | one =>
      exact neuLogRel_step (l := .one)
        (fun _ hlt _ _ _ hA₀ ↦ by cases hlt; exact h0 hA₀) hA

/-- Neutral reflexive terms are reducible (`neuTerm`). -/
theorem neuTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A n : Term}
    (pA : RedType eqrel l Γ A) (neN : Neutral n)
    (hn : HasType Γ n A) (n_eq_n : eqrel.NeEqRel Γ n n A) : RedTerm pA n := by
  rcases pA with ⟨rel, hA⟩
  exact ⟨rel, hA, (neuLogRelAt hA).1 neN hn n_eq_n⟩

/-- Neutrally equal terms are of reducible equality (`neuEqTerm`). -/
theorem neuEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A n n' : Term}
    (pA : RedType eqrel l Γ A) (neN : Neutral n) (neN' : Neutral n')
    (hn : HasType Γ n A) (hn' : HasType Γ n' A)
    (n_eq_n' : eqrel.NeEqRel Γ n n' A) : RedTermEq pA n n' := by
  rcases pA with ⟨rel, hA⟩
  exact ⟨rel, hA, (neuLogRelAt hA).2 neN neN' hn hn' n_eq_n'⟩

/-!
## Weak Head Expansion (`Definition/LogicalRelation/Properties/Reduction.agda`)
-/

/-- Single-level weak-head expansion step for `LogRelAt` types (`redSubst*`). -/
theorem redSubstStar_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A B rel},
      TypeStar Γ A B → logRelRec eqrel l l' hlt Γ B rel →
      logRelRec eqrel l l' hlt Γ A rel ∧ rel.eqType B)
    {Γ : Context} {B : Term} {rel : RedRel}
    (hB : LogRelAt eqrel l Γ B rel) :
    ∀ {A : Term}, TypeStar Γ A B → LogRelAt eqrel l Γ A rel ∧ rel.eqType B := by
  induction hB with
  | @U Γ l' hU =>
      intro A D
      have hAU : A = .univ := redUStar D
      subst hAU
      exact ⟨.U hU, rfl⟩
  | @nat Γ B D' =>
      intro A D
      have hA : TypeWf Γ A := redFirstStar D
      exact ⟨.nat ⟨hA, D'.target, D.trans D'.reduction⟩, D'.reduction⟩
  | @ne Γ B K neB =>
      intro A D
      have hA : TypeWf Γ A := redFirstStar D
      exact ⟨.ne ⟨⟨hA, neB.D.target, D.trans neB.D.reduction⟩, neB.neK, neB.KeqK⟩,
        ⟨K, neB.D, neB.neK, neB.KeqK⟩⟩
  | @pi Γ B F G D' hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext _ihF _ihG =>
      intro A D
      have hA : TypeWf Γ A := redFirstStar D
      refine ⟨.pi ⟨hA, D'.target, D.trans D'.reduction⟩
          hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext,
        ⟨F, G, D'.reduction, AeqA,
          fun {ρ Δ} hρ hΔ ↦ ?_,
          fun {ρ Δ a} hρ hΔ ha ↦ ?_⟩⟩
      · rcases hF_ex hρ hΔ with ⟨r, hr⟩
        exact ⟨r, hr, (reflLogRelAt (derivF hρ hΔ r hr)).1⟩
      · rcases hG_ex hρ hΔ ha with ⟨s, hs⟩
        exact ⟨s, hs, (reflLogRelAt (derivG hρ hΔ ha s hs)).1⟩
  | @emb Γ B l' rel hlt hB =>
      intro A D
      rcases ihRec l' hlt D hB with ⟨hA, hEq⟩
      exact ⟨.emb hlt hA, hEq⟩

theorem redSubstStarAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B : Term} {rel : RedRel}
    (D : TypeStar Γ A B) (hB : LogRelAt eqrel l Γ B rel) :
    LogRelAt eqrel l Γ A rel ∧ rel.eqType B := by
  have h0 : ∀ {Γ A B rel}, TypeStar Γ A B → LogRelAt eqrel .zero Γ B rel →
      LogRelAt eqrel .zero Γ A rel ∧ rel.eqType B :=
    fun D₀ hB₀ ↦ redSubstStar_step (l := .zero) (fun _ hlt ↦ nomatch hlt) hB₀ D₀
  cases l with
  | zero => exact h0 D hB
  | one =>
      exact redSubstStar_step (l := .one)
        (fun _ hlt _ _ _ _ D₀ hB₀ ↦ by cases hlt; exact h0 D₀ hB₀) hB D

/-- Weak head expansion of reducible types (`redSubst*`). -/
theorem redSubstStar {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B : Term}
    (D : TypeStar Γ A B) (pB : RedType eqrel l Γ B) :
    ∃ (pA : RedType eqrel l Γ A), RedEq pA B := by
  rcases pB with ⟨rel, hB⟩
  rcases redSubstStarAt D hB with ⟨hA, hEq⟩
  exact ⟨⟨rel, hA⟩, ⟨rel, hA, hEq⟩⟩

/-- Weak head expansion of reducible terms (`redSubst*Term`). -/
theorem redSubstStarTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u : Term}
    (d_tu : Star Γ t u A) (pA : RedType eqrel l Γ A) (hu : RedTerm pA u) :
    RedTerm pA t ∧ RedTermEq pA t u := by
  rcases hu with ⟨rel, hA, hu⟩
  cases logRelShape_of_LogRelAt hA with
  | @U l' l₀ _ hU =>
      rcases hu with ⟨A₀, d, typeA, AeqA, rel_u, hrel_u⟩
      cases hU.lt
      have ht_wf : HasType Γ t .univ := redFirstStarTerm d_tu
      have d' : StarWf Γ t A₀ .univ := ⟨ht_wf, d.target, d_tu.trans d.reduction⟩
      have ⟨hrel_t, hEq_tu⟩ := redSubstStarAt (.fromUniv d_tu) hrel_u
      exact ⟨⟨_, hA, ⟨A₀, d', typeA, AeqA, ⟨rel_u, hrel_t⟩⟩⟩,
        ⟨_, hA, ⟨A₀, A₀, d', d, typeA, typeA, AeqA, rel_u, hrel_t, ⟨rel_u, hrel_u⟩, hEq_tu⟩⟩⟩
  | nat D =>
      rcases hu with ⟨_, n, d, neqn, prop⟩
      have hANat : TypeEq Γ A .nat := subsetStar D.reduction
      have ht_nat : HasType Γ t .nat := .conv (redFirstStarTerm d_tu) hANat
      have d_tu_nat : Star Γ t u .nat := d_tu.conv hANat
      have d' : StarWf Γ t n .nat := ⟨ht_nat, d.target, d_tu_nat.trans d.reduction⟩
      exact ⟨⟨_, hA, .mk t n d' neqn prop⟩,
        ⟨_, hA, .mk t u n n d' d neqn (reflNaturalProp prop)⟩⟩
  | @ne _ _ K neA =>
      rcases hu with ⟨k, d, nf⟩
      have hAK : TypeEq Γ A K := subsetStar neA.D.reduction
      have ht_K : HasType Γ t K := .conv (redFirstStarTerm d_tu) hAK
      have d_tu_K : Star Γ t u K := d_tu.conv hAK
      have d' : StarWf Γ t k K := ⟨ht_K, d.target, d_tu_K.trans d.reduction⟩
      exact ⟨⟨_, hA, ⟨k, d', nf⟩⟩,
        ⟨_, hA, ⟨k, k, d', d, ⟨nf.neK, nf.neK, nf.keqk⟩⟩⟩⟩
  | @pi l₀ _ _ F G D _hF _hG _AeqA relF relG _hF_ex _derivF _hG_ex derivG _Gext =>
      rcases hu with ⟨f, d, funcF, feqf, appEq, appTerm⟩
      have hAPi : TypeEq Γ A (.pi F G) := subsetStar D.reduction
      have ht_Pi : HasType Γ t (.pi F G) := .conv (redFirstStarTerm d_tu) hAPi
      have d_tu_Pi : Star Γ t u (.pi F G) := d_tu.conv hAPi
      have d' : StarWf Γ t f (.pi F G) := ⟨ht_Pi, d.target, d_tu_Pi.trans d.reduction⟩
      have ht_PiTerm : RedPiTerm eqrel Γ F G relF relG t :=
        ⟨f, d', funcF, feqf, appEq, appTerm⟩
      have hu_PiTerm : RedPiTerm eqrel Γ F G relF relG u :=
        ⟨f, d, funcF, feqf, appEq, appTerm⟩
      refine ⟨⟨_, hA, ht_PiTerm⟩,
        ⟨_, hA, ⟨f, f, d', d, funcF, funcF, feqf, ht_PiTerm, hu_PiTerm,
          fun {ρ Δ a} hρ hΔ ha ↦ ?_⟩⟩⟩
      rcases appTerm hρ hΔ ha with ⟨s, hs, hfa⟩
      exact ⟨s, hs, (reflLogRelAt (derivG hρ hΔ ha s hs)).2 hfa⟩

/-- Single-step weak head expansion of reducible types (`redSubst`). -/
theorem redSubst {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B : Term}
    (hAB : TypeStep Γ A B) (pB : RedType eqrel l Γ B) :
    ∃ (pA : RedType eqrel l Γ A), RedEq pA B :=
  redSubstStar (.step hAB (.refl (escape pB))) pB

/-- Single-step weak head expansion of reducible terms (`redSubstTerm`). -/
theorem redSubstTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u : Term}
    (htu : Step Γ t u A) (pA : RedType eqrel l Γ A) (hu : RedTerm pA u) :
    RedTerm pA t ∧ RedTermEq pA t u :=
  redSubstStarTerm (.step htu (.refl (escapeTerm pA hu))) pA hu

/-!
## Successor Properties (`Definition/LogicalRelation/Properties/Successor.agda`)
-/

/-- Reducible natural numbers construct reducible successors (`sucTerm`). -/
theorem sucTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {n : Term}
    (pNat : RedType eqrel l Γ .nat) (hn : RedTerm pNat n) : RedTerm pNat (.succ n) := by
  have D : RedNat Γ .nat := elimNat pNat
  have hAt : LogRelAt eqrel l Γ .nat (RedNatRel eqrel Γ) := .nat D
  have hn' : RedNatTerm eqrel Γ n := (RedTerm_of_LogRelAt hAt pNat).mp hn
  cases hn' with
  | mk _ k d keqk prop =>
      have natK := natural_of_NaturalProp prop
      have hSuccEq : eqrel.TermEqRel Γ (.succ n) (.succ n) .nat :=
        eqrel.succCong (eqrel.redTerm D.reduction d.reduction d.reduction
          .nat natK.toWhnf natK.toWhnf keqk)
      exact (RedTerm_of_LogRelAt hAt pNat).mpr
        (.mk (.succ n) (.succ n) (idRedTermWf (.succ d.source))
          hSuccEq (.suc (.mk n k d keqk prop)))

/-- Reducible natural number equality constructs reducible successor equality (`sucEqTerm`). -/
theorem sucEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {n n' : Term}
    (pNat : RedType eqrel l Γ .nat) (hnn' : RedTermEq pNat n n') :
    RedTermEq pNat (.succ n) (.succ n') := by
  have D : RedNat Γ .nat := elimNat pNat
  have hAt : LogRelAt eqrel l Γ .nat (RedNatRel eqrel Γ) := .nat D
  have hnn'' : RedNatTermEq eqrel Γ n n' := (RedTermEq_of_LogRelAt hAt pNat).mp hnn'
  cases hnn'' with
  | mk _ _ k k' d d' keqk' prop =>
      have ⟨natK, natK'⟩ := split_of_NaturalEqProp prop
      have hSuccEq : eqrel.TermEqRel Γ (.succ n) (.succ n') .nat :=
        eqrel.succCong (eqrel.redTerm D.reduction d.reduction d'.reduction
          .nat natK.toWhnf natK'.toWhnf keqk')
      exact (RedTermEq_of_LogRelAt hAt pNat).mpr
        (.mk (.succ n) (.succ n') (.succ n) (.succ n')
          (idRedTermWf (.succ d.source)) (idRedTermWf (.succ d'.source))
          hSuccEq (.suc (.mk n n' k k' d d' keqk' prop)))

/-!
## Application of Reducible Terms (`Definition/LogicalRelation/Application.agda`)
-/

/-- Application of reducible terms (`appTerm`). -/
theorem appTerm {eqrel : EqRelSet} {l l' l'' : TypeLevel} {Γ : Context} {F G t u : Term}
    (pF : RedType eqrel l'' Γ F)
    (pGu : RedType eqrel l' Γ (subst0 G u))
    (pPi : RedType eqrel l Γ (.pi F G))
    (ht : RedTerm pPi t)
    (hu : RedTerm pF u) :
    RedTerm pGu (.app t u) := by
  rcases elimPiAt' (.refl (escape pPi)) pPi with ⟨l₀, piA⟩
  have hAt : LogRelAt eqrel l₀ Γ (.pi F G)
      (RedPiRel eqrel Γ F G
        (fun ρ Δ rel ↦ LogRelAt eqrel l₀ Δ (wk ρ F) rel)
        (fun ρ Δ a rel ↦ LogRelAt eqrel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel)) :=
    .pi piA.D piA.hF piA.hG piA.AeqA
      (fun ρ Δ rel ↦ LogRelAt eqrel l₀ Δ (wk ρ F) rel)
      (fun ρ Δ a rel ↦ LogRelAt eqrel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel)
      piA.redF (fun _ _ _ h ↦ h) piA.redG (fun _ _ _ _ h ↦ h) piA.Gext
  have htPi := (RedTerm_of_LogRelAt hAt ⟨_, hAt⟩).mp (irrelevanceTerm pPi ⟨_, hAt⟩ ht)
  rcases htPi with ⟨f, d, _funcF, _feqf, _appEq, hAppTerm⟩
  have hΓ : CtxWf Γ := wfType piA.hF
  have hu' : RedTerm (piA.redF .id hΓ) u :=
    irrelevanceTerm' (wk_id F).symm pF (piA.redF .id hΓ) hu
  have hfu : RedTerm (piA.redG .id hΓ hu') (.app (wk .id f) u) :=
    hAppTerm .id hΓ hu'
  have hGeq : subst0 (wk (.lift .id) G) u = subst0 G u := by
    rw [wk_lift_id]
  have hfeq : Term.app (wk .id f) u = Term.app f u := by
    rw [wk_id]
  have hfu' : RedTerm pGu (.app f u) :=
    irrelevanceTerm'' hGeq hfeq (piA.redG .id hΓ hu') pGu hfu
  have hu_syn : HasType Γ u F := escapeTerm pF hu
  exact (redSubstStarTerm (d.reduction.app hu_syn) pGu hfu').1

/-- Application congruence of reducible terms (`app-congTerm`). -/
theorem appCongTerm {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {F G t t' u u' : Term}
    (pF : RedType eqrel l' Γ F)
    (pGu : RedType eqrel l' Γ (subst0 G u))
    (pPi : RedType eqrel l Γ (.pi F G))
    (htt' : RedTermEq pPi t t')
    (hu : RedTerm pF u)
    (hu' : RedTerm pF u')
    (huu' : RedTermEq pF u u') :
    RedTermEq pGu (.app t u) (.app t' u') := by
  rcases elimPiAt' (.refl (escape pPi)) pPi with ⟨l₀, piA⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ rel ↦ LogRelAt eqrel l₀ Δ (wk ρ F) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ a rel ↦ LogRelAt eqrel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel
  have hAt : LogRelAt eqrel l₀ Γ (.pi F G) (RedPiRel eqrel Γ F G relF₀ relG₀) :=
    .pi piA.D piA.hF piA.hG piA.AeqA relF₀ relG₀
      piA.redF (fun _ _ _ h ↦ h) piA.redG (fun _ _ _ _ h ↦ h) piA.Gext
  have pPi₀ : RedType eqrel l₀ Γ (.pi F G) := ⟨_, hAt⟩
  have htt'Pi := (RedTermEq_of_LogRelAt hAt pPi₀).mp (irrelevanceEqTerm pPi pPi₀ htt')
  rcases htt'Pi with ⟨f, g, d, d', funcF, funcG, _feqg, ht_pi, ht'_pi, hAppEq⟩
  rcases ht_pi with ⟨f', d'', funcF', feqf', appEq_f', appTerm_f'⟩
  rcases ht'_pi with ⟨g', d''', funcG', geqg', appEq_g', appTerm_g'⟩
  have hff' : f = f' :=
    whrDetStarTerm ⟨d.reduction, funcF.toWhnf⟩ ⟨d''.reduction, funcF'.toWhnf⟩
  have hgg' : g = g' :=
    whrDetStarTerm ⟨d'.reduction, funcG.toWhnf⟩ ⟨d'''.reduction, funcG'.toWhnf⟩
  subst hff' hgg'
  have hΓ : CtxWf Γ := wfType piA.hF
  have hu_id : RedTerm (piA.redF .id hΓ) u :=
    irrelevanceTerm' (wk_id F).symm pF (piA.redF .id hΓ) hu
  have hu'_id : RedTerm (piA.redF .id hΓ) u' :=
    irrelevanceTerm' (wk_id F).symm pF (piA.redF .id hΓ) hu'
  have huu'_id : RedTermEq (piA.redF .id hΓ) u u' :=
    irrelevanceEqTerm' (wk_id F).symm pF (piA.redF .id hΓ) huu'
  have hGeq_u : subst0 (wk (.lift .id) G) u = subst0 G u := by rw [wk_lift_id]
  have hGeq_u' : subst0 (wk (.lift .id) G) u' = subst0 G u' := by rw [wk_lift_id]
  have pGu' : RedType eqrel l₀ Γ (subst0 G u') :=
    irrelevance' hGeq_u' (piA.redG .id hΓ hu'_id)
  have hGu_eq_Gu' : RedEq pGu (subst0 G u') :=
    irrelevanceEq'' hGeq_u hGeq_u' (piA.redG .id hΓ hu_id) pGu
      (piA.Gext .id hΓ hu_id hu'_id huu'_id)
  have hf_term : RedTerm pPi₀ f :=
    ⟨_, hAt, ⟨f, idRedTermWf d''.target, funcF', feqf', appEq_f', appTerm_f'⟩⟩
  have hg_term : RedTerm pPi₀ g :=
    ⟨_, hAt, ⟨g, idRedTermWf d'''.target, funcG', geqg', appEq_g', appTerm_g'⟩⟩
  have hfu : RedTerm pGu (.app f u) := appTerm pF pGu pPi₀ hf_term hu
  have hgu' : RedTerm pGu' (.app g u') := appTerm pF pGu' pPi₀ hg_term hu'
  have hfu_eq_gu : RedTermEq pGu (.app f u) (.app g u) :=
    irrelevanceEqTerm'' (by rw [wk_id]) (by rw [wk_id]) hGeq_u
      (piA.redG .id hΓ hu_id) pGu (hAppEq .id hΓ hu_id)
  have hgu_eq_gu' : RedTermEq pGu (.app g u) (.app g u') :=
    irrelevanceEqTerm'' (by rw [wk_id]) (by rw [wk_id]) hGeq_u
      (piA.redG .id hΓ hu_id) pGu (appEq_g' .id hΓ hu_id hu'_id huu'_id)
  have htu_eq_fu : RedTermEq pGu (.app t u) (.app f u) :=
    (redSubstStarTerm (d.reduction.app (escapeTerm pF hu)) pGu hfu).2
  have ht'u'_eq_gu' : RedTermEq pGu' (.app t' u') (.app g u') :=
    (redSubstStarTerm (d'.reduction.app (escapeTerm pF hu')) pGu' hgu').2
  have hgu'_eq_t'u' : RedTermEq pGu (.app g u') (.app t' u') :=
    convEqTerm₂ pGu pGu' hGu_eq_Gu' (symEqTerm pGu' ht'u'_eq_gu')
  exact transEqTerm pGu (transEqTerm pGu htu_eq_fu hfu_eq_gu)
    (transEqTerm pGu hgu_eq_gu' hgu'_eq_t'u')

end LogrelMLTT