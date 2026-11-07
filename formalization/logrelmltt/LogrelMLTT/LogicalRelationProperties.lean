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
      | empty D =>
          have h := whnfRedStar D.reduction .univ
          cases h
      | unit D =>
          have h := whnfRedStar D.reduction .univ
          cases h
      | ne neB =>
          have h := whnfRedStar neB.D.reduction .univ
          subst h
          cases neB.neK
      | pi D =>
          have h := whnfRedStar D.reduction .univ
          cases h
      | sigma D =>
          have h := whnfRedStar D.reduction .univ
          cases h
      | id D =>
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
      | empty D₂ =>
          have h := whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .empty⟩
          cases h
      | unit D₂ =>
          have h := whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .unit⟩
          cases h
      | ne neB =>
          have h := whrDetStar ⟨hAB, .nat⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ =>
          have h := whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .pi⟩
          cases h
      | sigma D₂ =>
          have h := whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .sigma⟩
          cases h
      | id D₂ =>
          have h := whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .id⟩
          cases h
  | @empty Γ A D₁ =>
      intro B relB hB hAB
      change TypeStar Γ B .empty at hAB
      cases hB with
      | U _ =>
          have h := whnfRedStar hAB .univ
          cases h
      | nat D₂ =>
          have h := whrDetStar ⟨hAB, .empty⟩ ⟨D₂.reduction, .nat⟩
          cases h
      | empty _ =>
          exact ⟨fun {_} ↦ Iff.rfl, fun {_ _} ↦ Iff.rfl⟩
      | unit D₂ =>
          have h := whrDetStar ⟨hAB, .empty⟩ ⟨D₂.reduction, .unit⟩
          cases h
      | ne neB =>
          have h := whrDetStar ⟨hAB, .empty⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ =>
          have h := whrDetStar ⟨hAB, .empty⟩ ⟨D₂.reduction, .pi⟩
          cases h
      | sigma D₂ =>
          have h := whrDetStar ⟨hAB, .empty⟩ ⟨D₂.reduction, .sigma⟩
          cases h
      | id D₂ =>
          have h := whrDetStar ⟨hAB, .empty⟩ ⟨D₂.reduction, .id⟩
          cases h
  | @unit Γ A D₁ =>
      intro B relB hB hAB
      change TypeStar Γ B .unit at hAB
      cases hB with
      | U _ =>
          have h := whnfRedStar hAB .univ
          cases h
      | nat D₂ =>
          have h := whrDetStar ⟨hAB, .unit⟩ ⟨D₂.reduction, .nat⟩
          cases h
      | empty D₂ =>
          have h := whrDetStar ⟨hAB, .unit⟩ ⟨D₂.reduction, .empty⟩
          cases h
      | unit _ =>
          exact ⟨fun {_} ↦ Iff.rfl, fun {_ _} ↦ Iff.rfl⟩
      | ne neB =>
          have h := whrDetStar ⟨hAB, .unit⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ =>
          have h := whrDetStar ⟨hAB, .unit⟩ ⟨D₂.reduction, .pi⟩
          cases h
      | sigma D₂ =>
          have h := whrDetStar ⟨hAB, .unit⟩ ⟨D₂.reduction, .sigma⟩
          cases h
      | id D₂ =>
          have h := whrDetStar ⟨hAB, .unit⟩ ⟨D₂.reduction, .id⟩
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
      | empty D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .empty⟩ ⟨D'.reduction, .neutral neM⟩
          subst h
          cases neM
      | unit D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .unit⟩ ⟨D'.reduction, .neutral neM⟩
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
      | sigma D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .sigma⟩ ⟨D'.reduction, .neutral neM⟩
          subst h
          cases neM
      | id D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .id⟩ ⟨D'.reduction, .neutral neM⟩
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
      | empty D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .empty⟩ ⟨D', .pi⟩
          cases h
      | unit D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .unit⟩ ⟨D', .pi⟩
          cases h
      | ne neB =>
          have h := whrDetStar ⟨D', .pi⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | sigma D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .sigma⟩ ⟨D', .pi⟩
          cases h
      | id D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .id⟩ ⟨D', .pi⟩
          cases h
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
  | @sigma Γ A F₁ G₁ D₁ hF₁ _hG₁ _AeqA₁ relF₁ relG₁ hF_ex₁ derivF₁ hG_ex₁ derivG₁ _Gext₁ ihF ihG =>
      intro B relB hB hAB
      rcases hAB with ⟨F', G', D', AeqB, FeqF', GeqG'⟩
      cases hB with
      | U _ =>
          have h := whnfRedStar D' .univ
          cases h
      | nat D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D', .sigma⟩
          cases h
      | empty D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .empty⟩ ⟨D', .sigma⟩
          cases h
      | unit D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .unit⟩ ⟨D', .sigma⟩
          cases h
      | ne neB =>
          have h := whrDetStar ⟨D', .sigma⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D', .sigma⟩
          cases h
      | id D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .id⟩ ⟨D', .sigma⟩
          cases h
      | @sigma l₂ _ _ F₂ G₂ D₂ _ _ _ relF₂ relG₂ hF_ex₂ derivF₂ hG_ex₂ derivG₂ _ =>
          have hSigma : Term.sigma F₂ G₂ = Term.sigma F' G' :=
            whrDetStar ⟨D₂.reduction, .sigma⟩ ⟨D', .sigma⟩
          injection hSigma with hF₂ hG₂
          subst hF₂ hG₂
          have hΓ : CtxWf Γ := wfType hF₁
          have hSigmaEq : TypeEq Γ (.sigma F₁ G₁) (.sigma F₂ G₂) := eqrel.typeToEq AeqB
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
          have hSigmaTermIff : ∀ {t},
              RedSigmaTerm eqrel Γ F₁ G₁ relF₁ relG₁ t ↔ RedSigmaTerm eqrel Γ F₂ G₂ relF₂ relG₂ t := by
            intro t
            constructor
            · rintro ⟨p, d, prodP, peqp, fstTerm, sndTerm⟩
              have fstTerm₂ := (hF_conv .id hΓ).1.mp fstTerm
              have sndTerm₂ := (hG_conv .id hΓ fstTerm).1.mp sndTerm
              exact ⟨p, convStarWf d hSigmaEq, prodP, eqrel.convTerm peqp hSigmaEq,
                fstTerm₂, sndTerm₂⟩
            · rintro ⟨p, d, prodP, peqp, fstTerm₂, sndTerm₂⟩
              have fstTerm₁ := (hF_conv .id hΓ).1.mpr fstTerm₂
              have sndTerm₁ := (hG_conv .id hΓ fstTerm₁).1.mpr sndTerm₂
              exact ⟨p, convStarWf d (.symm hSigmaEq), prodP, eqrel.convTerm peqp (.symm hSigmaEq),
                fstTerm₁, sndTerm₁⟩
          refine ⟨hSigmaTermIff, ?_⟩
          intro t u
          constructor
          · rintro ⟨p, r, d, d'', prodP, prodR, peqr, ht, hu, fstP, fstR, fstEq, sndEq⟩
            exact ⟨p, r, convStarWf d hSigmaEq, convStarWf d'' hSigmaEq, prodP, prodR,
              eqrel.convTerm peqr hSigmaEq, hSigmaTermIff.mp ht, hSigmaTermIff.mp hu,
              (hF_conv .id hΓ).1.mp fstP, (hF_conv .id hΓ).1.mp fstR,
              (hF_conv .id hΓ).2.mp fstEq, (hG_conv .id hΓ fstP).2.mp sndEq⟩
          · rintro ⟨p, r, d, d'', prodP, prodR, peqr, ht, hu, fstP₂, fstR₂, fstEq₂, sndEq₂⟩
            have fstP₁ := (hF_conv .id hΓ).1.mpr fstP₂
            exact ⟨p, r, convStarWf d (.symm hSigmaEq), convStarWf d'' (.symm hSigmaEq),
              prodP, prodR, eqrel.convTerm peqr (.symm hSigmaEq),
              hSigmaTermIff.mpr ht, hSigmaTermIff.mpr hu,
              fstP₁, (hF_conv .id hΓ).1.mpr fstR₂,
              (hF_conv .id hΓ).2.mpr fstEq₂, (hG_conv .id hΓ fstP₁).2.mpr sndEq₂⟩
  | @id Γ A Ty₁ lhs₁ rhs₁ relTy₁ D₁ _AeqA₁ _derivTy₁ _hasLhs₁ _hasRhs₁ _lhsEqLhs₁ _rhsEqRhs₁ ihTy =>
      intro B relB hB hAB
      rcases hAB with ⟨Ty', lhs', rhs', D', AeqB, TyeqTy', _lhseqlhs', _rhseqrhs', lhsEqRhs_iff⟩
      cases hB with
      | U _ =>
          have h := whnfRedStar D' .univ
          cases h
      | nat D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D', .id⟩
          cases h
      | empty D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .empty⟩ ⟨D', .id⟩
          cases h
      | unit D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .unit⟩ ⟨D', .id⟩
          cases h
      | ne neB =>
          have h := whrDetStar ⟨D', .id⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D', .id⟩
          cases h
      | sigma D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .sigma⟩ ⟨D', .id⟩
          cases h
      | @id l₂ _ _ Ty₂ lhs₂ rhs₂ relTy₂ D₂ _ derivTy₂ _ _ _ _ =>
          have hId : Term.id Ty₂ lhs₂ rhs₂ = Term.id Ty' lhs' rhs' :=
            whrDetStar ⟨D₂.reduction, .id⟩ ⟨D', .id⟩
          injection hId with hTy₂ hLhs₂ hRhs₂
          subst hTy₂ hLhs₂ hRhs₂
          have hIdEq : TypeEq Γ (.id Ty₁ lhs₁ rhs₁) (.id Ty₂ lhs₂ rhs₂) := eqrel.typeToEq AeqB
          have hConvTy := ihTy (logRelShape_of_LogRelAt derivTy₂) TyeqTy'
          have hLhsEqRhs : relTy₁.eqTerm lhs₁ rhs₁ ↔ relTy₂.eqTerm lhs₂ rhs₂ :=
            lhsEqRhs_iff.trans hConvTy.2
          refine ⟨?_, ?_⟩
          · intro t
            constructor
            · rintro ⟨u, d, uequ, prop⟩
              refine ⟨u, convStarWf d hIdEq, eqrel.convTerm uequ hIdEq, ?_⟩
              cases prop with
              | rfl h => exact .rfl (hLhsEqRhs.mp h)
              | ne nf => exact .ne ⟨nf.neK, .conv nf.hk hIdEq, eqrel.convNe nf.keqk hIdEq⟩
            · rintro ⟨u, d, uequ, prop⟩
              refine ⟨u, convStarWf d (.symm hIdEq), eqrel.convTerm uequ (.symm hIdEq), ?_⟩
              cases prop with
              | rfl h => exact .rfl (hLhsEqRhs.mpr h)
              | ne nf =>
                  exact .ne ⟨nf.neK, .conv nf.hk (.symm hIdEq), eqrel.convNe nf.keqk (.symm hIdEq)⟩
          · intro t u
            constructor
            · rintro ⟨t', u', d, d'', t'equ', prop⟩
              refine ⟨t', u', convStarWf d hIdEq, convStarWf d'' hIdEq,
                eqrel.convTerm t'equ' hIdEq, ?_⟩
              cases prop with
              | rfl h => exact .rfl (hLhsEqRhs.mp h)
              | ne nf => exact .ne ⟨nf.neK, nf.neM, eqrel.convNe nf.keqm hIdEq⟩
            · rintro ⟨t', u', d, d'', t'equ', prop⟩
              refine ⟨t', u', convStarWf d (.symm hIdEq), convStarWf d'' (.symm hIdEq),
                eqrel.convTerm t'equ' (.symm hIdEq), ?_⟩
              cases prop with
              | rfl h => exact .rfl (hLhsEqRhs.mpr h)
              | ne nf => exact .ne ⟨nf.neK, nf.neM, eqrel.convNe nf.keqm (.symm hIdEq)⟩
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

theorem symEqTermEmpty {eqrel : EqRelSet} {Γ : Context} {t u : Term}
    (htu : RedEmptyTermEq eqrel Γ t u) : RedEmptyTermEq eqrel Γ u t := by
  rcases htu with ⟨k, k', d, d', keqk', nf⟩
  exact .mk k' k d' d (eqrel.symmTerm keqk') (symNeutralTerm nf)

theorem symEqTermUnit {Γ : Context} {t u : Term}
    (htu : RedUnitTermEq Γ t u) : RedUnitTermEq Γ u t := by
  rcases htu with ⟨ht, hu⟩
  exact ⟨hu, ht⟩

theorem symEqTermId {eqrel : EqRelSet} {Γ : Context} {Ty lhs rhs t u : Term} {relTy : RedRel}
    (htu : RedIdTermEq eqrel Γ Ty lhs rhs relTy t u) :
    RedIdTermEq eqrel Γ Ty lhs rhs relTy u t := by
  rcases htu with ⟨t', u', d, d', t'equ', prop⟩
  cases prop with
  | rfl h => exact .mk .rfl .rfl d' d (eqrel.symmTerm t'equ') (.rfl h)
  | ne nf => exact .mk u' t' d' d (eqrel.symmTerm t'equ') (.ne (symNeutralTerm nf))

/-- Single-level symmetry step for `LogRelAt` type and term equality. -/
theorem symLogRel_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A relA},
      logRelRec eqrel l l' hlt Γ A relA →
      (∀ {B relB}, LogRelShape eqrel Γ B relB → relA.eqType B → relB.eqType A) ∧
      (∀ {t u}, relA.eqTerm t u → relA.eqTerm u t))
    {Γ : Context} {A : Term} {relA : RedRel}
    (hA : LogRelAt eqrel l Γ A relA) :
    (∀ {B : Term} {relB : RedRel},
      LogRelShape eqrel Γ B relB → relA.eqType B → relB.eqType A) ∧
    (∀ {t u : Term}, relA.eqTerm t u → relA.eqTerm u t) := by
  induction hA with
  | @U Γ l₁ hU =>
      refine ⟨?_, ?_⟩
      · intro B relB hB hAB
        change B = .univ at hAB
        subst hAB
        cases hB with
        | U _ => rfl
        | nat D => cases whnfRedStar D.reduction .univ
        | empty D => cases whnfRedStar D.reduction .univ
        | unit D => cases whnfRedStar D.reduction .univ
        | ne neB =>
            have h := whnfRedStar neB.D.reduction .univ
            subst h
            cases neB.neK
        | pi D => cases whnfRedStar D.reduction .univ
        | sigma D => cases whnfRedStar D.reduction .univ
        | id D => cases whnfRedStar D.reduction .univ
      · rintro t u ⟨A₀, B₀, d, d', typeA, typeB, AeqB, relt, ht, ⟨relu, hu⟩, tequ⟩
        have hUs : LogRelShape eqrel Γ u relu := by
          cases hU.lt
          exact logRelShape_of_LogRelAt hu
        exact ⟨B₀, A₀, d', d, typeB, typeA, eqrel.symmTerm AeqB, relu, hu, ⟨relt, ht⟩,
          (ihRec l₁ hU.lt ht).1 hUs tequ⟩
  | @nat Γ A D₁ =>
      refine ⟨?_, fun {_ _} htu ↦ symEqTermNat htu⟩
      intro B relB hB hAB
      change TypeStar Γ B .nat at hAB
      cases hB with
      | U _ => cases whnfRedStar hAB .univ
      | nat _ => exact D₁.reduction
      | empty D₂ => cases whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .empty⟩
      | unit D₂ => cases whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .unit⟩
      | ne neB =>
          have h := whrDetStar ⟨hAB, .nat⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ => cases whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .pi⟩
      | sigma D₂ => cases whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .sigma⟩
      | id D₂ => cases whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .id⟩
  | @empty Γ A D₁ =>
      refine ⟨?_, fun {_ _} htu ↦ symEqTermEmpty htu⟩
      intro B relB hB hAB
      change TypeStar Γ B .empty at hAB
      cases hB with
      | U _ => cases whnfRedStar hAB .univ
      | nat D₂ => cases whrDetStar ⟨hAB, .empty⟩ ⟨D₂.reduction, .nat⟩
      | empty _ => exact D₁.reduction
      | unit D₂ => cases whrDetStar ⟨hAB, .empty⟩ ⟨D₂.reduction, .unit⟩
      | ne neB =>
          have h := whrDetStar ⟨hAB, .empty⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ => cases whrDetStar ⟨hAB, .empty⟩ ⟨D₂.reduction, .pi⟩
      | sigma D₂ => cases whrDetStar ⟨hAB, .empty⟩ ⟨D₂.reduction, .sigma⟩
      | id D₂ => cases whrDetStar ⟨hAB, .empty⟩ ⟨D₂.reduction, .id⟩
  | @unit Γ A D₁ =>
      refine ⟨?_, fun {_ _} htu ↦ symEqTermUnit htu⟩
      intro B relB hB hAB
      change TypeStar Γ B .unit at hAB
      cases hB with
      | U _ => cases whnfRedStar hAB .univ
      | nat D₂ => cases whrDetStar ⟨hAB, .unit⟩ ⟨D₂.reduction, .nat⟩
      | empty D₂ => cases whrDetStar ⟨hAB, .unit⟩ ⟨D₂.reduction, .empty⟩
      | unit _ => exact D₁.reduction
      | ne neB =>
          have h := whrDetStar ⟨hAB, .unit⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ => cases whrDetStar ⟨hAB, .unit⟩ ⟨D₂.reduction, .pi⟩
      | sigma D₂ => cases whrDetStar ⟨hAB, .unit⟩ ⟨D₂.reduction, .sigma⟩
      | id D₂ => cases whrDetStar ⟨hAB, .unit⟩ ⟨D₂.reduction, .id⟩
  | @ne Γ A K₁ neA =>
      refine ⟨?_, ?_⟩
      · intro B relB hB hAB
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
        | empty D₂ =>
            have h := whrDetStar ⟨D₂.reduction, .empty⟩ ⟨D'.reduction, .neutral neM⟩
            subst h
            cases neM
        | unit D₂ =>
            have h := whrDetStar ⟨D₂.reduction, .unit⟩ ⟨D'.reduction, .neutral neM⟩
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
        | sigma D₂ =>
            have h := whrDetStar ⟨D₂.reduction, .sigma⟩ ⟨D'.reduction, .neutral neM⟩
            subst h
            cases neM
        | id D₂ =>
            have h := whrDetStar ⟨D₂.reduction, .id⟩ ⟨D'.reduction, .neutral neM⟩
            subst h
            cases neM
      · rintro t u ⟨k, m, d, d', nf⟩
        exact ⟨m, k, d', d, symNeutralTerm nf⟩
  | @pi Γ A F₁ G₁ D₁ _hF₁ _hG₁ _AeqA₁ relF₁ relG₁ _hF_ex₁ derivF₁ _hG_ex₁ _derivG₁ _Gext₁ ihF ihG =>
      refine ⟨?_, ?_⟩
      · intro B relB hB hAB
        rcases hAB with ⟨F', G', D', AeqB, FeqF', GeqG'⟩
        cases hB with
        | U _ => cases whnfRedStar D' .univ
        | nat D₂ => cases whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D', .pi⟩
        | empty D₂ => cases whrDetStar ⟨D₂.reduction, .empty⟩ ⟨D', .pi⟩
        | unit D₂ => cases whrDetStar ⟨D₂.reduction, .unit⟩ ⟨D', .pi⟩
        | ne neB =>
            have h := whrDetStar ⟨D', .pi⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
            subst h
            cases neB.neK
        | sigma D₂ => cases whrDetStar ⟨D₂.reduction, .sigma⟩ ⟨D', .pi⟩
        | id D₂ => cases whrDetStar ⟨D₂.reduction, .id⟩ ⟨D', .pi⟩
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
              exact ⟨r₂, hr₂, (ihF hρ hΔ r₁ hr₁).1 (logRelShape_of_LogRelAt hAt₂) hF₁₂⟩
            · rcases FeqF' hρ hΔ with ⟨r₁, hr₁, hF₁₂⟩
              rcases ha₂ with ⟨r₂, hr₂, ha₂'⟩
              have hAt₁ := derivF₁ hρ hΔ r₁ hr₁
              have hAt₂ := derivF₂ hρ hΔ r₂ hr₂
              have ha₁ : RelFHasTerm relF₁ ρ Δ a :=
                ⟨r₁, hr₁, (convLogRelAt hAt₁ hAt₂ hF₁₂).1.mpr ha₂'⟩
              rcases GeqG' hρ hΔ ha₁ with ⟨s₁, hs₁, hG₁₂⟩
              rcases hG_ex₂ hρ hΔ ⟨r₂, hr₂, ha₂'⟩ with ⟨s₂, hs₂⟩
              have hGAt₂ := derivG₂ hρ hΔ ⟨r₂, hr₂, ha₂'⟩ s₂ hs₂
              exact ⟨s₂, hs₂, (ihG hρ hΔ ha₁ s₁ hs₁).1 (logRelShape_of_LogRelAt hGAt₂) hG₁₂⟩
      · rintro t u ⟨f, g, d, d', funcF, funcG, feqg, ht, hu, appEq⟩
        refine ⟨g, f, d', d, funcG, funcF, eqrel.symmTerm feqg, hu, ht,
          fun {ρ Δ a} hρ hΔ ha ↦ ?_⟩
        rcases appEq hρ hΔ ha with ⟨s, hs, hfg⟩
        exact ⟨s, hs, (ihG hρ hΔ ha s hs).2 hfg⟩
  | @sigma Γ A F₁ G₁ D₁ hF₁ _hG₁ _AeqA₁ relF₁ relG₁ _hF_ex₁ derivF₁ hG_ex₁ derivG₁ Gext₁ ihF ihG =>
      refine ⟨?_, ?_⟩
      · intro B relB hB hAB
        rcases hAB with ⟨F', G', D', AeqB, FeqF', GeqG'⟩
        cases hB with
        | U _ => cases whnfRedStar D' .univ
        | nat D₂ => cases whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D', .sigma⟩
        | empty D₂ => cases whrDetStar ⟨D₂.reduction, .empty⟩ ⟨D', .sigma⟩
        | unit D₂ => cases whrDetStar ⟨D₂.reduction, .unit⟩ ⟨D', .sigma⟩
        | ne neB =>
            have h := whrDetStar ⟨D', .sigma⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
            subst h
            cases neB.neK
        | pi D₂ => cases whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D', .sigma⟩
        | id D₂ => cases whrDetStar ⟨D₂.reduction, .id⟩ ⟨D', .sigma⟩
        | @sigma l₂ _ _ F₂ G₂ D₂ _ _ _ relF₂ relG₂ hF_ex₂ derivF₂ hG_ex₂ derivG₂ _ =>
            have hSigma : Term.sigma F₂ G₂ = Term.sigma F' G' :=
              whrDetStar ⟨D₂.reduction, .sigma⟩ ⟨D', .sigma⟩
            injection hSigma with hF₂ hG₂
            subst hF₂ hG₂
            refine ⟨F₁, G₁, D₁.reduction, eqrel.symmType AeqB,
              fun {ρ Δ} hρ hΔ ↦ ?_,
              fun {ρ Δ a} hρ hΔ ha₂ ↦ ?_⟩
            · rcases FeqF' hρ hΔ with ⟨r₁, hr₁, hF₁₂⟩
              rcases hF_ex₂ hρ hΔ with ⟨r₂, hr₂⟩
              have hAt₂ := derivF₂ hρ hΔ r₂ hr₂
              exact ⟨r₂, hr₂, (ihF hρ hΔ r₁ hr₁).1 (logRelShape_of_LogRelAt hAt₂) hF₁₂⟩
            · rcases FeqF' hρ hΔ with ⟨r₁, hr₁, hF₁₂⟩
              rcases ha₂ with ⟨r₂, hr₂, ha₂'⟩
              have hAt₁ := derivF₁ hρ hΔ r₁ hr₁
              have hAt₂ := derivF₂ hρ hΔ r₂ hr₂
              have ha₁ : RelFHasTerm relF₁ ρ Δ a :=
                ⟨r₁, hr₁, (convLogRelAt hAt₁ hAt₂ hF₁₂).1.mpr ha₂'⟩
              rcases GeqG' hρ hΔ ha₁ with ⟨s₁, hs₁, hG₁₂⟩
              rcases hG_ex₂ hρ hΔ ⟨r₂, hr₂, ha₂'⟩ with ⟨s₂, hs₂⟩
              have hGAt₂ := derivG₂ hρ hΔ ⟨r₂, hr₂, ha₂'⟩ s₂ hs₂
              exact ⟨s₂, hs₂, (ihG hρ hΔ ha₁ s₁ hs₁).1 (logRelShape_of_LogRelAt hGAt₂) hG₁₂⟩
      · rintro t u ⟨p, r, d, d', prodP, prodR, peqr, ht, hu, fstP, fstR, fstEq, sndEq⟩
        have hΓ : CtxWf Γ := wfType hF₁
        rcases fstEq with ⟨rF, hrF, hFstEq⟩
        have hFstSym : RelFEqTerm relF₁ .id Γ (.fst r) (.fst p) :=
          ⟨rF, hrF, (ihF .id hΓ rF hrF).2 hFstEq⟩
        rcases sndEq with ⟨sG_p, hsG_p, hSndEq_p⟩
        have hSndSym_p : sG_p.eqTerm (.snd r) (.snd p) :=
          (ihG .id hΓ fstP sG_p hsG_p).2 hSndEq_p
        rcases Gext₁ .id hΓ fstP fstR ⟨rF, hrF, hFstEq⟩ with ⟨sG_ext, hsG_ext, hG_pr⟩
        rcases hG_ex₁ .id hΓ fstR with ⟨sG_r, hsG_r⟩
        have hGAt_p := derivG₁ .id hΓ fstP sG_p hsG_p
        have hGAt_ext := derivG₁ .id hΓ fstP sG_ext hsG_ext
        have hGAt_r := derivG₁ .id hΓ fstR sG_r hsG_r
        have hSndSym_ext : sG_ext.eqTerm (.snd r) (.snd p) :=
          (irrelLogRel hGAt_p hGAt_ext).2.2.mp hSndSym_p
        have hSndSym_r : sG_r.eqTerm (.snd r) (.snd p) :=
          (convLogRelAt hGAt_ext hGAt_r hG_pr).2.mp hSndSym_ext
        exact ⟨r, p, d', d, prodR, prodP, eqrel.symmTerm peqr, hu, ht,
          fstR, fstP, hFstSym, ⟨sG_r, hsG_r, hSndSym_r⟩⟩
  | @id Γ A Ty₁ lhs₁ rhs₁ relTy₁ D₁ _AeqA₁ derivTy₁ _hasLhs₁ _hasRhs₁ _lhsEqLhs₁ _rhsEqRhs₁ ihTy =>
      refine ⟨?_, fun {_ _} htu ↦ symEqTermId htu⟩
      intro B relB hB hAB
      rcases hAB with ⟨Ty', lhs', rhs', D', AeqB, TyeqTy', lhseqlhs', rhseqrhs', lhsEqRhs_iff⟩
      cases hB with
      | U _ => cases whnfRedStar D' .univ
      | nat D₂ => cases whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D', .id⟩
      | empty D₂ => cases whrDetStar ⟨D₂.reduction, .empty⟩ ⟨D', .id⟩
      | unit D₂ => cases whrDetStar ⟨D₂.reduction, .unit⟩ ⟨D', .id⟩
      | ne neB =>
          have h := whrDetStar ⟨D', .id⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ => cases whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D', .id⟩
      | sigma D₂ => cases whrDetStar ⟨D₂.reduction, .sigma⟩ ⟨D', .id⟩
      | @id l₂ _ _ Ty₂ lhs₂ rhs₂ relTy₂ D₂ _ derivTy₂ _ _ _ _ =>
          have hId : Term.id Ty₂ lhs₂ rhs₂ = Term.id Ty' lhs' rhs' :=
            whrDetStar ⟨D₂.reduction, .id⟩ ⟨D', .id⟩
          injection hId with hTy₂ hLhs₂ hRhs₂
          subst hTy₂ hLhs₂ hRhs₂
          have hConvTy := convLogRelAt derivTy₁ derivTy₂ TyeqTy'
          exact ⟨Ty₁, lhs₁, rhs₁, D₁.reduction, eqrel.symmType AeqB,
            ihTy.1 (logRelShape_of_LogRelAt derivTy₂) TyeqTy',
            hConvTy.2.mp (ihTy.2 lhseqlhs'),
            hConvTy.2.mp (ihTy.2 rhseqrhs'),
            hConvTy.2.symm.trans (lhsEqRhs_iff.symm.trans hConvTy.2)⟩
  | @emb Γ A l' relA hlt hA =>
      exact ihRec l' hlt hA

theorem symLogRelAt_both {eqrel : EqRelSet} {l₁ : TypeLevel} {Γ : Context} {A : Term}
    {relA : RedRel} (hA : LogRelAt eqrel l₁ Γ A relA) :
    (∀ {B relB}, LogRelShape eqrel Γ B relB → relA.eqType B → relB.eqType A) ∧
    (∀ {t u}, relA.eqTerm t u → relA.eqTerm u t) := by
  have h0 : ∀ {Γ A relA},
      LogRelAt eqrel .zero Γ A relA →
      (∀ {B relB}, LogRelShape eqrel Γ B relB → relA.eqType B → relB.eqType A) ∧
      (∀ {t u}, relA.eqTerm t u → relA.eqTerm u t) :=
    fun hA₀ ↦ symLogRel_step (l := .zero) (fun _ hlt ↦ nomatch hlt) hA₀
  cases l₁ with
  | zero => exact h0 hA
  | one =>
      exact symLogRel_step (l := .one)
        (fun _ hlt _ _ _ hA₀ ↦ by cases hlt; exact h0 hA₀) hA

theorem symLogRelAt {eqrel : EqRelSet} {l₁ l₂ : TypeLevel} {Γ : Context} {A B : Term}
    {relA relB : RedRel}
    (hA : LogRelAt eqrel l₁ Γ A relA)
    (hB : LogRelAt eqrel l₂ Γ B relB)
    (hAB : relA.eqType B) : relB.eqType A :=
  (symLogRelAt_both hA).1 (logRelShape_of_LogRelAt hB) hAB

theorem symEqTermAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u : Term}
    {relA : RedRel} (hA : LogRelAt eqrel l Γ A relA)
    (htu : relA.eqTerm t u) : relA.eqTerm u t :=
  (symLogRelAt_both hA).2 htu

/-- Symmetry of reducible type equality (`symEq`). -/
theorem symEq {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B : Term}
    (pA : RedType eqrel l Γ A) (pB : RedType eqrel l' Γ B)
    (hAB : RedEq pA B) : RedEq pB A := by
  rcases hAB with ⟨relA, hA, hEqB⟩
  rcases pB with ⟨relB, hB⟩
  exact ⟨relB, hB, symLogRelAt hA hB hEqB⟩

/-- Symmetry of reducible term equality (`symEqTerm`). -/
theorem symEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u : Term}
    (pA : RedType eqrel l Γ A) (htu : RedTermEq pA t u) : RedTermEq pA u t := by
  rcases htu with ⟨rel, hA, htu⟩
  exact ⟨rel, hA, symEqTermAt hA htu⟩

/-!
## Transitivity of the Logical Relation (`Definition/LogicalRelation/Properties/Transitivity.agda`)
-/

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

theorem transEqTermEmpty {eqrel : EqRelSet} {Γ : Context} {n n' n'' : Term}
    (h₁ : RedEmptyTermEq eqrel Γ n n') (h₂ : RedEmptyTermEq eqrel Γ n' n'') :
    RedEmptyTermEq eqrel Γ n n'' := by
  rcases h₁ with ⟨k, k', d, d', keqk', nf₁⟩
  rcases h₂ with ⟨k₁, k'', d₁, d'', k₁eqk'', nf₂⟩
  have hk₁ : k₁ = k' :=
    whrDetStarTerm ⟨d₁.reduction, .neutral nf₂.neK⟩ ⟨d'.reduction, .neutral nf₁.neM⟩
  subst hk₁
  exact .mk k k'' d d'' (eqrel.transTerm keqk' k₁eqk'') (transEqTermNe nf₁ nf₂)

theorem transEqTermUnit {Γ : Context} {t u v : Term}
    (h₁ : RedUnitTermEq Γ t u) (h₂ : RedUnitTermEq Γ u v) :
    RedUnitTermEq Γ t v :=
  ⟨h₁.ht, h₂.hu⟩

theorem transEqTermId {eqrel : EqRelSet} {Γ : Context} {Ty lhs rhs t u v : Term} {relTy : RedRel}
    (h₁ : RedIdTermEq eqrel Γ Ty lhs rhs relTy t u)
    (h₂ : RedIdTermEq eqrel Γ Ty lhs rhs relTy u v) :
    RedIdTermEq eqrel Γ Ty lhs rhs relTy t v := by
  rcases h₁ with ⟨t', u', d₁, d₁', t'equ', prop₁⟩
  rcases h₂ with ⟨u₁, v', d₂, d₂', u₁eqv', prop₂⟩
  have ⟨_, idU'⟩ := split_of_RedIdTermEqProp prop₁
  have ⟨idU₁, _⟩ := split_of_RedIdTermEqProp prop₂
  have hu₁ : u₁ = u' :=
    whrDetStarTerm ⟨d₂.reduction, idU₁.toWhnf⟩ ⟨d₁'.reduction, idU'.toWhnf⟩
  subst hu₁
  have t'eqv' := eqrel.transTerm t'equ' u₁eqv'
  cases prop₁ with
  | rfl h =>
      cases prop₂ with
      | rfl _ => exact .mk .rfl .rfl d₁ d₂' t'eqv' (.rfl h)
      | ne nf₂ => cases nf₂.neK
  | ne nf₁ =>
      cases prop₂ with
      | rfl _ => cases nf₁.neM
      | ne nf₂ => exact .mk t' v' d₁ d₂' t'eqv' (.ne (transEqTermNe nf₁ nf₂))

/-- Single-level transitivity step for `LogRelAt` type and term equality. -/
theorem transLogRel_step {eqrel : EqRelSet} {l : TypeLevel}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A relA},
      logRelRec eqrel l l' hlt Γ A relA →
      (∀ {B C relB}, LogRelShape eqrel Γ B relB → relA.eqType B → relB.eqType C → relA.eqType C) ∧
      (∀ {t u v}, relA.eqTerm t u → relA.eqTerm u v → relA.eqTerm t v))
    {Γ : Context} {A : Term} {relA : RedRel}
    (hA : LogRelAt eqrel l Γ A relA) :
    (∀ {B C : Term} {relB : RedRel},
      LogRelShape eqrel Γ B relB → relA.eqType B → relB.eqType C → relA.eqType C) ∧
    (∀ {t u v : Term}, relA.eqTerm t u → relA.eqTerm u v → relA.eqTerm t v) := by
  induction hA with
  | @U Γ l₁ hU =>
      refine ⟨?_, ?_⟩
      · intro B C relB hB hAB hBC
        change B = .univ at hAB
        subst hAB
        cases hB with
        | U _ => exact hBC
        | nat D => cases whnfRedStar D.reduction .univ
        | empty D => cases whnfRedStar D.reduction .univ
        | unit D => cases whnfRedStar D.reduction .univ
        | ne neB =>
            have h := whnfRedStar neB.D.reduction .univ
            subst h
            cases neB.neK
        | pi D => cases whnfRedStar D.reduction .univ
        | sigma D => cases whnfRedStar D.reduction .univ
        | id D => cases whnfRedStar D.reduction .univ
      · rintro t u v
          ⟨A₀, B₀, d, d', typeA, typeB, AeqB, relt, ht, ⟨relu, hu⟩, tequ⟩
          ⟨A₁, B₁, d₁, d₁', typeA₁, typeB₁, A₁eqB₁, relu', hu', ⟨relv, hv⟩, ueqv⟩
        have hBA₁ : B₀ = A₁ :=
          whrDetStarTerm ⟨d'.reduction, typeB.toWhnf⟩ ⟨d₁.reduction, typeA₁.toWhnf⟩
        subst hBA₁
        have hTrans : relt.eqType v := by
          cases hU.lt
          have ueqv' : relu.eqType v :=
            (irrelLogRel (l₁ := .zero) (l₂ := .zero) hu' hu).1.mp ueqv
          exact (ihRec .zero .zeroLT ht).1 (logRelShape_of_LogRelAt hu) tequ ueqv'
        exact ⟨A₀, B₁, d, d₁', typeA, typeB₁, eqrel.transTerm AeqB A₁eqB₁,
          relt, ht, ⟨relv, hv⟩, hTrans⟩
  | @nat Γ A _ =>
      refine ⟨?_, fun {_ _ _} htu huv ↦ transEqTermNat htu huv⟩
      intro B C relB hB hAB hBC
      change TypeStar Γ B .nat at hAB
      cases hB with
      | U _ => cases whnfRedStar hAB .univ
      | nat _ => exact hBC
      | empty D₂ => cases whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .empty⟩
      | unit D₂ => cases whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .unit⟩
      | ne neB =>
          have h := whrDetStar ⟨hAB, .nat⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ => cases whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .pi⟩
      | sigma D₂ => cases whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .sigma⟩
      | id D₂ => cases whrDetStar ⟨hAB, .nat⟩ ⟨D₂.reduction, .id⟩
  | @empty Γ A _ =>
      refine ⟨?_, fun {_ _ _} htu huv ↦ transEqTermEmpty htu huv⟩
      intro B C relB hB hAB hBC
      change TypeStar Γ B .empty at hAB
      cases hB with
      | U _ => cases whnfRedStar hAB .univ
      | nat D₂ => cases whrDetStar ⟨hAB, .empty⟩ ⟨D₂.reduction, .nat⟩
      | empty _ => exact hBC
      | unit D₂ => cases whrDetStar ⟨hAB, .empty⟩ ⟨D₂.reduction, .unit⟩
      | ne neB =>
          have h := whrDetStar ⟨hAB, .empty⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ => cases whrDetStar ⟨hAB, .empty⟩ ⟨D₂.reduction, .pi⟩
      | sigma D₂ => cases whrDetStar ⟨hAB, .empty⟩ ⟨D₂.reduction, .sigma⟩
      | id D₂ => cases whrDetStar ⟨hAB, .empty⟩ ⟨D₂.reduction, .id⟩
  | @unit Γ A _ =>
      refine ⟨?_, fun {_ _ _} htu huv ↦ transEqTermUnit htu huv⟩
      intro B C relB hB hAB hBC
      change TypeStar Γ B .unit at hAB
      cases hB with
      | U _ => cases whnfRedStar hAB .univ
      | nat D₂ => cases whrDetStar ⟨hAB, .unit⟩ ⟨D₂.reduction, .nat⟩
      | empty D₂ => cases whrDetStar ⟨hAB, .unit⟩ ⟨D₂.reduction, .empty⟩
      | unit _ => exact hBC
      | ne neB =>
          have h := whrDetStar ⟨hAB, .unit⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ => cases whrDetStar ⟨hAB, .unit⟩ ⟨D₂.reduction, .pi⟩
      | sigma D₂ => cases whrDetStar ⟨hAB, .unit⟩ ⟨D₂.reduction, .sigma⟩
      | id D₂ => cases whrDetStar ⟨hAB, .unit⟩ ⟨D₂.reduction, .id⟩
  | @ne Γ A K₁ _ =>
      refine ⟨?_, ?_⟩
      · intro B C relB hB hAB hBC
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
        | empty D₂ =>
            have h := whrDetStar ⟨D₂.reduction, .empty⟩ ⟨D'.reduction, .neutral neM⟩
            subst h
            cases neM
        | unit D₂ =>
            have h := whrDetStar ⟨D₂.reduction, .unit⟩ ⟨D'.reduction, .neutral neM⟩
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
        | sigma D₂ =>
            have h := whrDetStar ⟨D₂.reduction, .sigma⟩ ⟨D'.reduction, .neutral neM⟩
            subst h
            cases neM
        | id D₂ =>
            have h := whrDetStar ⟨D₂.reduction, .id⟩ ⟨D'.reduction, .neutral neM⟩
            subst h
            cases neM
      · rintro t u v ⟨k, m, d, d', nf₁⟩ ⟨k₁, m₁, d₁, d'', nf₂⟩
        have hk₁m : k₁ = m :=
          whrDetStarTerm ⟨d₁.reduction, .neutral nf₂.neK⟩ ⟨d'.reduction, .neutral nf₁.neM⟩
        subst hk₁m
        exact ⟨k, m₁, d, d'', transEqTermNe nf₁ nf₂⟩
  | @pi Γ A F₁ G₁ _ _hF₁ _hG₁ _AeqA₁ relF₁ relG₁ _hF_ex₁ derivF₁ _hG_ex₁ derivG₁ _Gext₁ ihF ihG =>
      refine ⟨?_, ?_⟩
      · intro B C relB hB hAB hBC
        rcases hAB with ⟨F', G', D', AeqB, FeqF', GeqG'⟩
        cases hB with
        | U _ => cases whnfRedStar D' .univ
        | nat D₂ => cases whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D', .pi⟩
        | empty D₂ => cases whrDetStar ⟨D₂.reduction, .empty⟩ ⟨D', .pi⟩
        | unit D₂ => cases whrDetStar ⟨D₂.reduction, .unit⟩ ⟨D', .pi⟩
        | ne neB =>
            have h := whrDetStar ⟨D', .pi⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
            subst h
            cases neB.neK
        | sigma D₂ => cases whrDetStar ⟨D₂.reduction, .sigma⟩ ⟨D', .pi⟩
        | id D₂ => cases whrDetStar ⟨D₂.reduction, .id⟩ ⟨D', .pi⟩
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
              exact ⟨r₁, hr₁, (ihF hρ hΔ r₁ hr₁).1 (logRelShape_of_LogRelAt hAt₂) hF₁₂ hF₂₃⟩
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
              exact ⟨s₁, hs₁, (ihG hρ hΔ ⟨r₁', hr₁', ha₁'⟩ s₁ hs₁).1 (logRelShape_of_LogRelAt hGAt₂) hG₁₂ hG₂₃⟩
      · rintro t u v
          ⟨f, g, d, d', funcF, funcG, feqg, ht, _hu, appEq₁⟩
          ⟨f₁, g₁, d₁, d₁', funcF₁, funcG₁, f₁eqg₁, _hu', hv, appEq₂⟩
        have hf₁g : f₁ = g :=
          whrDetStarTerm ⟨d₁.reduction, funcF₁.toWhnf⟩ ⟨d'.reduction, funcG.toWhnf⟩
        subst hf₁g
        refine ⟨f, g₁, d, d₁', funcF, funcG₁, eqrel.transTerm feqg f₁eqg₁, ht, hv,
          fun {ρ Δ a} hρ hΔ ha ↦ ?_⟩
        rcases appEq₁ hρ hΔ ha with ⟨s₁, hs₁, hfg⟩
        rcases appEq₂ hρ hΔ ha with ⟨s₂, hs₂, hgg₁⟩
        have hGAt₁ := derivG₁ hρ hΔ ha s₁ hs₁
        have hGAt₂ := derivG₁ hρ hΔ ha s₂ hs₂
        have hgg₁' : s₁.eqTerm (.app (wk ρ f₁) a) (.app (wk ρ g₁) a) :=
          (irrelLogRel hGAt₂ hGAt₁).2.2.mp hgg₁
        exact ⟨s₁, hs₁, (ihG hρ hΔ ha s₁ hs₁).2 hfg hgg₁'⟩
  | @sigma Γ A F₁ G₁ _ hF₁ _hG₁ _AeqA₁ relF₁ relG₁ _hF_ex₁ derivF₁ _hG_ex₁ derivG₁ Gext₁ ihF ihG =>
      refine ⟨?_, ?_⟩
      · intro B C relB hB hAB hBC
        rcases hAB with ⟨F', G', D', AeqB, FeqF', GeqG'⟩
        cases hB with
        | U _ => cases whnfRedStar D' .univ
        | nat D₂ => cases whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D', .sigma⟩
        | empty D₂ => cases whrDetStar ⟨D₂.reduction, .empty⟩ ⟨D', .sigma⟩
        | unit D₂ => cases whrDetStar ⟨D₂.reduction, .unit⟩ ⟨D', .sigma⟩
        | ne neB =>
            have h := whrDetStar ⟨D', .sigma⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
            subst h
            cases neB.neK
        | pi D₂ => cases whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D', .sigma⟩
        | id D₂ => cases whrDetStar ⟨D₂.reduction, .id⟩ ⟨D', .sigma⟩
        | @sigma l₂ _ _ F₂ G₂ D₂ _ _ _ relF₂ relG₂ _hF_ex₂ derivF₂ _hG_ex₂ derivG₂ _ =>
            have hSigma : Term.sigma F₂ G₂ = Term.sigma F' G' :=
              whrDetStar ⟨D₂.reduction, .sigma⟩ ⟨D', .sigma⟩
            injection hSigma with hF₂ hG₂
            subst hF₂ hG₂
            rcases hBC with ⟨F'', G'', D'', BeqC, FeqF'', GeqG''⟩
            refine ⟨F'', G'', D'', eqrel.transType AeqB BeqC,
              fun {ρ Δ} hρ hΔ ↦ ?_,
              fun {ρ Δ a} hρ hΔ ha₁ ↦ ?_⟩
            · rcases FeqF' hρ hΔ with ⟨r₁, hr₁, hF₁₂⟩
              rcases FeqF'' hρ hΔ with ⟨r₂, hr₂, hF₂₃⟩
              have hAt₂ := derivF₂ hρ hΔ r₂ hr₂
              exact ⟨r₁, hr₁, (ihF hρ hΔ r₁ hr₁).1 (logRelShape_of_LogRelAt hAt₂) hF₁₂ hF₂₃⟩
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
              exact ⟨s₁, hs₁, (ihG hρ hΔ ⟨r₁', hr₁', ha₁'⟩ s₁ hs₁).1 (logRelShape_of_LogRelAt hGAt₂) hG₁₂ hG₂₃⟩
      · rintro t u v
          ⟨p, r, d, d', prodP, prodR, peqr, ht, _hu, fstP, fstR, fstEq₁, sndEq₁⟩
          ⟨p₁, r₁, d₁, d₁', prodP₁, prodR₁, p₁eqr₁, _hu', hv, fstP₁, _fstR₁, fstEq₂, sndEq₂⟩
        have hp₁r : p₁ = r :=
          whrDetStarTerm ⟨d₁.reduction, prodP₁.toWhnf⟩ ⟨d'.reduction, prodR.toWhnf⟩
        subst hp₁r
        have hΓ : CtxWf Γ := wfType hF₁
        rcases fstEq₁ with ⟨rF₁, hrF₁, hFstEq₁⟩
        rcases fstEq₂ with ⟨rF₂, hrF₂, hFstEq₂⟩
        have hFAt₁ := derivF₁ .id hΓ rF₁ hrF₁
        have hFAt₂ := derivF₁ .id hΓ rF₂ hrF₂
        have hFstEq₂' : rF₁.eqTerm (.fst p₁) (.fst r₁) :=
          (irrelLogRel hFAt₂ hFAt₁).2.2.mp hFstEq₂
        have hFstTrans : RelFEqTerm relF₁ .id Γ (.fst p) (.fst r₁) :=
          ⟨rF₁, hrF₁, (ihF .id hΓ rF₁ hrF₁).2 hFstEq₁ hFstEq₂'⟩
        rcases sndEq₁ with ⟨sG₁, hsG₁, hSndEq₁⟩
        rcases sndEq₂ with ⟨sG₂, hsG₂, hSndEq₂⟩
        rcases Gext₁ .id hΓ fstP fstR ⟨rF₁, hrF₁, hFstEq₁⟩ with ⟨sG_ext, hsG_ext, hG_pr⟩
        have hGAt₁ := derivG₁ .id hΓ fstP sG₁ hsG₁
        have hGAt_ext := derivG₁ .id hΓ fstP sG_ext hsG_ext
        have hGAt₂ := derivG₁ .id hΓ fstP₁ sG₂ hsG₂
        have hSndEq₂_ext : sG_ext.eqTerm (.snd p₁) (.snd r₁) :=
          (convLogRelAt hGAt_ext hGAt₂ hG_pr).2.mpr hSndEq₂
        have hSndEq₂_p : sG₁.eqTerm (.snd p₁) (.snd r₁) :=
          (irrelLogRel hGAt_ext hGAt₁).2.2.mp hSndEq₂_ext
        have hSndTrans : RelGEqTerm relG₁ .id Γ (.fst p) (.snd p) (.snd r₁) :=
          ⟨sG₁, hsG₁, (ihG .id hΓ fstP sG₁ hsG₁).2 hSndEq₁ hSndEq₂_p⟩
        exact ⟨p, r₁, d, d₁', prodP, prodR₁, eqrel.transTerm peqr p₁eqr₁, ht, hv,
          fstP, _fstR₁, hFstTrans, hSndTrans⟩
  | @id Γ A Ty₁ lhs₁ rhs₁ relTy₁ _D₁ _AeqA₁ derivTy₁ _hasLhs₁ _hasRhs₁ _lhsEqLhs₁ _rhsEqRhs₁ ihTy =>
      refine ⟨?_, fun {_ _ _} htu huv ↦ transEqTermId htu huv⟩
      intro B C relB hB hAB hBC
      rcases hAB with ⟨Ty', lhs', rhs', D', AeqB, TyeqTy', lhseqlhs', rhseqrhs', lhsEqRhs_iff⟩
      cases hB with
      | U _ => cases whnfRedStar D' .univ
      | nat D₂ => cases whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D', .id⟩
      | empty D₂ => cases whrDetStar ⟨D₂.reduction, .empty⟩ ⟨D', .id⟩
      | unit D₂ => cases whrDetStar ⟨D₂.reduction, .unit⟩ ⟨D', .id⟩
      | ne neB =>
          have h := whrDetStar ⟨D', .id⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ => cases whrDetStar ⟨D₂.reduction, .pi⟩ ⟨D', .id⟩
      | sigma D₂ => cases whrDetStar ⟨D₂.reduction, .sigma⟩ ⟨D', .id⟩
      | @id l₂ _ _ Ty₂ lhs₂ rhs₂ relTy₂ D₂ _ derivTy₂ _ _ _ _ =>
          have hId : Term.id Ty₂ lhs₂ rhs₂ = Term.id Ty' lhs' rhs' :=
            whrDetStar ⟨D₂.reduction, .id⟩ ⟨D', .id⟩
          injection hId with hTy₂ hLhs₂ hRhs₂
          subst hTy₂ hLhs₂ hRhs₂
          rcases hBC with ⟨Ty'', lhs'', rhs'', D'', BeqC, Ty₂eqTy'', lhs₂eqlhs'', rhs₂eqrhs'', lhsEqRhs_iff₂⟩
          have hConvTy := convLogRelAt derivTy₁ derivTy₂ TyeqTy'
          exact ⟨Ty'', lhs'', rhs'', D'', eqrel.transType AeqB BeqC,
            ihTy.1 (logRelShape_of_LogRelAt derivTy₂) TyeqTy' Ty₂eqTy'',
            ihTy.2 lhseqlhs' (hConvTy.2.mpr lhs₂eqlhs''),
            ihTy.2 rhseqrhs' (hConvTy.2.mpr rhs₂eqrhs''),
            lhsEqRhs_iff.trans (hConvTy.2.trans (lhsEqRhs_iff₂.trans hConvTy.2.symm))⟩
  | @emb Γ A l' relA hlt hA =>
      exact ihRec l' hlt hA

theorem transLogRelAt_both {eqrel : EqRelSet} {l₁ : TypeLevel} {Γ : Context} {A : Term}
    {relA : RedRel} (hA : LogRelAt eqrel l₁ Γ A relA) :
    (∀ {B C relB}, LogRelShape eqrel Γ B relB → relA.eqType B → relB.eqType C → relA.eqType C) ∧
    (∀ {t u v}, relA.eqTerm t u → relA.eqTerm u v → relA.eqTerm t v) := by
  have h0 : ∀ {Γ A relA},
      LogRelAt eqrel .zero Γ A relA →
      (∀ {B C relB}, LogRelShape eqrel Γ B relB → relA.eqType B → relB.eqType C → relA.eqType C) ∧
      (∀ {t u v}, relA.eqTerm t u → relA.eqTerm u v → relA.eqTerm t v) :=
    fun hA₀ ↦ transLogRel_step (l := .zero) (fun _ hlt ↦ nomatch hlt) hA₀
  cases l₁ with
  | zero => exact h0 hA
  | one =>
      exact transLogRel_step (l := .one)
        (fun _ hlt _ _ _ hA₀ ↦ by cases hlt; exact h0 hA₀) hA

theorem transLogRelAt {eqrel : EqRelSet} {l₁ l₂ : TypeLevel} {Γ : Context} {A B C : Term}
    {relA relB : RedRel}
    (hA : LogRelAt eqrel l₁ Γ A relA)
    (hB : LogRelAt eqrel l₂ Γ B relB)
    (hAB : relA.eqType B)
    (hBC : relB.eqType C) : relA.eqType C :=
  (transLogRelAt_both hA).1 (logRelShape_of_LogRelAt hB) hAB hBC

theorem transEqTermAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u v : Term}
    {relA : RedRel} (hA : LogRelAt eqrel l Γ A relA)
    (htu : relA.eqTerm t u) (huv : relA.eqTerm u v) : relA.eqTerm t v :=
  (transLogRelAt_both hA).2 htu huv

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

/-- Transitivity of reducible term equality (`transEqTerm`). -/
theorem transEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u v : Term}
    (pA : RedType eqrel l Γ A)
    (htu : RedTermEq pA t u) (huv : RedTermEq pA u v) : RedTermEq pA t v := by
  rcases htu with ⟨rel, hA, htu⟩
  rcases huv with ⟨rel', hA', huv⟩
  have huv_rel : rel.eqTerm u v := (irrelLogRel hA' hA).2.2.mp huv
  exact ⟨rel, hA, transEqTermAt hA htu huv_rel⟩

/-- Smart constructor for `RedIdEq` deriving `lhsEqRhs_iff` from symmetry and transitivity (`Id₌′`). -/
theorem RedIdEq.ofTermEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context}
    {Ty lhs rhs B Ty' lhs' rhs' : Term} {relTy : RedRel}
    (hTy : LogRelAt eqrel l Γ Ty relTy)
    (D' : TypeStar Γ B (.id Ty' lhs' rhs'))
    (AeqB : eqrel.TypeEqRel Γ (.id Ty lhs rhs) (.id Ty' lhs' rhs'))
    (TyeqTy' : relTy.eqType Ty')
    (lhseqlhs' : relTy.eqTerm lhs lhs')
    (rhseqrhs' : relTy.eqTerm rhs rhs') :
    RedIdEq eqrel Γ Ty lhs rhs relTy B :=
  ⟨Ty', lhs', rhs', D', AeqB, TyeqTy', lhseqlhs', rhseqrhs',
    ⟨fun h ↦ transEqTermAt hTy (transEqTermAt hTy (symEqTermAt hTy lhseqlhs') h) rhseqrhs',
     fun h' ↦ transEqTermAt hTy lhseqlhs' (transEqTermAt hTy h' (symEqTermAt hTy rhseqrhs'))⟩⟩

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

theorem wkTermEmpty {eqrel : EqRelSet} {ρ : Wk} {Γ Δ : Context} {t : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (ht : RedEmptyTerm eqrel Γ t) :
    RedEmptyTerm eqrel Δ (wk ρ t) := by
  rcases ht with ⟨n, d, neqn, prop⟩
  exact ⟨wk ρ n, wkStarWf hρ hΔ d, eqrel.wkTerm hρ hΔ neqn, wkTermNe hρ hΔ prop⟩

theorem wkEqTermEmpty {eqrel : EqRelSet} {ρ : Wk} {Γ Δ : Context} {t u : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (htu : RedEmptyTermEq eqrel Γ t u) :
    RedEmptyTermEq eqrel Δ (wk ρ t) (wk ρ u) := by
  rcases htu with ⟨k, k', d, d', keqk', prop⟩
  exact ⟨wk ρ k, wk ρ k', wkStarWf hρ hΔ d, wkStarWf hρ hΔ d',
    eqrel.wkTerm hρ hΔ keqk', wkEqTermNe hρ hΔ prop⟩

theorem wkTermUnit {ρ : Wk} {Γ Δ : Context} {t : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (ht : RedUnitTerm Γ t) :
    RedUnitTerm Δ (wk ρ t) := by
  rcases ht with ⟨n, d, prop⟩
  exact ⟨wk ρ n, wkStarWf hρ hΔ d, prop.wk ρ⟩

theorem wkEqTermUnit {ρ : Wk} {Γ Δ : Context} {t u : Term}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (htu : RedUnitTermEq Γ t u) :
    RedUnitTermEq Δ (wk ρ t) (wk ρ u) :=
  ⟨wkHasType hρ hΔ htu.ht, wkHasType hρ hΔ htu.hu⟩

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
  | @empty Γ A D =>
      intro ρ Δ hρ hΔ
      refine ⟨RedEmptyRel eqrel Δ, .empty (wkTypeStarWf hρ hΔ D), ?_, ?_, ?_⟩
      · intro B hB
        exact wkTypeStar hρ hΔ hB
      · intro t ht
        exact wkTermEmpty hρ hΔ ht
      · intro t u htu
        exact wkEqTermEmpty hρ hΔ htu
  | @unit Γ A D =>
      intro ρ Δ hρ hΔ
      refine ⟨RedUnitRel Δ, .unit (wkTypeStarWf hρ hΔ D), ?_, ?_, ?_⟩
      · intro B hB
        exact wkTypeStar hρ hΔ hB
      · intro t ht
        exact wkTermUnit hρ hΔ ht
      · intro t u htu
        exact wkEqTermUnit hρ hΔ htu
  | @sigma Γ A F G D hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext ihF ihG =>
      intro ρ Δ hρ hΔ
      have hΓ : CtxWf Γ := wfType hF
      have hρF : TypeWf Δ (wk ρ F) := wkTypeWf hρ hΔ hF
      have hρG : TypeWf (wk ρ F :: Δ) (wk (.lift ρ) G) :=
        wkTypeWf (.lift hρ) (.cons hΔ hρF) hG
      let relF' : Wk → Context → RedRel → Prop :=
        fun ρ₁ Δ₁ rel ↦ relF (compWk ρ₁ ρ) Δ₁ rel
      let relG' : Wk → Context → Term → RedRel → Prop :=
        fun ρ₁ Δ₁ a rel ↦ relG (compWk ρ₁ ρ) Δ₁ a rel
      have hF_wk_hasTerm : ∀ {a},
          RelFHasTerm relF .id Γ a → RelFHasTerm relF' .id Δ (wk ρ a) := by
        rintro a ⟨r₀, hr₀, ha⟩
        rcases ihF .id hΓ r₀ hr₀ hρ hΔ with ⟨r₀', hAt₀', _, hTerm₀', _⟩
        rw [wk_id] at hAt₀'
        rcases hF_ex hρ hΔ with ⟨r₁, hr₁⟩
        have hAt₁ := derivF hρ hΔ r₁ hr₁
        exact ⟨r₁, hr₁, (irrelLogRel hAt₀' hAt₁).2.1.mp (hTerm₀' ha)⟩
      have hF_wk_eqTerm : ∀ {a b},
          RelFEqTerm relF .id Γ a b → RelFEqTerm relF' .id Δ (wk ρ a) (wk ρ b) := by
        rintro a b ⟨r₀, hr₀, hab⟩
        rcases ihF .id hΓ r₀ hr₀ hρ hΔ with ⟨r₀', hAt₀', _, _, hEqTerm₀'⟩
        rw [wk_id] at hAt₀'
        rcases hF_ex hρ hΔ with ⟨r₁, hr₁⟩
        have hAt₁ := derivF hρ hΔ r₁ hr₁
        exact ⟨r₁, hr₁, (irrelLogRel hAt₀' hAt₁).2.2.mp (hEqTerm₀' hab)⟩
      have hG_wk_hasTerm : ∀ {a u} (ha : RelFHasTerm relF .id Γ a),
          RelGHasTerm relG .id Γ a u → RelGHasTerm relG' .id Δ (wk ρ a) (wk ρ u) := by
        rintro a u ha ⟨s₀, hs₀, hu⟩
        rcases ihG .id hΓ ha s₀ hs₀ hρ hΔ with ⟨s₀', hGAt₀', _, hGTerm₀', _⟩
        have hG_eq : wk ρ (subst0 (wk (.lift .id) G) a) = subst0 (wk (.lift ρ) G) (wk ρ a) := by
          rw [wk_lift_id, wk_beta]
        rw [hG_eq] at hGAt₀'
        have ha' : RelFHasTerm relF ρ Δ (wk ρ a) := hF_wk_hasTerm ha
        rcases hG_ex hρ hΔ ha' with ⟨s₁, hs₁⟩
        have hGAt₁ := derivG hρ hΔ ha' s₁ hs₁
        exact ⟨s₁, hs₁, (irrelLogRel hGAt₀' hGAt₁).2.1.mp (hGTerm₀' hu)⟩
      have hG_wk_eqTerm : ∀ {a u v} (ha : RelFHasTerm relF .id Γ a),
          RelGEqTerm relG .id Γ a u v → RelGEqTerm relG' .id Δ (wk ρ a) (wk ρ u) (wk ρ v) := by
        rintro a u v ha ⟨s₀, hs₀, huv⟩
        rcases ihG .id hΓ ha s₀ hs₀ hρ hΔ with ⟨s₀', hGAt₀', _, _, hGEqTerm₀'⟩
        have hG_eq : wk ρ (subst0 (wk (.lift .id) G) a) = subst0 (wk (.lift ρ) G) (wk ρ a) := by
          rw [wk_lift_id, wk_beta]
        rw [hG_eq] at hGAt₀'
        have ha' : RelFHasTerm relF ρ Δ (wk ρ a) := hF_wk_hasTerm ha
        rcases hG_ex hρ hΔ ha' with ⟨s₁, hs₁⟩
        have hGAt₁ := derivG hρ hΔ ha' s₁ hs₁
        exact ⟨s₁, hs₁, (irrelLogRel hGAt₀' hGAt₁).2.2.mp (hGEqTerm₀' huv)⟩
      have hSigmaTerm : ∀ {t},
          RedSigmaTerm eqrel Γ F G relF relG t →
          RedSigmaTerm eqrel Δ (wk ρ F) (wk (.lift ρ) G) relF' relG' (wk ρ t) := by
        rintro t ⟨p, d, prodP, peqp, fstTerm, sndTerm⟩
        exact ⟨wk ρ p, wkStarWf hρ hΔ d, prodP.wk ρ, eqrel.wkTerm hρ hΔ peqp,
          hF_wk_hasTerm fstTerm, hG_wk_hasTerm fstTerm sndTerm⟩
      refine ⟨RedSigmaRel eqrel Δ (wk ρ F) (wk (.lift ρ) G) relF' relG',
        .sigma (wkTypeStarWf hρ hΔ D) hρF hρG (eqrel.wkType hρ hΔ AeqA)
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
        ?_, hSigmaTerm, ?_⟩
      · rintro B ⟨F', G', D', AeqB, FeqF', GeqG'⟩
        refine ⟨wk ρ F', wk (.lift ρ) G', wkTypeStar hρ hΔ D', eqrel.wkType hρ hΔ AeqB,
          fun {ρ₁ Δ₁} hρ₁ hΔ₁ ↦ ?_,
          fun {ρ₁ Δ₁ a} hρ₁ hΔ₁ ha ↦ ?_⟩
        · rw [wk_comp]
          exact FeqF' (hρ₁.comp hρ) hΔ₁
        · rw [← wk_comp_subst]
          exact GeqG' (hρ₁.comp hρ) hΔ₁ ha
      · rintro t u ⟨p, r, d, d', prodP, prodR, peqr, ht, hu, fstP, fstR, fstEq, sndEq⟩
        exact ⟨wk ρ p, wk ρ r, wkStarWf hρ hΔ d, wkStarWf hρ hΔ d',
          prodP.wk ρ, prodR.wk ρ, eqrel.wkTerm hρ hΔ peqr,
          hSigmaTerm ht, hSigmaTerm hu,
          hF_wk_hasTerm fstP, hF_wk_hasTerm fstR,
          hF_wk_eqTerm fstEq, hG_wk_eqTerm fstP sndEq⟩
  | @id Γ A Ty lhs rhs relTy D AeqA _derivTy hasLhs hasRhs lhsEqLhs rhsEqRhs ihTy =>
      intro ρ Δ hρ hΔ
      rcases ihTy hρ hΔ with ⟨relTy', hTy', hEqTy, hTermTy, hEqTermTy⟩
      refine ⟨RedIdRel eqrel Δ (wk ρ Ty) (wk ρ lhs) (wk ρ rhs) relTy',
        .id (wkTypeStarWf hρ hΔ D) (eqrel.wkType hρ hΔ AeqA) hTy'
          (hTermTy hasLhs) (hTermTy hasRhs) (hEqTermTy lhsEqLhs) (hEqTermTy rhsEqRhs),
        ?_, ?_, ?_⟩
      · rintro B ⟨Ty', lhs', rhs', D', AeqB, TyeqTy', lhseqlhs', rhseqrhs', _lhsEqRhs_iff⟩
        exact RedIdEq.ofTermEq hTy' (wkTypeStar hρ hΔ D') (eqrel.wkType hρ hΔ AeqB)
          (hEqTy TyeqTy') (hEqTermTy lhseqlhs') (hEqTermTy rhseqrhs')
      · rintro t ⟨u, d, uequ, prop⟩
        refine ⟨wk ρ u, wkStarWf hρ hΔ d, eqrel.wkTerm hρ hΔ uequ, ?_⟩
        cases prop with
        | rfl h => exact .rfl (hEqTermTy h)
        | ne nf => exact .ne (wkTermNe hρ hΔ nf)
      · rintro t u ⟨t', u', d, d', t'equ', prop⟩
        refine ⟨wk ρ t', wk ρ u', wkStarWf hρ hΔ d, wkStarWf hρ hΔ d',
          eqrel.wkTerm hρ hΔ t'equ', ?_⟩
        cases prop with
        | rfl h => exact .rfl (hEqTermTy h)
        | ne nf => exact .ne (wkEqTermNe hρ hΔ nf)
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
  | empty D => cases whnfRedStar D.reduction .univ
  | unit D => cases whnfRedStar D.reduction .univ
  | ne neA =>
      have h := whnfRedStar neA.D.reduction .univ
      subst h
      cases neA.neK
  | pi D => cases whnfRedStar D.reduction .univ
  | sigma D => cases whnfRedStar D.reduction .univ
  | id D => cases whnfRedStar D.reduction .univ

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
  | empty D => cases whnfRedStar D.reduction .univ
  | unit D => cases whnfRedStar D.reduction .univ
  | ne neA =>
      have h := whnfRedStar neA.D.reduction .univ
      subst h
      cases neA.neK
  | pi D => cases whnfRedStar D.reduction .univ
  | sigma D => cases whnfRedStar D.reduction .univ
  | id D => cases whnfRedStar D.reduction .univ

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
  | @empty Γ A D =>
      have hAEmpty : TypeEq Γ A .empty := subsetStar D.reduction
      refine ⟨?_, ?_⟩
      · intro n neN hn n_eq_n
        have hn' : HasType Γ n .empty := .conv hn hAEmpty
        have n_eq_n' : eqrel.NeEqRel Γ n n .empty := eqrel.convNe n_eq_n hAEmpty
        exact .mk n (idRedTermWf hn') (eqrel.neToTerm n_eq_n') ⟨neN, hn', n_eq_n'⟩
      · intro n n' neN neN' hn hn' n_eq_n'
        have hn_empty : HasType Γ n .empty := .conv hn hAEmpty
        have hn'_empty : HasType Γ n' .empty := .conv hn' hAEmpty
        have n_eq_n'_empty : eqrel.NeEqRel Γ n n' .empty := eqrel.convNe n_eq_n' hAEmpty
        exact .mk n n' (idRedTermWf hn_empty) (idRedTermWf hn'_empty)
          (eqrel.neToTerm n_eq_n'_empty) ⟨neN, neN', n_eq_n'_empty⟩
  | @unit Γ A D =>
      have hAUnit : TypeEq Γ A .unit := subsetStar D.reduction
      refine ⟨?_, ?_⟩
      · intro n neN hn _n_eq_n
        have hn' : HasType Γ n .unit := .conv hn hAUnit
        exact .mk n (idRedTermWf hn') (.neutral neN)
      · intro n n' _neN _neN' hn hn' _n_eq_n'
        exact ⟨.conv hn hAUnit, .conv hn' hAUnit⟩
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
  | @sigma Γ A F G D hF hG _AeqA relF relG hF_ex _derivF hG_ex derivG Gext ihF ihG =>
      have hASigma : TypeEq Γ A (.sigma F G) := subsetStar D.reduction
      have hΓ : CtxWf Γ := wfType hF
      have hF_eq : wk .id F = F := wk_id F
      have hG_eq : ∀ u, subst0 (wk (.lift .id) G) u = subst0 G u := by
        intro u; rw [wk_lift_id]
      have hNeuTerm : ∀ {n}, Neutral n → HasType Γ n A → eqrel.NeEqRel Γ n n A →
          RedSigmaTerm eqrel Γ F G relF relG n := by
        intro n neN hn n_eq_n
        have hnSigma : HasType Γ n (.sigma F G) := .conv hn hASigma
        have neqSigma : eqrel.NeEqRel Γ n n (.sigma F G) := eqrel.convNe n_eq_n hASigma
        rcases hF_ex .id hΓ with ⟨rF, hrF⟩
        have hFst_syn : HasType Γ (.fst n) (wk .id F) := by
          rw [hF_eq]; exact .fst hF hG hnSigma
        have hNeFst : eqrel.NeEqRel Γ (.fst n) (.fst n) (wk .id F) := by
          rw [hF_eq]; exact eqrel.fstCong hF hG neqSigma
        have fstN : RelFHasTerm relF .id Γ (.fst n) :=
          ⟨rF, hrF, (ihF .id hΓ rF hrF).1 (.fst neN) hFst_syn hNeFst⟩
        rcases hG_ex .id hΓ fstN with ⟨sG, hsG⟩
        have hSnd_syn : HasType Γ (.snd n) (subst0 (wk (.lift .id) G) (.fst n)) := by
          rw [hG_eq]; exact .snd hF hG hnSigma
        have hNeSnd : eqrel.NeEqRel Γ (.snd n) (.snd n) (subst0 (wk (.lift .id) G) (.fst n)) := by
          rw [hG_eq]; exact eqrel.sndCong hF hG neqSigma
        have sndN : RelGHasTerm relG .id Γ (.fst n) (.snd n) :=
          ⟨sG, hsG, (ihG .id hΓ fstN sG hsG).1 (.snd neN) hSnd_syn hNeSnd⟩
        exact ⟨n, idRedTermWf hnSigma, .neutral neN, eqrel.neToTerm neqSigma, fstN, sndN⟩
      refine ⟨hNeuTerm, ?_⟩
      intro n n' neN neN' hn hn' n_eq_n'
      have hnSigma : HasType Γ n (.sigma F G) := .conv hn hASigma
      have hn'Sigma : HasType Γ n' (.sigma F G) := .conv hn' hASigma
      have neqSigma : eqrel.NeEqRel Γ n n' (.sigma F G) := eqrel.convNe n_eq_n' hASigma
      have n_eq_n : eqrel.NeEqRel Γ n n A :=
        eqrel.transNe n_eq_n' (eqrel.symmNe n_eq_n')
      have n'_eq_n' : eqrel.NeEqRel Γ n' n' A :=
        eqrel.transNe (eqrel.symmNe n_eq_n') n_eq_n'
      have ht := hNeuTerm neN hn n_eq_n
      have ht' := hNeuTerm neN' hn' n'_eq_n'
      rcases hF_ex .id hΓ with ⟨rF, hrF⟩
      have hFst_n : HasType Γ (.fst n) (wk .id F) := by rw [hF_eq]; exact .fst hF hG hnSigma
      have hFst_n' : HasType Γ (.fst n') (wk .id F) := by rw [hF_eq]; exact .fst hF hG hn'Sigma
      have hNeFst_nn : eqrel.NeEqRel Γ (.fst n) (.fst n) (wk .id F) := by
        rw [hF_eq]; exact eqrel.fstCong hF hG (eqrel.convNe n_eq_n hASigma)
      have hNeFst_n'n' : eqrel.NeEqRel Γ (.fst n') (.fst n') (wk .id F) := by
        rw [hF_eq]; exact eqrel.fstCong hF hG (eqrel.convNe n'_eq_n' hASigma)
      have hNeFst_nn' : eqrel.NeEqRel Γ (.fst n) (.fst n') (wk .id F) := by
        rw [hF_eq]; exact eqrel.fstCong hF hG neqSigma
      have fstN : RelFHasTerm relF .id Γ (.fst n) :=
        ⟨rF, hrF, (ihF .id hΓ rF hrF).1 (.fst neN) hFst_n hNeFst_nn⟩
      have fstN' : RelFHasTerm relF .id Γ (.fst n') :=
        ⟨rF, hrF, (ihF .id hΓ rF hrF).1 (.fst neN') hFst_n' hNeFst_n'n'⟩
      have fstEq : RelFEqTerm relF .id Γ (.fst n) (.fst n') :=
        ⟨rF, hrF, (ihF .id hΓ rF hrF).2 (.fst neN) (.fst neN') hFst_n hFst_n' hNeFst_nn'⟩
      rcases hG_ex .id hΓ fstN with ⟨sG, hsG⟩
      rcases hG_ex .id hΓ fstN' with ⟨sG', hsG'⟩
      rcases Gext .id hΓ fstN fstN' fstEq with ⟨sG_ext, hsG_ext, hGnGn'⟩
      have hGAt_ext := derivG .id hΓ fstN sG_ext hsG_ext
      have hGAt_n' := derivG .id hΓ fstN' sG' hsG'
      have hGn'Gn : sG'.eqType (subst0 (wk (.lift .id) G) (.fst n)) :=
        symLogRelAt hGAt_ext hGAt_n' hGnGn'
      have hGn'Gn_syn : TypeEq Γ (subst0 (wk (.lift .id) G) (.fst n')) (subst0 (wk (.lift .id) G) (.fst n)) :=
        eqrel.typeToEq (escapeEq ⟨sG', hGAt_n'⟩ ⟨sG', hGAt_n', hGn'Gn⟩)
      have hSnd_n : HasType Γ (.snd n) (subst0 (wk (.lift .id) G) (.fst n)) := by
        rw [hG_eq]; exact .snd hF hG hnSigma
      have hSnd_n'_0 : HasType Γ (.snd n') (subst0 (wk (.lift .id) G) (.fst n')) := by
        rw [hG_eq]; exact .snd hF hG hn'Sigma
      have hSnd_n' : HasType Γ (.snd n') (subst0 (wk (.lift .id) G) (.fst n)) :=
        .conv hSnd_n'_0 hGn'Gn_syn
      have hNeSnd_nn' : eqrel.NeEqRel Γ (.snd n) (.snd n') (subst0 (wk (.lift .id) G) (.fst n)) := by
        rw [hG_eq]; exact eqrel.sndCong hF hG neqSigma
      have sndEq : RelGEqTerm relG .id Γ (.fst n) (.snd n) (.snd n') :=
        ⟨sG, hsG, (ihG .id hΓ fstN sG hsG).2 (.snd neN) (.snd neN') hSnd_n hSnd_n' hNeSnd_nn'⟩
      exact ⟨n, n', idRedTermWf hnSigma, idRedTermWf hn'Sigma,
        .neutral neN, .neutral neN', eqrel.neToTerm neqSigma,
        ht, ht', fstN, fstN', fstEq, sndEq⟩
  | @id Γ A Ty lhs rhs relTy D _AeqA _derivTy _hasLhs _hasRhs _lhsEqLhs _rhsEqRhs _ihTy =>
      have hAId : TypeEq Γ A (.id Ty lhs rhs) := subsetStar D.reduction
      refine ⟨?_, ?_⟩
      · intro n neN hn n_eq_n
        have hn' : HasType Γ n (.id Ty lhs rhs) := .conv hn hAId
        have n_eq_n' : eqrel.NeEqRel Γ n n (.id Ty lhs rhs) := eqrel.convNe n_eq_n hAId
        exact .mk n (idRedTermWf hn') (eqrel.neToTerm n_eq_n') (.ne ⟨neN, hn', n_eq_n'⟩)
      · intro n n' neN neN' hn hn' n_eq_n'
        have hn_id : HasType Γ n (.id Ty lhs rhs) := .conv hn hAId
        have hn'_id : HasType Γ n' (.id Ty lhs rhs) := .conv hn' hAId
        have n_eq_n'_id : eqrel.NeEqRel Γ n n' (.id Ty lhs rhs) := eqrel.convNe n_eq_n' hAId
        exact .mk n n' (idRedTermWf hn_id) (idRedTermWf hn'_id)
          (eqrel.neToTerm n_eq_n'_id) (.ne ⟨neN, neN', n_eq_n'_id⟩)
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
  | @empty Γ B D' =>
      intro A D
      have hA : TypeWf Γ A := redFirstStar D
      exact ⟨.empty ⟨hA, D'.target, D.trans D'.reduction⟩, D'.reduction⟩
  | @unit Γ B D' =>
      intro A D
      have hA : TypeWf Γ A := redFirstStar D
      exact ⟨.unit ⟨hA, D'.target, D.trans D'.reduction⟩, D'.reduction⟩
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
  | @sigma Γ B F G D' hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext _ihF _ihG =>
      intro A D
      have hA : TypeWf Γ A := redFirstStar D
      refine ⟨.sigma ⟨hA, D'.target, D.trans D'.reduction⟩
          hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext,
        ⟨F, G, D'.reduction, AeqA,
          fun {ρ Δ} hρ hΔ ↦ ?_,
          fun {ρ Δ a} hρ hΔ ha ↦ ?_⟩⟩
      · rcases hF_ex hρ hΔ with ⟨r, hr⟩
        exact ⟨r, hr, (reflLogRelAt (derivF hρ hΔ r hr)).1⟩
      · rcases hG_ex hρ hΔ ha with ⟨s, hs⟩
        exact ⟨s, hs, (reflLogRelAt (derivG hρ hΔ ha s hs)).1⟩
  | @id Γ B Ty lhs rhs relTy D' AeqA derivTy hasLhs hasRhs lhsEqLhs rhsEqRhs _ihTy =>
      intro A D
      have hA : TypeWf Γ A := redFirstStar D
      exact ⟨.id ⟨hA, D'.target, D.trans D'.reduction⟩
          AeqA derivTy hasLhs hasRhs lhsEqLhs rhsEqRhs,
        ⟨Ty, lhs, rhs, D'.reduction, AeqA, (reflLogRelAt derivTy).1,
          lhsEqLhs, rhsEqRhs, Iff.rfl⟩⟩
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
  | empty D =>
      rcases hu with ⟨n, d, neqn, nf⟩
      have hAEmpty : TypeEq Γ A .empty := subsetStar D.reduction
      have ht_empty : HasType Γ t .empty := .conv (redFirstStarTerm d_tu) hAEmpty
      have d_tu_empty : Star Γ t u .empty := d_tu.conv hAEmpty
      have d' : StarWf Γ t n .empty := ⟨ht_empty, d.target, d_tu_empty.trans d.reduction⟩
      exact ⟨⟨_, hA, .mk n d' neqn nf⟩,
        ⟨_, hA, .mk n n d' d neqn ⟨nf.neK, nf.neK, nf.keqk⟩⟩⟩
  | unit D =>
      rcases hu with ⟨n, d, prop⟩
      have hAUnit : TypeEq Γ A .unit := subsetStar D.reduction
      have ht_unit : HasType Γ t .unit := .conv (redFirstStarTerm d_tu) hAUnit
      have hu_unit : HasType Γ u .unit := d.source
      have d_tu_unit : Star Γ t u .unit := d_tu.conv hAUnit
      have d' : StarWf Γ t n .unit := ⟨ht_unit, d.target, d_tu_unit.trans d.reduction⟩
      exact ⟨⟨_, hA, .mk n d' prop⟩,
        ⟨_, hA, ⟨ht_unit, hu_unit⟩⟩⟩
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
  | @sigma l₀ _ _ F G D hF _hG _AeqA relF relG _hF_ex derivF _hG_ex derivG _Gext =>
      rcases hu with ⟨p, d, prodP, peqp, fstP, sndP⟩
      have hΓ : CtxWf Γ := wfType hF
      have hASigma : TypeEq Γ A (.sigma F G) := subsetStar D.reduction
      have ht_Sigma : HasType Γ t (.sigma F G) := .conv (redFirstStarTerm d_tu) hASigma
      have d_tu_Sigma : Star Γ t u (.sigma F G) := d_tu.conv hASigma
      have d' : StarWf Γ t p (.sigma F G) := ⟨ht_Sigma, d.target, d_tu_Sigma.trans d.reduction⟩
      have ht_SigmaTerm : RedSigmaTerm eqrel Γ F G relF relG t :=
        ⟨p, d', prodP, peqp, fstP, sndP⟩
      have hu_SigmaTerm : RedSigmaTerm eqrel Γ F G relF relG u :=
        ⟨p, d, prodP, peqp, fstP, sndP⟩
      rcases fstP with ⟨rF, hrF, hFstP⟩
      rcases sndP with ⟨sG, hsG, hSndP⟩
      have fstEq : RelFEqTerm relF .id Γ (.fst p) (.fst p) :=
        ⟨rF, hrF, (reflLogRelAt (derivF .id hΓ rF hrF)).2 hFstP⟩
      have sndEq : RelGEqTerm relG .id Γ (.fst p) (.snd p) (.snd p) :=
        ⟨sG, hsG, (reflLogRelAt (derivG .id hΓ ⟨rF, hrF, hFstP⟩ sG hsG)).2 hSndP⟩
      exact ⟨⟨_, hA, ht_SigmaTerm⟩,
        ⟨_, hA, ⟨p, p, d', d, prodP, prodP, peqp, ht_SigmaTerm, hu_SigmaTerm,
          ⟨rF, hrF, hFstP⟩, ⟨rF, hrF, hFstP⟩, fstEq, sndEq⟩⟩⟩
  | @id l₀ _ _ Ty lhs rhs relTy D _AeqA _derivTy _hasLhs _hasRhs _lhsEqLhs _rhsEqRhs =>
      rcases hu with ⟨u', d, u'equ', prop⟩
      have hAId : TypeEq Γ A (.id Ty lhs rhs) := subsetStar D.reduction
      have ht_id : HasType Γ t (.id Ty lhs rhs) := .conv (redFirstStarTerm d_tu) hAId
      have d_tu_id : Star Γ t u (.id Ty lhs rhs) := d_tu.conv hAId
      have d' : StarWf Γ t u' (.id Ty lhs rhs) := ⟨ht_id, d.target, d_tu_id.trans d.reduction⟩
      have propEq : RedIdTermEqProp eqrel Γ Ty lhs rhs relTy u' u' := by
        cases prop with
        | rfl h => exact .rfl h
        | ne nf => exact .ne ⟨nf.neK, nf.neK, nf.keqk⟩
      exact ⟨⟨_, hA, .mk u' d' u'equ' prop⟩,
        ⟨_, hA, .mk u' u' d' d u'equ' propEq⟩⟩

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