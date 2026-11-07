/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Typed/Properties.agda, Definition/Typed/Reduction.agda,
Definition/Typed/RedSteps.agda, Definition/Typed/EqualityRelation.agda,
Definition/Typed/EqRelInstance.agda.
-/
import LogrelMLTT.Weakening

namespace LogrelMLTT

/-- Induction principle on `HasType` alone (for properties that do not need hypotheses on `TypeWf`/`TypeEq`). -/
theorem HasType.indOnly
    {motive : ∀ (Γ : Context) (t A : Term), HasType Γ t A → Prop}
    (nat : ∀ {Γ} (hΓ : CtxWf Γ), motive Γ .nat .univ (.nat hΓ))
    (pi : ∀ {Γ F G} (hF : HasType Γ F .univ) (hG : HasType (F :: Γ) G .univ),
      motive Γ F .univ hF → motive (F :: Γ) G .univ hG → motive Γ (.pi F G) .univ (.pi hF hG))
    (var : ∀ {Γ A x} (hΓ : CtxWf Γ) (hm : Member x A Γ), motive Γ (.var x) A (.var hΓ hm))
    (lam : ∀ {Γ F G t} (hF : TypeWf Γ F) (ht : HasType (F :: Γ) t G),
      motive (F :: Γ) t G ht → motive Γ (.lam t) (.pi F G) (.lam hF ht))
    (app : ∀ {Γ g a F G} (hg : HasType Γ g (.pi F G)) (ha : HasType Γ a F),
      motive Γ g (.pi F G) hg → motive Γ a F ha → motive Γ (.app g a) (subst0 G a) (.app hg ha))
    (zero : ∀ {Γ} (hΓ : CtxWf Γ), motive Γ .zero .nat (.zero hΓ))
    (succ : ∀ {Γ n} (hn : HasType Γ n .nat), motive Γ n .nat hn → motive Γ (.succ n) .nat (.succ hn))
    (natrec : ∀ {Γ G s z n} (hG : TypeWf (.nat :: Γ) G) (hz : HasType Γ z (subst0 G .zero))
      (hs : HasType Γ s (recStepType G)) (hn : HasType Γ n .nat),
      motive Γ z (subst0 G .zero) hz → motive Γ s (recStepType G) hs → motive Γ n .nat hn →
      motive Γ (.natrec G z s n) (subst0 G n) (.natrec hG hz hs hn))
    (conv : ∀ {Γ t A B} (ht : HasType Γ t A) (hEq : TypeEq Γ A B),
      motive Γ t A ht → motive Γ t B (.conv ht hEq))
    {Γ : Context} {t A : Term} (d : HasType Γ t A) : motive Γ t A d :=
  HasType.rec
    (motive_1 := fun _ _ ↦ True)
    (motive_2 := fun _ _ _ ↦ True)
    (motive_3 := motive)
    (motive_4 := fun _ _ _ _ ↦ True)
    (motive_5 := fun _ _ _ _ _ ↦ True)
    trivial
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun hΓ _ ↦ nat hΓ)
    (fun hF hG ihF ihG ↦ pi hF hG ihF ihG)
    (fun hΓ hm _ ↦ var hΓ hm)
    (fun hF ht _ iht ↦ lam hF ht iht)
    (fun hg ha ihg iha ↦ app hg ha ihg iha)
    (fun hΓ _ ↦ zero hΓ)
    (fun hn ihn ↦ succ hn ihn)
    (fun hG hz hs hn _ ihz ihs ihn ↦ natrec hG hz hs hn ihz ihs ihn)
    (fun ht hEq iht _ ↦ conv ht hEq iht)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    d

theorem CtxWf.tail {Γ : Context} {A : Term} : CtxWf (A :: Γ) → CtxWf Γ
  | .cons hΓ _ => hΓ

theorem CtxWf.headWf {Γ : Context} {A : Term} : CtxWf (A :: Γ) → TypeWf Γ A
  | .cons _ hA => hA

/-- Context well-formedness extracted from a type derivation (`wf`). -/
theorem wfType {Γ : Context} {A : Term} (d : TypeWf Γ A) : CtxWf Γ :=
  TypeWf.rec
    (motive_1 := fun Γ _ ↦ CtxWf Γ)
    (motive_2 := fun Γ _ _ ↦ CtxWf Γ)
    (motive_3 := fun Γ _ _ _ ↦ CtxWf Γ)
    (motive_4 := fun Γ _ _ _ ↦ CtxWf Γ)
    (motive_5 := fun Γ _ _ _ _ ↦ CtxWf Γ)
    .nil
    (fun hΓ hA _ _ ↦ .cons hΓ hA)
    (fun hΓ _ ↦ hΓ)
    (fun hΓ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun _ ihA ↦ ihA)
    (fun hΓ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun hΓ _ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun _ _ _ iha ↦ iha)
    (fun hΓ _ ↦ hΓ)
    (fun _ ihn ↦ ihn)
    (fun _ _ _ _ _ ihz _ _ ↦ ihz)
    (fun _ _ iht _ ↦ iht)
    (fun _ ihEq ↦ ihEq)
    (fun _ ihA ↦ ihA)
    (fun _ ihEq ↦ ihEq)
    (fun _ _ ih₁ _ ↦ ih₁)
    (fun _ _ _ _ ihFH _ ↦ ihFH)
    (fun _ iht ↦ iht)
    (fun _ ihEq ↦ ihEq)
    (fun _ _ ih₁ _ ↦ ih₁)
    (fun _ _ ihEq _ ↦ ihEq)
    (fun _ _ _ _ ihFH _ ↦ ihFH)
    (fun _ _ ihfg _ ↦ ihfg)
    (fun _ _ _ _ _ iha ↦ iha)
    (fun _ _ _ _ _ ihf _ _ ↦ ihf)
    (fun _ ihmn ↦ ihmn)
    (fun _ _ _ _ _ ihzz' _ _ ↦ ihzz')
    (fun _ _ _ _ ihz _ ↦ ihz)
    (fun _ _ _ _ ihn _ _ _ ↦ ihn)
    d

/-- Context well-formedness extracted from a term typing derivation (`wfTerm`). -/
theorem wfTerm {Γ : Context} {t A : Term} (d : HasType Γ t A) : CtxWf Γ :=
  HasType.indOnly (motive := fun Γ _ _ _ ↦ CtxWf Γ)
    (fun hΓ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun hΓ _ ↦ hΓ)
    (fun _ _ iht ↦ CtxWf.tail iht)
    (fun _ _ _ iha ↦ iha)
    (fun hΓ ↦ hΓ)
    (fun _ ihn ↦ ihn)
    (fun _ _ _ _ ihz _ _ ↦ ihz)
    (fun _ _ iht ↦ iht)
    d

/-- Context well-formedness extracted from a type equality derivation (`wfEq`). -/
theorem wfTypeEq {Γ : Context} {A B : Term} (d : TypeEq Γ A B) : CtxWf Γ :=
  TypeEq.rec
    (motive_1 := fun Γ _ ↦ CtxWf Γ)
    (motive_2 := fun Γ _ _ ↦ CtxWf Γ)
    (motive_3 := fun Γ _ _ _ ↦ CtxWf Γ)
    (motive_4 := fun Γ _ _ _ ↦ CtxWf Γ)
    (motive_5 := fun Γ _ _ _ _ ↦ CtxWf Γ)
    .nil
    (fun hΓ hA _ _ ↦ .cons hΓ hA)
    (fun hΓ _ ↦ hΓ)
    (fun hΓ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun _ ihA ↦ ihA)
    (fun hΓ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun hΓ _ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun _ _ _ iha ↦ iha)
    (fun hΓ _ ↦ hΓ)
    (fun _ ihn ↦ ihn)
    (fun _ _ _ _ _ ihz _ _ ↦ ihz)
    (fun _ _ iht _ ↦ iht)
    (fun _ ihEq ↦ ihEq)
    (fun _ ihA ↦ ihA)
    (fun _ ihEq ↦ ihEq)
    (fun _ _ ih₁ _ ↦ ih₁)
    (fun _ _ _ _ ihFH _ ↦ ihFH)
    (fun _ iht ↦ iht)
    (fun _ ihEq ↦ ihEq)
    (fun _ _ ih₁ _ ↦ ih₁)
    (fun _ _ ihEq _ ↦ ihEq)
    (fun _ _ _ _ ihFH _ ↦ ihFH)
    (fun _ _ ihfg _ ↦ ihfg)
    (fun _ _ _ _ _ iha ↦ iha)
    (fun _ _ _ _ _ ihf _ _ ↦ ihf)
    (fun _ ihmn ↦ ihmn)
    (fun _ _ _ _ _ ihzz' _ _ ↦ ihzz')
    (fun _ _ _ _ ihz _ ↦ ihz)
    (fun _ _ _ _ ihn _ _ _ ↦ ihn)
    d

/-- Context well-formedness extracted from a term equality derivation (`wfEqTerm`). -/
theorem wfTermEq {Γ : Context} {t u A : Term} (d : TermEq Γ t u A) : CtxWf Γ :=
  TermEq.rec
    (motive_1 := fun Γ _ ↦ CtxWf Γ)
    (motive_2 := fun Γ _ _ ↦ CtxWf Γ)
    (motive_3 := fun Γ _ _ _ ↦ CtxWf Γ)
    (motive_4 := fun Γ _ _ _ ↦ CtxWf Γ)
    (motive_5 := fun Γ _ _ _ _ ↦ CtxWf Γ)
    .nil
    (fun hΓ hA _ _ ↦ .cons hΓ hA)
    (fun hΓ _ ↦ hΓ)
    (fun hΓ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun _ ihA ↦ ihA)
    (fun hΓ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun hΓ _ _ ↦ hΓ)
    (fun _ _ ihF _ ↦ ihF)
    (fun _ _ _ iha ↦ iha)
    (fun hΓ _ ↦ hΓ)
    (fun _ ihn ↦ ihn)
    (fun _ _ _ _ _ ihz _ _ ↦ ihz)
    (fun _ _ iht _ ↦ iht)
    (fun _ ihEq ↦ ihEq)
    (fun _ ihA ↦ ihA)
    (fun _ ihEq ↦ ihEq)
    (fun _ _ ih₁ _ ↦ ih₁)
    (fun _ _ _ _ ihFH _ ↦ ihFH)
    (fun _ iht ↦ iht)
    (fun _ ihEq ↦ ihEq)
    (fun _ _ ih₁ _ ↦ ih₁)
    (fun _ _ ihEq _ ↦ ihEq)
    (fun _ _ _ _ ihFH _ ↦ ihFH)
    (fun _ _ ihfg _ ↦ ihfg)
    (fun _ _ _ _ _ iha ↦ iha)
    (fun _ _ _ _ _ ihf _ _ ↦ ihf)
    (fun _ ihmn ↦ ihmn)
    (fun _ _ _ _ _ ihzz' _ _ ↦ ihzz')
    (fun _ _ _ _ ihz _ ↦ ihz)
    (fun _ _ _ _ ihn _ _ _ ↦ ihn)
    d

/-- Single-step term reduction is included in judgmental equality (`subsetTerm`, Lemma 2.2). -/
theorem subsetTerm {Γ : Context} {t u A : Term} :
    Step Γ t u A → TermEq Γ t u A
  | .conv hStep hEq => .conv (subsetTerm hStep) hEq
  | .app hStep ha => .app (subsetTerm hStep) (.refl ha)
  | .beta hA ht ha => .beta hA ht ha
  | .natrec hF hz hs hStep =>
      .natrec (.refl hF) (.refl hz) (.refl hs) (subsetTerm hStep)
  | .natrecZero hF hz hs => .natrecZero hF hz hs
  | .natrecSucc hn hF hz hs => .natrecSucc hn hF hz hs

/-- Single-step type reduction is included in judgmental type equality (`subset`, Lemma 2.2). -/
theorem subsetType {Γ : Context} {A B : Term} :
    TypeStep Γ A B → TypeEq Γ A B
  | .fromUniv hStep => .fromUniv (subsetTerm hStep)

/-- Multi-step term reduction is included in judgmental equality (`subset*Term`, Lemma 2.2). -/
theorem subsetStarTerm {Γ : Context} {t u A : Term} :
    Star Γ t u A → TermEq Γ t u A
  | .refl ht => .refl ht
  | .step hStep hStar => .trans (subsetTerm hStep) (subsetStarTerm hStar)

/-- Multi-step type reduction is included in judgmental type equality (`subset*`, Lemma 2.2). -/
theorem subsetStar {Γ : Context} {A B : Term} :
    TypeStar Γ A B → TypeEq Γ A B
  | .refl hA => .refl hA
  | .step hStep hStar => .trans (subsetType hStep) (subsetStar hStar)

/-- Left-hand typing extraction from single-step term reduction (`redFirstTerm`, Lemma 2.3). -/
theorem redFirstTerm {Γ : Context} {t u A : Term} :
    Step Γ t u A → HasType Γ t A
  | .conv hStep hEq => .conv (redFirstTerm hStep) hEq
  | .app hStep ha => .app (redFirstTerm hStep) ha
  | .beta hA ht ha => .app (.lam hA ht) ha
  | .natrec hF hz hs hStep => .natrec hF hz hs (redFirstTerm hStep)
  | .natrecZero hF hz hs => .natrec hF hz hs (.zero (wfTerm hz))
  | .natrecSucc hn hF hz hs => .natrec hF hz hs (.succ hn)

/-- Left-hand well-formedness extraction from single-step type reduction (`redFirst`, Lemma 2.3). -/
theorem redFirstType {Γ : Context} {A B : Term} :
    TypeStep Γ A B → TypeWf Γ A
  | .fromUniv hStep => .fromUniv (redFirstTerm hStep)

/-- Left-hand typing extraction from multi-step term reduction (`redFirst*Term`, Lemma 2.3). -/
theorem redFirstStarTerm {Γ : Context} {t u A : Term} :
    Star Γ t u A → HasType Γ t A
  | .refl ht => ht
  | .step hStep _ => redFirstTerm hStep

/-- Left-hand well-formedness extraction from multi-step type reduction (`redFirst*`, Lemma 2.3). -/
theorem redFirstStar {Γ : Context} {A B : Term} :
    TypeStar Γ A B → TypeWf Γ A
  | .refl hA => hA
  | .step hStep _ => redFirstType hStep

/-- No neutral term is well-typed in the empty context (`noNe`). -/
theorem noNe {t A : Term} (ht : HasType [] t A) (hn : Neutral t) : False := by
  have aux : ∀ {Γ : Context} {t A : Term}, HasType Γ t A → Γ = [] → Neutral t → False := by
    intro Γ t A h
    induction h using HasType.indOnly with
    | nat _ => intro _ hn; cases hn
    | pi _ _ _ _ => intro _ hn; cases hn
    | var _ hm =>
        intro hΓ _
        subst hΓ
        cases hm
    | lam _ _ _ => intro _ hn; cases hn
    | app _ _ ihg _ =>
        intro hΓ hn
        cases hn with
        | app hn' => exact ihg hΓ hn'
    | zero _ => intro _ hn; cases hn
    | succ _ _ => intro _ hn; cases hn
    | natrec _ _ _ _ _ _ ihn =>
        intro hΓ hn
        cases hn with
        | natrec hn' => exact ihn hΓ hn'
    | conv _ _ iht =>
        intro hΓ hn
        exact iht hΓ hn
  exact aux ht rfl hn

/-- Neutral terms do not weak-head reduce (`neRedTerm`, Lemma 2.4). -/
theorem neRedTerm {Γ : Context} {t u A : Term} (d : Step Γ t u A) (hn : Neutral t) : False := by
  induction d with
  | conv _ _ ih => exact ih hn
  | app _ _ ih =>
      cases hn with
      | app hn' => exact ih hn'
  | beta _ _ _ =>
      cases hn with
      | app hn' => cases hn'
  | natrec _ _ _ _ ih =>
      cases hn with
      | natrec hn' => exact ih hn'
  | natrecZero _ _ _ =>
      cases hn with
      | natrec hn' => cases hn'
  | natrecSucc _ _ _ _ =>
      cases hn with
      | natrec hn' => cases hn'

/-- Neutral types do not weak-head reduce (`neRed`, Lemma 2.4). -/
theorem neRedType {Γ : Context} {A B : Term} :
    TypeStep Γ A B → Neutral A → False
  | .fromUniv hStep, hn => neRedTerm hStep hn

/-- Weak-head normal forms do not weak-head reduce (`whnfRedTerm`, Lemma 2.4). -/
theorem whnfRedTerm {Γ : Context} {t u A : Term} (d : Step Γ t u A) (hw : Whnf t) : False := by
  induction d with
  | conv _ _ ih => exact ih hw
  | app hStep _ _ =>
      cases hw with
      | neutral hn =>
          cases hn with
          | app hn' => exact neRedTerm hStep hn'
  | beta _ _ _ =>
      cases hw with
      | neutral hn =>
          cases hn with
          | app hn' => cases hn'
  | natrec _ _ _ hStep _ =>
      cases hw with
      | neutral hn =>
          cases hn with
          | natrec hn' => exact neRedTerm hStep hn'
  | natrecZero _ _ _ =>
      cases hw with
      | neutral hn =>
          cases hn with
          | natrec hn' => cases hn'
  | natrecSucc _ _ _ _ =>
      cases hw with
      | neutral hn =>
          cases hn with
          | natrec hn' => cases hn'

/-- Weak-head normal types do not weak-head reduce (`whnfRed`, Lemma 2.4). -/
theorem whnfRedType {Γ : Context} {A B : Term} :
    TypeStep Γ A B → Whnf A → False
  | .fromUniv hStep, hw => whnfRedTerm hStep hw

/-- Multi-step reduction from a term in WHNF is trivial (`whnfRed*Term`, Lemma 2.4). -/
theorem whnfRedStarTerm {Γ : Context} {t u A : Term} :
    Star Γ t u A → Whnf t → t = u
  | .refl _, _ => rfl
  | .step hStep _, hw => False.elim (whnfRedTerm hStep hw)

/-- Multi-step reduction from a type in WHNF is trivial (`whnfRed*`, Lemma 2.4). -/
theorem whnfRedStar {Γ : Context} {A B : Term} :
    TypeStar Γ A B → Whnf A → A = B
  | .refl _, _ => rfl
  | .step hStep _, hw => False.elim (whnfRedType hStep hw)

/-- Determinism of single-step term reduction (`whrDetTerm`, Lemma 2.5). -/
theorem whrDetTerm {Γ : Context} {t u A u' A' : Term}
    (d₁ : Step Γ t u A) (d₂ : Step Γ t u' A') : u = u' := by
  induction d₁ generalizing u' A' with
  | conv _ _ ih => exact ih d₂
  | @app A₀ B₀ f₀ u₀ a₀ d₁ _ ih =>
      have aux : ∀ {t₀ u' A' : Term}, Step Γ t₀ u' A' →
          t₀ = .app f₀ a₀ → Term.app u₀ a₀ = u' := by
        intro t₀ u' A' hStep
        induction hStep with
        | conv _ _ ih₂ => intro heq; exact ih₂ heq
        | app d₂ _ =>
            intro heq
            cases heq
            exact congrArg (fun x ↦ Term.app x a₀) (ih d₂)
        | beta _ _ _ =>
            intro heq
            cases heq
            exact False.elim (whnfRedTerm d₁ .lam)
        | natrec _ _ _ _ => intro heq; cases heq
        | natrecZero _ _ _ => intro heq; cases heq
        | natrecSucc _ _ _ _ => intro heq; cases heq
      exact aux d₂ rfl
  | @beta A₀ B₀ a₀ body₀ _ _ _ =>
      have aux : ∀ {t₀ u' A' : Term}, Step Γ t₀ u' A' →
          t₀ = .app (.lam body₀) a₀ → subst0 body₀ a₀ = u' := by
        intro t₀ u' A' hStep
        induction hStep with
        | conv _ _ ih₂ => intro heq; exact ih₂ heq
        | app d₂ _ =>
            intro heq
            cases heq
            exact False.elim (whnfRedTerm d₂ .lam)
        | beta _ _ _ =>
            intro heq
            cases heq
            rfl
        | natrec _ _ _ _ => intro heq; cases heq
        | natrecZero _ _ _ => intro heq; cases heq
        | natrecSucc _ _ _ _ => intro heq; cases heq
      exact aux d₂ rfl
  | @natrec z₀ s₀ n₀ n'₀ F₀ _ _ _ d₁ ih =>
      have aux : ∀ {t₀ u' A' : Term}, Step Γ t₀ u' A' →
          t₀ = .natrec F₀ z₀ s₀ n₀ → Term.natrec F₀ z₀ s₀ n'₀ = u' := by
        intro t₀ u' A' hStep
        induction hStep with
        | conv _ _ ih₂ => intro heq; exact ih₂ heq
        | app _ _ => intro heq; cases heq
        | beta _ _ _ => intro heq; cases heq
        | natrec _ _ _ d₂ =>
            intro heq
            cases heq
            exact congrArg (Term.natrec F₀ z₀ s₀) (ih d₂)
        | natrecZero _ _ _ =>
            intro heq
            cases heq
            exact False.elim (whnfRedTerm d₁ .zero)
        | natrecSucc _ _ _ _ =>
            intro heq
            cases heq
            exact False.elim (whnfRedTerm d₁ .succ)
      exact aux d₂ rfl
  | @natrecZero z₀ s₀ F₀ _ _ _ =>
      have aux : ∀ {t₀ u' A' : Term}, Step Γ t₀ u' A' →
          t₀ = .natrec F₀ z₀ s₀ .zero → z₀ = u' := by
        intro t₀ u' A' hStep
        induction hStep with
        | conv _ _ ih₂ => intro heq; exact ih₂ heq
        | app _ _ => intro heq; cases heq
        | beta _ _ _ => intro heq; cases heq
        | natrec _ _ _ d₂ =>
            intro heq
            cases heq
            exact False.elim (whnfRedTerm d₂ .zero)
        | natrecZero _ _ _ =>
            intro heq
            cases heq
            rfl
        | natrecSucc _ _ _ _ => intro heq; cases heq
      exact aux d₂ rfl
  | @natrecSucc n₀ z₀ s₀ F₀ _ _ _ _ =>
      have aux : ∀ {t₀ u' A' : Term}, Step Γ t₀ u' A' →
          t₀ = .natrec F₀ z₀ s₀ (.succ n₀) →
          .app (.app s₀ n₀) (.natrec F₀ z₀ s₀ n₀) = u' := by
        intro t₀ u' A' hStep
        induction hStep with
        | conv _ _ ih₂ => intro heq; exact ih₂ heq
        | app _ _ => intro heq; cases heq
        | beta _ _ _ => intro heq; cases heq
        | natrec _ _ _ d₂ =>
            intro heq
            cases heq
            exact False.elim (whnfRedTerm d₂ .succ)
        | natrecZero _ _ _ => intro heq; cases heq
        | natrecSucc _ _ _ _ =>
            intro heq
            cases heq
            rfl
      exact aux d₂ rfl

/-- Determinism of single-step type reduction (`whrDet`, Lemma 2.5). -/
theorem whrDetType {Γ : Context} {A B B' : Term} :
    TypeStep Γ A B → TypeStep Γ A B' → B = B'
  | .fromUniv d₁, .fromUniv d₂ => whrDetTerm d₁ d₂

/-- Confluence toward WHNF for term reduction (`whrDet↘Term`, Lemma 2.5). -/
theorem whrDetWhnfTerm {Γ : Context} {t u A u' : Term}
    (d : TermWhnf Γ t u A) (d' : Star Γ t u' A) : Star Γ u' u A := by
  rcases d with ⟨dStar, hw⟩
  induction d' with
  | refl _ => exact dStar
  | step hStep₂ _ ih =>
      cases dStar with
      | refl _ => exact False.elim (whnfRedTerm hStep₂ hw)
      | step hStep₁ dStar₁ =>
          have heq := whrDetTerm hStep₁ hStep₂
          subst heq
          exact ih dStar₁

/-- Uniqueness of term WHNF (`whrDet*Term`, Lemma 2.5). -/
theorem whrDetStarTerm {Γ : Context} {t u A u' : Term}
    (d₁ : TermWhnf Γ t u A) (d₂ : TermWhnf Γ t u' A) : u = u' := by
  have hStar : Star Γ u' u A := whrDetWhnfTerm d₁ d₂.1
  exact (whnfRedStarTerm hStar d₂.2).symm

/-- Confluence toward WHNF for type reduction. -/
theorem whrDetWhnfType {Γ : Context} {A B B' : Term}
    (d : TypeWhnf Γ A B) (d' : TypeStar Γ A B') : TypeStar Γ B' B := by
  rcases d with ⟨dStar, hw⟩
  induction d' with
  | refl _ => exact dStar
  | step hStep₂ _ ih =>
      cases dStar with
      | refl _ => exact False.elim (whnfRedType hStep₂ hw)
      | step hStep₁ dStar₁ =>
          have heq := whrDetType hStep₁ hStep₂
          subst heq
          exact ih dStar₁

/-- Uniqueness of type WHNF (`whrDet*`, Lemma 2.5). -/
theorem whrDetStar {Γ : Context} {A B B' : Term}
    (d₁ : TypeWhnf Γ A B) (d₂ : TypeWhnf Γ A B') : B = B' := by
  have hStar : TypeStar Γ B' B := whrDetWhnfType d₁ d₂.1
  exact (whnfRedStar hStar d₂.2).symm

/-- Identity bundled type reduction (`idRed:*:`). -/
theorem idRedWf {Γ : Context} {A : Term} (hA : TypeWf Γ A) : TypeStarWf Γ A A :=
  ⟨hA, hA, .refl hA⟩

/-- Identity bundled term reduction (`idRedTerm:*:`). -/
theorem idRedTermWf {Γ : Context} {t A : Term} (ht : HasType Γ t A) : StarWf Γ t t A :=
  ⟨ht, ht, .refl ht⟩

/-- The universe `U` is not a well-typed term (`UnotInA`). -/
theorem UnotInA {Γ : Context} {A : Term} (h : HasType Γ .univ A) : False := by
  have aux : ∀ {Γ : Context} {u A : Term}, HasType Γ u A → u = .univ → False := by
    intro Γ u A ht
    induction ht using HasType.indOnly with
    | nat _ => intro hu; cases hu
    | pi _ _ _ _ => intro hu; cases hu
    | var _ _ => intro hu; cases hu
    | lam _ _ _ => intro hu; cases hu
    | app _ _ _ _ => intro hu; cases hu
    | zero _ => intro hu; cases hu
    | succ _ _ => intro hu; cases hu
    | natrec _ _ _ _ _ _ _ => intro hu; cases hu
    | conv _ _ ih => intro hu; exact ih hu
  exact aux h rfl

theorem UnotInA_subst {Γ : Context} {A B t a : Term}
    (heq : subst0 t a = .univ) (ha : HasType Γ a A) (ht : HasType (A :: Γ) t B) : False := by
  have aux : ∀ {Δ : Context} {t B : Term}, HasType Δ t B →
      subst0 t a = .univ → False := by
    intro Δ t B h
    induction h using HasType.indOnly with
    | nat _ => intro h; cases h
    | pi _ _ _ _ => intro h; cases h
    | @var _ _ x _ _ =>
        intro h
        cases x with
        | zero =>
            change a = .univ at h
            subst h
            exact UnotInA ha
        | succ _ => cases h
    | lam _ _ _ => intro h; cases h
    | app _ _ _ _ => intro h; cases h
    | zero _ => intro h; cases h
    | succ _ _ => intro h; cases h
    | natrec _ _ _ _ _ _ _ => intro h; cases h
    | conv _ _ ih => intro h; exact ih h
  exact aux ht heq

theorem redUStarTerm' {Γ : Context} {A B U' : Term}
    (heq : U' = .univ) (d : Step Γ A U' B) : False := by
  induction d with
  | conv _ _ ih => exact ih heq
  | app _ _ => cases heq
  | beta _ ht ha => exact UnotInA_subst heq ha ht
  | natrec _ _ _ _ => cases heq
  | natrecZero _ hz _ =>
      subst heq
      exact UnotInA hz
  | natrecSucc _ _ _ _ => cases heq

theorem redUStarTerm {Γ : Context} {A B : Term} (d : Star Γ A .univ B) : False := by
  generalize hu : Term.univ = u at d
  induction d with
  | refl ht =>
      subst hu
      exact UnotInA ht
  | step _ _ ih => exact ih hu

/-- No type steps to `U` (`redU`). -/
theorem redU {Γ : Context} {A : Term} : TypeStep Γ A .univ → False
  | .fromUniv d => redUStarTerm' rfl d

/-- Only `U` reduces to `U` (`redU*`). -/
theorem redUStar {Γ : Context} {A : Term} (d : TypeStar Γ A .univ) : A = .univ := by
  have aux : ∀ {A u : Term}, TypeStar Γ A u → u = .univ → A = .univ := by
    intro A u h
    induction h with
    | refl _ => intro hu; exact hu
    | step hStep _ ih =>
        intro hu
        have h' := ih hu
        subst h'
        exact False.elim (redU hStep)
  exact aux d rfl

/-- Weak-head expansion of type equality (`reduction`). -/
theorem reduction {Γ : Context} {A A' B B' : Term}
    (D : TypeStar Γ A A') (D' : TypeStar Γ B B')
    (_whnfA' : Whnf A') (_whnfB' : Whnf B')
    (hEq : TypeEq Γ A' B') : TypeEq Γ A B :=
  .trans (subsetStar D) (.trans hEq (.symm (subsetStar D')))

theorem reduction' {Γ : Context} {A A' B B' : Term}
    (D : TypeStar Γ A A') (D' : TypeStar Γ B B')
    (_whnfA' : Whnf A') (_whnfB' : Whnf B')
    (hEq : TypeEq Γ A B) : TypeEq Γ A' B' :=
  .trans (.symm (subsetStar D)) (.trans hEq (subsetStar D'))

/-- Weak-head expansion of term equality (`reductionₜ`). -/
theorem reductionTerm {Γ : Context} {a a' b b' A B : Term}
    (D : TypeStar Γ A B) (d : Star Γ a a' B) (d' : Star Γ b b' B)
    (_whnfB : Whnf B) (_whnfa' : Whnf a') (_whnfb' : Whnf b')
    (hEq : TermEq Γ a' b' B) : TermEq Γ a b A :=
  .conv (.trans (subsetStarTerm d) (.trans hEq (.symm (subsetStarTerm d'))))
    (.symm (subsetStar D))

theorem reductionTerm' {Γ : Context} {a a' b b' A B : Term}
    (D : TypeStar Γ A B) (d : Star Γ a a' B) (d' : Star Γ b b' B)
    (_whnfB : Whnf B) (_whnfa' : Whnf a') (_whnfb' : Whnf b')
    (hEq : TermEq Γ a b A) : TermEq Γ a' b' B :=
  .trans (.symm (subsetStarTerm d))
    (.trans (.conv hEq (subsetStar D)) (subsetStarTerm d'))

/-- Concatenation of multi-step type reductions (`_⇨*_`). -/
theorem TypeStar.trans {Γ : Context} {A B C : Term} :
    TypeStar Γ A B → TypeStar Γ B C → TypeStar Γ A C
  | .refl _, hBC => hBC
  | .step h₁ h₂, hBC => .step h₁ (h₂.trans hBC)

/-- Concatenation of multi-step term reductions (`_⇨∷*_`). -/
theorem Star.trans {Γ : Context} {t u r A : Term} :
    Star Γ t u A → Star Γ u r A → Star Γ t r A
  | .refl _, hur => hur
  | .step h₁ h₂, hur => .step h₁ (h₂.trans hur)

/-- Conversion of multi-step term reductions (`conv*`). -/
theorem Star.conv {Γ : Context} {t u A B : Term} :
    Star Γ t u A → TypeEq Γ A B → Star Γ t u B
  | .refl ht, hAB => .refl (.conv ht hAB)
  | .step h₁ h₂, hAB => .step (.conv h₁ hAB) (h₂.conv hAB)

/-- Embedding universe term reduction into type reduction (`univ*`). -/
theorem TypeStar.fromUniv {Γ : Context} {A B : Term} (d : Star Γ A B .univ) :
    TypeStar Γ A B := by
  generalize hu : Term.univ = U₀ at d
  induction d with
  | refl hA =>
      subst hu
      exact .refl (.fromUniv hA)
  | step h₁ _ ih =>
      subst hu
      exact .step (.fromUniv h₁) (ih rfl)

/-- Application congruence for multi-step reduction (`app-subst*`). -/
theorem Star.app {Γ : Context} {A B t t' a : Term}
    (d : Star Γ t t' (.pi A B)) (ha : HasType Γ a A) :
    Star Γ (.app t a) (.app t' a) (subst0 B a) := by
  generalize hpi : Term.pi A B = P at d
  induction d with
  | refl ht =>
      subst hpi
      exact .refl (.app ht ha)
  | step h₁ _ ih =>
      subst hpi
      exact .step (.app h₁ ha) (ih rfl)

/-- Generic equality relation interface (`EqRelSet` from `Definition.Typed.EqualityRelation`). -/
structure EqRelSet where
  TypeEqRel : Context → Term → Term → Prop
  TermEqRel : Context → Term → Term → Term → Prop
  NeEqRel : Context → Term → Term → Term → Prop
  neToTerm : ∀ {Γ k l A}, NeEqRel Γ k l A → TermEqRel Γ k l A
  typeToEq : ∀ {Γ A B}, TypeEqRel Γ A B → TypeEq Γ A B
  termToEq : ∀ {Γ t u A}, TermEqRel Γ t u A → TermEq Γ t u A
  univ : ∀ {Γ A B}, TermEqRel Γ A B .univ → TypeEqRel Γ A B
  symmType : ∀ {Γ A B}, TypeEqRel Γ A B → TypeEqRel Γ B A
  symmTerm : ∀ {Γ t u A}, TermEqRel Γ t u A → TermEqRel Γ u t A
  symmNe : ∀ {Γ k l A}, NeEqRel Γ k l A → NeEqRel Γ l k A
  transType : ∀ {Γ A B C}, TypeEqRel Γ A B → TypeEqRel Γ B C → TypeEqRel Γ A C
  transTerm : ∀ {Γ t u v A}, TermEqRel Γ t u A → TermEqRel Γ u v A → TermEqRel Γ t v A
  transNe : ∀ {Γ k l m A}, NeEqRel Γ k l A → NeEqRel Γ l m A → NeEqRel Γ k m A
  convTerm : ∀ {Γ t u A B}, TermEqRel Γ t u A → TypeEq Γ A B → TermEqRel Γ t u B
  convNe : ∀ {Γ k l A B}, NeEqRel Γ k l A → TypeEq Γ A B → NeEqRel Γ k l B
  wkType : ∀ {Γ Δ A B ρ}, WkCtx ρ Δ Γ → CtxWf Δ → TypeEqRel Γ A B → TypeEqRel Δ (wk ρ A) (wk ρ B)
  wkTerm : ∀ {Γ Δ t u A ρ}, WkCtx ρ Δ Γ → CtxWf Δ → TermEqRel Γ t u A →
    TermEqRel Δ (wk ρ t) (wk ρ u) (wk ρ A)
  wkNe : ∀ {Γ Δ k l A ρ}, WkCtx ρ Δ Γ → CtxWf Δ → NeEqRel Γ k l A →
    NeEqRel Δ (wk ρ k) (wk ρ l) (wk ρ A)
  redType : ∀ {Γ A A' B B'}, TypeStar Γ A A' → TypeStar Γ B B' →
    Whnf A' → Whnf B' → TypeEqRel Γ A' B' → TypeEqRel Γ A B
  redTerm : ∀ {Γ a a' b b' A B}, TypeStar Γ A B → Star Γ a a' B → Star Γ b b' B →
    Whnf B → Whnf a' → Whnf b' → TermEqRel Γ a' b' B → TermEqRel Γ a b A
  univRefl : ∀ {Γ}, CtxWf Γ → TypeEqRel Γ .univ .univ
  natRefl : ∀ {Γ}, CtxWf Γ → TypeEqRel Γ .nat .nat
  natTermRefl : ∀ {Γ}, CtxWf Γ → TermEqRel Γ .nat .nat .univ
  piCong : ∀ {Γ F G H E}, TypeWf Γ F → TypeEqRel Γ F H → TypeEqRel (F :: Γ) G E →
    TypeEqRel Γ (.pi F G) (.pi H E)
  piTermCong : ∀ {Γ F G H E}, TypeWf Γ F → TermEqRel Γ F H .univ → TermEqRel (F :: Γ) G E .univ →
    TermEqRel Γ (.pi F G) (.pi H E) .univ
  zeroRefl : ∀ {Γ}, CtxWf Γ → TermEqRel Γ .zero .zero .nat
  succCong : ∀ {Γ m n}, TermEqRel Γ m n .nat → TermEqRel Γ (.succ m) (.succ n) .nat
  etaEq : ∀ {Γ f g F G}, TypeWf Γ F → HasType Γ f (.pi F G) → HasType Γ g (.pi F G) →
    Whnf f → Whnf g → TermEqRel (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G →
    TermEqRel Γ f g (.pi F G)
  varRefl : ∀ {Γ x A}, HasType Γ (.var x) A → NeEqRel Γ (.var x) (.var x) A
  appCong : ∀ {Γ a b f g F G}, NeEqRel Γ f g (.pi F G) → TermEqRel Γ a b F →
    NeEqRel Γ (.app f a) (.app g b) (subst0 G a)
  natrecCong : ∀ {Γ z z' s s' n n' F F'}, TypeEqRel (.nat :: Γ) F F' →
    TermEqRel Γ z z' (subst0 F .zero) → TermEqRel Γ s s' (recStepType F) →
    NeEqRel Γ n n' .nat → NeEqRel Γ (.natrec F z s n) (.natrec F' z' s' n') (subst0 F n)

theorem EqRelSet.neToType (eqrel : EqRelSet) {Γ : Context} {k l : Term}
    (h : eqrel.NeEqRel Γ k l .univ) : eqrel.TypeEqRel Γ k l :=
  eqrel.univ (eqrel.neToTerm h)

/-- Judgmental equality instance of `EqRelSet` (`Definition.Typed.EqRelInstance`). -/
def synEqRel : EqRelSet where
  TypeEqRel := TypeEq
  TermEqRel := TermEq
  NeEqRel := TermEq
  neToTerm h := h
  typeToEq h := h
  termToEq h := h
  univ := .fromUniv
  symmType := .symm
  symmTerm := .symm
  symmNe := .symm
  transType := .trans
  transTerm := .trans
  transNe := .trans
  convTerm := .conv
  convNe := .conv
  wkType := wkTypeEq
  wkTerm := wkTermEq
  wkNe := wkTermEq
  redType := reduction
  redTerm := reductionTerm
  univRefl hΓ := .refl (.univ hΓ)
  natRefl hΓ := .refl (.nat hΓ)
  natTermRefl hΓ := .refl (.nat hΓ)
  piCong := .pi
  piTermCong := .pi
  zeroRefl hΓ := .refl (.zero hΓ)
  succCong := .succ
  etaEq hF hf hg _ _ hfg := .eta hF hf hg hfg
  varRefl := .refl
  appCong := .app
  natrecCong := .natrec

end LogrelMLTT
