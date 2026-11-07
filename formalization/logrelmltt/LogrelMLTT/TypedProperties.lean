/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Typed/Properties.agda, Definition/Typed/Reduction.agda,
Definition/Typed/RedSteps.agda, Definition/Typed/EqualityRelation.agda,
Definition/Typed/EqRelInstance.agda; Σ, Unit and Empty cases follow
mr-ohman/logrel-mltt master, commit 9d6e290064962a1987c9e1a131c2fb967d6ef928.
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
    (sigma : ∀ {Γ F G} (hF : HasType Γ F .univ) (hG : HasType (F :: Γ) G .univ),
      motive Γ F .univ hF → motive (F :: Γ) G .univ hG →
      motive Γ (.sigma F G) .univ (.sigma hF hG))
    (empty : ∀ {Γ} (hΓ : CtxWf Γ), motive Γ .empty .univ (.empty hΓ))
    (unit : ∀ {Γ} (hΓ : CtxWf Γ), motive Γ .unit .univ (.unit hΓ))
    (prod : ∀ {Γ F G t u} (hF : TypeWf Γ F) (hG : TypeWf (F :: Γ) G) (ht : HasType Γ t F)
      (hu : HasType Γ u (subst0 G t)),
      motive Γ t F ht → motive Γ u (subst0 G t) hu →
      motive Γ (.prod t u) (.sigma F G) (.prod hF hG ht hu))
    (fst : ∀ {Γ F G t} (hF : TypeWf Γ F) (hG : TypeWf (F :: Γ) G) (ht : HasType Γ t (.sigma F G)),
      motive Γ t (.sigma F G) ht → motive Γ (.fst t) F (.fst hF hG ht))
    (snd : ∀ {Γ F G t} (hF : TypeWf Γ F) (hG : TypeWf (F :: Γ) G) (ht : HasType Γ t (.sigma F G)),
      motive Γ t (.sigma F G) ht → motive Γ (.snd t) (subst0 G (.fst t)) (.snd hF hG ht))
    (emptyrec : ∀ {Γ A e} (hA : TypeWf Γ A) (he : HasType Γ e .empty),
      motive Γ e .empty he → motive Γ (.emptyrec A e) A (.emptyrec hA he))
    (star : ∀ {Γ} (hΓ : CtxWf Γ), motive Γ .star .unit (.star hΓ))
    (id : ∀ {Γ A t u} (hA : HasType Γ A .univ) (ht : HasType Γ t A) (hu : HasType Γ u A),
      motive Γ A .univ hA → motive Γ t A ht → motive Γ u A hu →
      motive Γ (.id A t u) .univ (.id hA ht hu))
    (rfl : ∀ {Γ A t} (hA : TypeWf Γ A) (ht : HasType Γ t A),
      motive Γ t A ht → motive Γ .rfl (.id A t t) (.rfl hA ht))
    (idrec : ∀ {Γ A P r t u h} (hA : TypeWf Γ A)
      (hP : TypeWf (.id (wk1 A) (wk1 t) (.var 0) :: A :: Γ) P)
      (hr : HasType Γ r (subst2 P t .rfl)) (ht : HasType Γ t A) (hu : HasType Γ u A)
      (hh : HasType Γ h (.id A t u)),
      motive Γ r (subst2 P t .rfl) hr → motive Γ t A ht → motive Γ u A hu →
      motive Γ h (.id A t u) hh →
      motive Γ (.idrec A P r t u h) (subst2 P u h) (.idrec hA hP hr ht hu hh)) :
    ∀ {Γ : Context} {t A : Term} (d : HasType Γ t A), motive Γ t A d
  | _, _, _, .nat hΓ => nat hΓ
  | _, _, _, .pi hF hG => pi hF hG (HasType.indOnly nat pi var lam app zero succ natrec conv sigma
      empty unit prod fst snd emptyrec star id rfl idrec hF) (HasType.indOnly nat pi var lam app
      zero succ natrec conv sigma empty unit prod fst snd emptyrec star id rfl idrec hG)
  | _, _, _, .var hΓ hm => var hΓ hm
  | _, _, _, .lam hF ht => lam hF ht (HasType.indOnly nat pi var lam app zero succ natrec conv
      sigma empty unit prod fst snd emptyrec star id rfl idrec ht)
  | _, _, _, .app hg ha => app hg ha (HasType.indOnly nat pi var lam app zero succ natrec conv
      sigma empty unit prod fst snd emptyrec star id rfl idrec hg) (HasType.indOnly nat pi var lam
      app zero succ natrec conv sigma empty unit prod fst snd emptyrec star id rfl idrec ha)
  | _, _, _, .zero hΓ => zero hΓ
  | _, _, _, .succ hn => succ hn (HasType.indOnly nat pi var lam app zero succ natrec conv sigma
      empty unit prod fst snd emptyrec star id rfl idrec hn)
  | _, _, _, .natrec hG hz hs hn => natrec hG hz hs hn
      (HasType.indOnly nat pi var lam app zero succ natrec conv sigma empty unit prod fst snd
        emptyrec star id rfl idrec hz)
      (HasType.indOnly nat pi var lam app zero succ natrec conv sigma empty unit prod fst snd
        emptyrec star id rfl idrec hs)
      (HasType.indOnly nat pi var lam app zero succ natrec conv sigma empty unit prod fst snd
        emptyrec star id rfl idrec hn)
  | _, _, _, .conv ht hEq => conv ht hEq (HasType.indOnly nat pi var lam app zero succ natrec conv
      sigma empty unit prod fst snd emptyrec star id rfl idrec ht)
  | _, _, _, .sigma hF hG => sigma hF hG (HasType.indOnly nat pi var lam app zero succ natrec conv
      sigma empty unit prod fst snd emptyrec star id rfl idrec hF) (HasType.indOnly nat pi var lam
      app zero succ natrec conv sigma empty unit prod fst snd emptyrec star id rfl idrec hG)
  | _, _, _, .empty hΓ => empty hΓ
  | _, _, _, .unit hΓ => unit hΓ
  | _, _, _, .prod hF hG ht hu => prod hF hG ht hu
      (HasType.indOnly nat pi var lam app zero succ natrec conv sigma empty unit prod fst snd
        emptyrec star id rfl idrec ht)
      (HasType.indOnly nat pi var lam app zero succ natrec conv sigma empty unit prod fst snd
        emptyrec star id rfl idrec hu)
  | _, _, _, .fst hF hG ht => fst hF hG ht (HasType.indOnly nat pi var lam app zero succ natrec
      conv sigma empty unit prod fst snd emptyrec star id rfl idrec ht)
  | _, _, _, .snd hF hG ht => snd hF hG ht (HasType.indOnly nat pi var lam app zero succ natrec
      conv sigma empty unit prod fst snd emptyrec star id rfl idrec ht)
  | _, _, _, .emptyrec hA he => emptyrec hA he (HasType.indOnly nat pi var lam app zero succ
      natrec conv sigma empty unit prod fst snd emptyrec star id rfl idrec he)
  | _, _, _, .star hΓ => star hΓ
  | _, _, _, .id hA ht hu => id hA ht hu
      (HasType.indOnly nat pi var lam app zero succ natrec conv sigma empty unit prod fst snd
        emptyrec star id rfl idrec hA)
      (HasType.indOnly nat pi var lam app zero succ natrec conv sigma empty unit prod fst snd
        emptyrec star id rfl idrec ht)
      (HasType.indOnly nat pi var lam app zero succ natrec conv sigma empty unit prod fst snd
        emptyrec star id rfl idrec hu)
  | _, _, _, .rfl hA ht => rfl hA ht
      (HasType.indOnly nat pi var lam app zero succ natrec conv sigma empty unit prod fst snd
        emptyrec star id rfl idrec ht)
  | _, _, _, .idrec hA hP hr ht hu hh => idrec hA hP hr ht hu hh
      (HasType.indOnly nat pi var lam app zero succ natrec conv sigma empty unit prod fst snd
        emptyrec star id rfl idrec hr)
      (HasType.indOnly nat pi var lam app zero succ natrec conv sigma empty unit prod fst snd
        emptyrec star id rfl idrec ht)
      (HasType.indOnly nat pi var lam app zero succ natrec conv sigma empty unit prod fst snd
        emptyrec star id rfl idrec hu)
      (HasType.indOnly nat pi var lam app zero succ natrec conv sigma empty unit prod fst snd
        emptyrec star id rfl idrec hh)

theorem CtxWf.tail {Γ : Context} {A : Term} : CtxWf (A :: Γ) → CtxWf Γ
  | .cons hΓ _ => hΓ

theorem CtxWf.headWf {Γ : Context} {A : Term} : CtxWf (A :: Γ) → TypeWf Γ A
  | .cons _ hA => hA

mutual
/-- Context well-formedness extracted from a type derivation (`wf`). -/
theorem wfType : ∀ {Γ : Context} {A : Term}, TypeWf Γ A → CtxWf Γ
  | _, _, .nat hΓ => hΓ
  | _, _, .univ hΓ => hΓ
  | _, _, .pi hF _ => wfType hF
  | _, _, .fromUniv hA => wfTerm hA
  | _, _, .empty hΓ => hΓ
  | _, _, .unit hΓ => hΓ
  | _, _, .sigma hF _ => wfType hF
  | _, _, .id hA _ _ => wfType hA

/-- Context well-formedness extracted from a term typing derivation (`wfTerm`). -/
theorem wfTerm : ∀ {Γ : Context} {t A : Term}, HasType Γ t A → CtxWf Γ
  | _, _, _, .nat hΓ => hΓ
  | _, _, _, .pi hF _ => wfTerm hF
  | _, _, _, .var hΓ _ => hΓ
  | _, _, _, .lam hF _ => wfType hF
  | _, _, _, .app _ ha => wfTerm ha
  | _, _, _, .zero hΓ => hΓ
  | _, _, _, .succ hn => wfTerm hn
  | _, _, _, .natrec _ hz _ _ => wfTerm hz
  | _, _, _, .conv ht _ => wfTerm ht
  | _, _, _, .sigma hF _ => wfTerm hF
  | _, _, _, .empty hΓ => hΓ
  | _, _, _, .unit hΓ => hΓ
  | _, _, _, .prod hF _ _ _ => wfType hF
  | _, _, _, .fst hF _ _ => wfType hF
  | _, _, _, .snd hF _ _ => wfType hF
  | _, _, _, .emptyrec hA _ => wfType hA
  | _, _, _, .star hΓ => hΓ
  | _, _, _, .id hA _ _ => wfTerm hA
  | _, _, _, .rfl hA _ => wfType hA
  | _, _, _, .idrec hA _ _ _ _ _ => wfType hA

/-- Context well-formedness extracted from a type equality derivation (`wfEq`). -/
theorem wfTypeEq : ∀ {Γ : Context} {A B : Term}, TypeEq Γ A B → CtxWf Γ
  | _, _, _, .fromUniv h => wfTermEq h
  | _, _, _, .refl hA => wfType hA
  | _, _, _, .symm h => wfTypeEq h
  | _, _, _, .trans h _ => wfTypeEq h
  | _, _, _, .pi hF _ _ => wfType hF
  | _, _, _, .sigma hF _ _ => wfType hF
  | _, _, _, .id hAA' _ _ => wfTypeEq hAA'

/-- Context well-formedness extracted from a term equality derivation (`wfEqTerm`). -/
theorem wfTermEq : ∀ {Γ : Context} {t u A : Term}, TermEq Γ t u A → CtxWf Γ
  | _, _, _, _, .refl ht => wfTerm ht
  | _, _, _, _, .symm h => wfTermEq h
  | _, _, _, _, .trans h _ => wfTermEq h
  | _, _, _, _, .conv h _ => wfTermEq h
  | _, _, _, _, .pi hF _ _ => wfType hF
  | _, _, _, _, .app h _ => wfTermEq h
  | _, _, _, _, .beta hF _ _ => wfType hF
  | _, _, _, _, .eta hF _ _ _ => wfType hF
  | _, _, _, _, .succ h => wfTermEq h
  | _, _, _, _, .natrec _ h _ _ => wfTermEq h
  | _, _, _, _, .natrecZero _ hz _ => wfTerm hz
  | _, _, _, _, .natrecSucc hn _ _ _ => wfTerm hn
  | _, _, _, _, .sigma hF _ _ => wfType hF
  | _, _, _, _, .fst hF _ _ => wfType hF
  | _, _, _, _, .snd hF _ _ => wfType hF
  | _, _, _, _, .sigmaBeta1 hF _ _ _ => wfType hF
  | _, _, _, _, .sigmaBeta2 hF _ _ _ => wfType hF
  | _, _, _, _, .sigmaEta hF _ _ _ _ _ => wfType hF
  | _, _, _, _, .emptyrec h _ => wfTypeEq h
  | _, _, _, _, .etaUnit he _ => wfTerm he
  | _, _, _, _, .id hAA' _ _ => wfTermEq hAA'
  | _, _, _, _, .idrec hA _ _ _ _ _ _ _ => wfType hA
  | _, _, _, _, .idrecBeta hA _ _ _ => wfType hA
end

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
  | .fst hF hG hStep => .fst hF hG (subsetTerm hStep)
  | .snd hF hG hStep => .snd hF hG (subsetTerm hStep)
  | .sigmaBeta1 hF hG ht hu => .sigmaBeta1 hF hG ht hu
  | .sigmaBeta2 hF hG ht hu => .sigmaBeta2 hF hG ht hu
  | .emptyrec hA hStep => .emptyrec (.refl hA) (subsetTerm hStep)
  | .idrec hA hP hr ht hu hStep =>
      .idrec hA (.refl hA) ht (.refl ht) (.refl hP) (.refl hr) (.refl hu) (subsetTerm hStep)
  | .idrecBeta hA hP hr ht _ htu _ =>
      .trans
        (.symm (.idrec hA (.refl hA) ht (.refl ht) (.refl hP) (.refl hr) htu (.refl (.rfl hA ht))))
        (.idrecBeta hA hP hr ht)

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
  | .fst hF hG hStep => .fst hF hG (redFirstTerm hStep)
  | .snd hF hG hStep => .snd hF hG (redFirstTerm hStep)
  | .sigmaBeta1 hF hG ht hu => .fst hF hG (.prod hF hG ht hu)
  | .sigmaBeta2 hF hG ht hu => .snd hF hG (.prod hF hG ht hu)
  | .emptyrec hA hStep => .emptyrec hA (redFirstTerm hStep)
  | .idrec hA hP hr ht hu hStep => .idrec hA hP hr ht hu (redFirstTerm hStep)
  | .idrecBeta hA hP hr ht hu htu hPP =>
      .conv
        (.idrec hA hP hr ht hu (.conv (.rfl hA ht) (.id (.refl hA) (.refl ht) htu)))
        (.symm hPP)

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
    | sigma _ _ _ _ => intro _ hn; cases hn
    | empty _ => intro _ hn; cases hn
    | unit _ => intro _ hn; cases hn
    | prod _ _ _ _ _ _ => intro _ hn; cases hn
    | fst _ _ _ iht =>
        intro hΓ hn
        cases hn with
        | fst hn' => exact iht hΓ hn'
    | snd _ _ _ iht =>
        intro hΓ hn
        cases hn with
        | snd hn' => exact iht hΓ hn'
    | emptyrec _ _ ihe =>
        intro hΓ hn
        cases hn with
        | emptyrec hn' => exact ihe hΓ hn'
    | star _ => intro _ hn; cases hn
    | id _ _ _ _ _ _ => intro _ hn; cases hn
    | rfl _ _ _ => intro _ hn; cases hn
    | idrec _ _ _ _ _ _ _ _ _ ihh =>
        intro hΓ hn
        cases hn with
        | idrec hn' => exact ihh hΓ hn'
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
  | fst _ _ _ ih =>
      cases hn with
      | fst hn' => exact ih hn'
  | snd _ _ _ ih =>
      cases hn with
      | snd hn' => exact ih hn'
  | sigmaBeta1 _ _ _ _ =>
      cases hn with
      | fst hn' => cases hn'
  | sigmaBeta2 _ _ _ _ =>
      cases hn with
      | snd hn' => cases hn'
  | emptyrec _ _ ih =>
      cases hn with
      | emptyrec hn' => exact ih hn'
  | idrec _ _ _ _ _ _ ih =>
      cases hn with
      | idrec hn' => exact ih hn'
  | idrecBeta _ _ _ _ _ _ _ =>
      cases hn with
      | idrec hn' => cases hn'

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
  | fst _ _ hStep _ =>
      cases hw with
      | neutral hn =>
          cases hn with
          | fst hn' => exact neRedTerm hStep hn'
  | snd _ _ hStep _ =>
      cases hw with
      | neutral hn =>
          cases hn with
          | snd hn' => exact neRedTerm hStep hn'
  | sigmaBeta1 _ _ _ _ =>
      cases hw with
      | neutral hn =>
          cases hn with
          | fst hn' => cases hn'
  | sigmaBeta2 _ _ _ _ =>
      cases hw with
      | neutral hn =>
          cases hn with
          | snd hn' => cases hn'
  | emptyrec _ hStep _ =>
      cases hw with
      | neutral hn =>
          cases hn with
          | emptyrec hn' => exact neRedTerm hStep hn'
  | idrec _ _ _ _ _ hStep _ =>
      cases hw with
      | neutral hn =>
          cases hn with
          | idrec hn' => exact neRedTerm hStep hn'
  | idrecBeta _ _ _ _ _ _ _ =>
      cases hw with
      | neutral hn =>
          cases hn with
          | idrec hn' => cases hn'

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

/-- Untyped shadow of the typed weak-head reduction relation, used to prove determinism. -/
inductive UStep : Term → Term → Prop where
  | app {t u a} : UStep t u → UStep (.app t a) (.app u a)
  | beta {t a} : UStep (.app (.lam t) a) (subst0 t a)
  | natrec {F z s n n'} : UStep n n' → UStep (.natrec F z s n) (.natrec F z s n')
  | natrecZero {F z s} : UStep (.natrec F z s .zero) z
  | natrecSucc {F z s n} : UStep (.natrec F z s (.succ n)) (.app (.app s n) (.natrec F z s n))
  | fst {t t'} : UStep t t' → UStep (.fst t) (.fst t')
  | snd {t t'} : UStep t t' → UStep (.snd t) (.snd t')
  | sigmaBeta1 {t u} : UStep (.fst (.prod t u)) t
  | sigmaBeta2 {t u} : UStep (.snd (.prod t u)) u
  | emptyrec {A n n'} : UStep n n' → UStep (.emptyrec A n) (.emptyrec A n')
  | idrec {A P r t u h h'} : UStep h h' → UStep (.idrec A P r t u h) (.idrec A P r t u h')
  | idrecBeta {A P r t u} : UStep (.idrec A P r t u .rfl) r

theorem Step.toU {Γ : Context} {t u A : Term} (d : Step Γ t u A) : UStep t u := by
  induction d with
  | conv _ _ ih => exact ih
  | app _ _ ih => exact .app ih
  | beta _ _ _ => exact .beta
  | natrec _ _ _ _ ih => exact .natrec ih
  | natrecZero _ _ _ => exact .natrecZero
  | natrecSucc _ _ _ _ => exact .natrecSucc
  | fst _ _ _ ih => exact .fst ih
  | snd _ _ _ ih => exact .snd ih
  | sigmaBeta1 _ _ _ _ => exact .sigmaBeta1
  | sigmaBeta2 _ _ _ _ => exact .sigmaBeta2
  | emptyrec _ _ ih => exact .emptyrec ih
  | idrec _ _ _ _ _ _ ih => exact .idrec ih
  | idrecBeta _ _ _ _ _ _ _ => exact .idrecBeta

theorem UStep.not_whnf {t u : Term} (d : UStep t u) (hw : Whnf t) : False := by
  induction d with
  | app d ih =>
      cases hw with | neutral hn => cases hn with | app hn' => exact ih (.neutral hn')
  | beta => cases hw with | neutral hn => cases hn with | app hn' => cases hn'
  | natrec d ih =>
      cases hw with | neutral hn => cases hn with | natrec hn' => exact ih (.neutral hn')
  | natrecZero => cases hw with | neutral hn => cases hn with | natrec hn' => cases hn'
  | natrecSucc => cases hw with | neutral hn => cases hn with | natrec hn' => cases hn'
  | fst d ih =>
      cases hw with | neutral hn => cases hn with | fst hn' => exact ih (.neutral hn')
  | snd d ih =>
      cases hw with | neutral hn => cases hn with | snd hn' => exact ih (.neutral hn')
  | sigmaBeta1 => cases hw with | neutral hn => cases hn with | fst hn' => cases hn'
  | sigmaBeta2 => cases hw with | neutral hn => cases hn with | snd hn' => cases hn'
  | emptyrec d ih =>
      cases hw with | neutral hn => cases hn with | emptyrec hn' => exact ih (.neutral hn')
  | idrec d ih =>
      cases hw with | neutral hn => cases hn with | idrec hn' => exact ih (.neutral hn')
  | idrecBeta => cases hw with | neutral hn => cases hn with | idrec hn' => cases hn'

theorem UStep.det {t u u' : Term} (d₁ : UStep t u) (d₂ : UStep t u') : u = u' := by
  induction d₁ generalizing u' with
  | app d ih =>
      cases d₂ with
      | app d₂ => rw [ih d₂]
      | beta => exact (d.not_whnf .lam).elim
  | beta =>
      cases d₂ with
      | app d₂ => exact (d₂.not_whnf .lam).elim
      | beta => rfl
  | natrec d ih =>
      cases d₂ with
      | natrec d₂ => rw [ih d₂]
      | natrecZero => exact (d.not_whnf .zero).elim
      | natrecSucc => exact (d.not_whnf .succ).elim
  | natrecZero =>
      cases d₂ with
      | natrec d₂ => exact (d₂.not_whnf .zero).elim
      | natrecZero => rfl
  | natrecSucc =>
      cases d₂ with
      | natrec d₂ => exact (d₂.not_whnf .succ).elim
      | natrecSucc => rfl
  | fst d ih =>
      cases d₂ with
      | fst d₂ => rw [ih d₂]
      | sigmaBeta1 => exact (d.not_whnf .prod).elim
  | snd d ih =>
      cases d₂ with
      | snd d₂ => rw [ih d₂]
      | sigmaBeta2 => exact (d.not_whnf .prod).elim
  | sigmaBeta1 =>
      cases d₂ with
      | fst d₂ => exact (d₂.not_whnf .prod).elim
      | sigmaBeta1 => rfl
  | sigmaBeta2 =>
      cases d₂ with
      | snd d₂ => exact (d₂.not_whnf .prod).elim
      | sigmaBeta2 => rfl
  | emptyrec d ih =>
      cases d₂ with
      | emptyrec d₂ => rw [ih d₂]
  | idrec d ih =>
      cases d₂ with
      | idrec d₂ => rw [ih d₂]
      | idrecBeta => exact (d.not_whnf .rfl).elim
  | idrecBeta =>
      cases d₂ with
      | idrec d₂ => exact (d₂.not_whnf .rfl).elim
      | idrecBeta => rfl

/-- Determinism of single-step term reduction (`whrDetTerm`, Lemma 2.5). -/
theorem whrDetTerm {Γ : Context} {t u A u' A' : Term}
    (d₁ : Step Γ t u A) (d₂ : Step Γ t u' A') : u = u' :=
  d₁.toU.det d₂.toU

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
    | sigma _ _ _ _ => intro hu; cases hu
    | empty _ => intro hu; cases hu
    | unit _ => intro hu; cases hu
    | prod _ _ _ _ _ _ => intro hu; cases hu
    | fst _ _ _ _ => intro hu; cases hu
    | snd _ _ _ _ => intro hu; cases hu
    | emptyrec _ _ _ => intro hu; cases hu
    | star _ => intro hu; cases hu
    | id _ _ _ _ _ _ => intro hu; cases hu
    | rfl _ _ _ => intro hu; cases hu
    | idrec _ _ _ _ _ _ _ _ _ _ => intro hu; cases hu
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
    | sigma _ _ _ _ => intro h; cases h
    | empty _ => intro h; cases h
    | unit _ => intro h; cases h
    | prod _ _ _ _ _ _ => intro h; cases h
    | fst _ _ _ _ => intro h; cases h
    | snd _ _ _ _ => intro h; cases h
    | emptyrec _ _ _ => intro h; cases h
    | star _ => intro h; cases h
    | id _ _ _ _ _ _ => intro h; cases h
    | rfl _ _ _ => intro h; cases h
    | idrec _ _ _ _ _ _ _ _ _ _ => intro h; cases h
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
  | fst _ _ _ _ => cases heq
  | snd _ _ _ _ => cases heq
  | sigmaBeta1 _ _ ht _ =>
      subst heq
      exact UnotInA ht
  | sigmaBeta2 _ _ _ hu =>
      subst heq
      exact UnotInA hu
  | emptyrec _ _ _ => cases heq
  | idrec _ _ _ _ _ _ _ => cases heq
  | idrecBeta _ _ hr _ _ _ _ =>
      subst heq
      exact UnotInA hr

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

/-- First-projection congruence for multi-step reduction. -/
theorem Star.fst {Γ : Context} {F G t t' : Term} (hF : TypeWf Γ F) (hG : TypeWf (F :: Γ) G)
    (d : Star Γ t t' (.sigma F G)) : Star Γ (.fst t) (.fst t') F := by
  generalize hs : Term.sigma F G = S at d
  induction d with
  | refl ht =>
      subst hs
      exact .refl (.fst hF hG ht)
  | step h₁ _ ih =>
      subst hs
      exact .step (.fst hF hG h₁) (ih rfl)

/-- Emptyrec congruence for multi-step reduction. -/
theorem Star.emptyrec {Γ : Context} {A n n' : Term} (hA : TypeWf Γ A)
    (d : Star Γ n n' .empty) : Star Γ (.emptyrec A n) (.emptyrec A n') A := by
  generalize hs : Term.empty = S at d
  induction d with
  | refl ht =>
      subst hs
      exact .refl (.emptyrec hA ht)
  | step h₁ _ ih =>
      subst hs
      exact .step (.emptyrec hA h₁) (ih rfl)

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
  emptyRefl : ∀ {Γ}, CtxWf Γ → TypeEqRel Γ .empty .empty
  emptyTermRefl : ∀ {Γ}, CtxWf Γ → TermEqRel Γ .empty .empty .univ
  unitRefl : ∀ {Γ}, CtxWf Γ → TypeEqRel Γ .unit .unit
  unitTermRefl : ∀ {Γ}, CtxWf Γ → TermEqRel Γ .unit .unit .univ
  etaUnit : ∀ {Γ e e'}, HasType Γ e .unit → HasType Γ e' .unit → TermEqRel Γ e e' .unit
  sigmaCong : ∀ {Γ F G H E}, TypeWf Γ F → TypeEqRel Γ F H → TypeEqRel (F :: Γ) G E →
    TypeEqRel Γ (.sigma F G) (.sigma H E)
  sigmaTermCong : ∀ {Γ F G H E}, TypeWf Γ F → TermEqRel Γ F H .univ →
    TermEqRel (F :: Γ) G E .univ → TermEqRel Γ (.sigma F G) (.sigma H E) .univ
  sigmaEta : ∀ {Γ p r F G}, TypeWf Γ F → TypeWf (F :: Γ) G →
    HasType Γ p (.sigma F G) → HasType Γ r (.sigma F G) → ProductView p → ProductView r →
    TermEqRel Γ (.fst p) (.fst r) F → TermEqRel Γ (.snd p) (.snd r) (subst0 G (.fst p)) →
    TermEqRel Γ p r (.sigma F G)
  fstCong : ∀ {Γ p r F G}, TypeWf Γ F → TypeWf (F :: Γ) G → NeEqRel Γ p r (.sigma F G) →
    NeEqRel Γ (.fst p) (.fst r) F
  sndCong : ∀ {Γ p r F G}, TypeWf Γ F → TypeWf (F :: Γ) G → NeEqRel Γ p r (.sigma F G) →
    NeEqRel Γ (.snd p) (.snd r) (subst0 G (.fst p))
  emptyrecCong : ∀ {Γ n n' F F'}, TypeEqRel Γ F F' → NeEqRel Γ n n' .empty →
    NeEqRel Γ (.emptyrec F n) (.emptyrec F' n') F
  idCong : ∀ {Γ A A' t t' u u'}, TypeEqRel Γ A A' → TermEqRel Γ t t' A →
    TermEqRel Γ u u' A → TypeEqRel Γ (.id A t u) (.id A' t' u')
  idTermCong : ∀ {Γ A A' t t' u u'}, TermEqRel Γ A A' .univ → TermEqRel Γ t t' A →
    TermEqRel Γ u u' A → TermEqRel Γ (.id A t u) (.id A' t' u') .univ
  rflRefl : ∀ {Γ A t}, TypeWf Γ A → HasType Γ t A → TermEqRel Γ .rfl .rfl (.id A t t)
  idrecCong : ∀ {Γ A A' P P' r r' t t' u u' h h'},
    TypeWf Γ A → TypeEqRel Γ A A' → HasType Γ t A → TermEqRel Γ t t' A →
    TypeEqRel (.id (wk1 A) (wk1 t) (.var 0) :: A :: Γ) P P' →
    TermEqRel Γ r r' (subst2 P t .rfl) →
    TermEqRel Γ u u' A → NeEqRel Γ h h' (.id A t u) →
    NeEqRel Γ (.idrec A P r t u h) (.idrec A' P' r' t' u' h') (subst2 P u h)

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
  emptyRefl hΓ := .refl (.empty hΓ)
  emptyTermRefl hΓ := .refl (.empty hΓ)
  unitRefl hΓ := .refl (.unit hΓ)
  unitTermRefl hΓ := .refl (.unit hΓ)
  etaUnit := .etaUnit
  sigmaCong := .sigma
  sigmaTermCong := .sigma
  sigmaEta hF hG hp hr _ _ hfst hsnd := .sigmaEta hF hG hp hr hfst hsnd
  fstCong := .fst
  sndCong := .snd
  emptyrecCong := .emptyrec
  idCong := .id
  idTermCong := .id
  rflRefl hA ht := .refl (.rfl hA ht)
  idrecCong := .idrec

end LogrelMLTT
