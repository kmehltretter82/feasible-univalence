/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Conversion.agda, Definition/Conversion/Whnf.agda,
Definition/Conversion/Reduction.agda, Definition/Conversion/Weakening.agda,
plus executable adequacy and fuel stability for LogrelMLTT/Algorithm.lean.
-/
import LogrelMLTT.TypedProperties
import LogrelMLTT.Algorithm

namespace LogrelMLTT

mutual
  /-- Algorithmic equality of neutrals (`Γ ⊢ k ~ l ↑ A`). -/
  inductive ConvNeUp : Context → Term → Term → Term → Prop where
    | var {Γ x y A} : HasType Γ (.var x) A → x = y → ConvNeUp Γ (.var x) (.var y) A
    | app {Γ k l t v F G} :
        ConvNeDown Γ k l (.pi F G) →
        ConvTermUp Γ t v F →
        ConvNeUp Γ (.app k t) (.app l v) (subst0 G t)
    | natrec {Γ k l h g a₀ b₀ F G} :
        ConvTypeUp (.nat :: Γ) F G →
        ConvTermUp Γ a₀ b₀ (subst0 F .zero) →
        ConvTermUp Γ h g (recStepType F) →
        ConvNeDown Γ k l .nat →
        ConvNeUp Γ (.natrec F a₀ h k) (.natrec G b₀ g l) (subst0 F k)

  /-- Algorithmic equality of neutrals with type in WHNF (`Γ ⊢ k ~ l ↓ B`). -/
  inductive ConvNeDown : Context → Term → Term → Term → Prop where
    | mk {Γ k l A B} :
        TypeStar Γ A B →
        Whnf B →
        ConvNeUp Γ k l A →
        ConvNeDown Γ k l B

  /-- Algorithmic equality of types (`Γ ⊢ A [conv↑] B`). -/
  inductive ConvTypeUp : Context → Term → Term → Prop where
    | mk {Γ A B A' B'} :
        TypeStar Γ A A' →
        TypeStar Γ B B' →
        Whnf A' →
        Whnf B' →
        ConvTypeDown Γ A' B' →
        ConvTypeUp Γ A B

  /-- Algorithmic equality of types in WHNF (`Γ ⊢ A [conv↓] B`). -/
  inductive ConvTypeDown : Context → Term → Term → Prop where
    | univRefl {Γ} : CtxWf Γ → ConvTypeDown Γ .univ .univ
    | natRefl {Γ} : CtxWf Γ → ConvTypeDown Γ .nat .nat
    | ne {Γ K L} : ConvNeDown Γ K L .univ → ConvTypeDown Γ K L
    | piCong {Γ F G H E} :
        TypeWf Γ F →
        ConvTypeUp Γ F H →
        ConvTypeUp (F :: Γ) G E →
        ConvTypeDown Γ (.pi F G) (.pi H E)

  /-- Algorithmic equality of terms (`Γ ⊢ t [conv↑] u ∷ A`). -/
  inductive ConvTermUp : Context → Term → Term → Term → Prop where
    | mk {Γ t u A B t' u'} :
        TypeStar Γ A B →
        Star Γ t t' B →
        Star Γ u u' B →
        Whnf B →
        Whnf t' →
        Whnf u' →
        ConvTermDown Γ t' u' B →
        ConvTermUp Γ t u A

  /-- Algorithmic equality of terms and types in WHNF (`Γ ⊢ t [conv↓] u ∷ A`). -/
  inductive ConvTermDown : Context → Term → Term → Term → Prop where
    | natIns {Γ k l} : ConvNeDown Γ k l .nat → ConvTermDown Γ k l .nat
    | neIns {Γ k l M N} :
        HasType Γ k N →
        HasType Γ l N →
        Neutral N →
        ConvNeDown Γ k l M →
        ConvTermDown Γ k l N
    | univ {Γ A B} :
        HasType Γ A .univ →
        HasType Γ B .univ →
        ConvTypeDown Γ A B →
        ConvTermDown Γ A B .univ
    | zeroRefl {Γ} : CtxWf Γ → ConvTermDown Γ .zero .zero .nat
    | succCong {Γ m n} : ConvTermUp Γ m n .nat → ConvTermDown Γ (.succ m) (.succ n) .nat
    | etaEq {Γ f g F G} :
        TypeWf Γ F →
        HasType Γ f (.pi F G) →
        HasType Γ g (.pi F G) →
        Whnf f →
        Whnf g →
        ConvTermUp (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G →
        ConvTermDown Γ f g (.pi F G)
end

/-- Extraction of neutrality from `ConvNeUp` (`ne~↑`). -/
theorem neConvNeUp {Γ : Context} {t u A : Term} (d : ConvNeUp Γ t u A) :
    Neutral t ∧ Neutral u :=
  ConvNeUp.rec
    (motive_1 := fun _ t u _ _ ↦ Neutral t ∧ Neutral u)
    (motive_2 := fun _ t u A _ ↦ Whnf A ∧ Neutral t ∧ Neutral u)
    (motive_3 := fun _ _ _ _ ↦ True)
    (motive_4 := fun _ _ _ _ ↦ True)
    (motive_5 := fun _ _ _ _ _ ↦ True)
    (motive_6 := fun _ _ _ _ _ ↦ True)
    (fun {_Γ x y _} _ _ ↦ ⟨.var x, .var y⟩)
    (fun _ _ ihk _ ↦ ⟨.app ihk.2.1, .app ihk.2.2⟩)
    (fun _ _ _ _ _ _ _ ihk ↦ ⟨.natrec ihk.2.1, .natrec ihk.2.2⟩)
    (fun _ hw _ ih ↦ ⟨hw, ih⟩)
    (fun _ _ _ _ _ _ ↦ trivial)
    (fun _ ↦ trivial)
    (fun _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ ↦ trivial)
    d

/-- Extraction of WHNF and neutrality from `ConvNeDown` (`ne~↓`). -/
theorem neConvNeDown {Γ : Context} {t u A : Term} :
    ConvNeDown Γ t u A → Whnf A ∧ Neutral t ∧ Neutral u
  | .mk _ hw hne => ⟨hw, neConvNeUp hne⟩

/-- Extraction of WHNF from `ConvTypeDown` (`whnfConv↓`). -/
theorem whnfConvTypeDown {Γ : Context} {A B : Term} :
    ConvTypeDown Γ A B → Whnf A ∧ Whnf B
  | .univRefl _ => ⟨.univ, .univ⟩
  | .natRefl _ => ⟨.nat, .nat⟩
  | .ne hne =>
      let ⟨_, neK, neL⟩ := neConvNeDown hne
      ⟨.neutral neK, .neutral neL⟩
  | .piCong _ _ _ => ⟨.pi, .pi⟩

/-- Extraction of WHNF from `ConvTermDown` (`whnfConv↓Term`). -/
theorem whnfConvTermDown {Γ : Context} {t u A : Term} :
    ConvTermDown Γ t u A → Whnf A ∧ Whnf t ∧ Whnf u
  | .natIns hne =>
      let ⟨_, neK, neL⟩ := neConvNeDown hne
      ⟨.nat, .neutral neK, .neutral neL⟩
  | .neIns _ _ neN hne =>
      let ⟨_, neK, neL⟩ := neConvNeDown hne
      ⟨.neutral neN, .neutral neK, .neutral neL⟩
  | .univ _ _ hAB => ⟨.univ, whnfConvTypeDown hAB⟩
  | .zeroRefl _ => ⟨.nat, .zero, .zero⟩
  | .succCong _ => ⟨.nat, .succ, .succ⟩
  | .etaEq _ _ _ wf wg _ => ⟨.pi, wf, wg⟩

/-- Weak-head expansion of algorithmic type equality (`reductionConv↑`). -/
theorem reductionConvTypeUp {Γ : Context} {A A' B B' : Term}
    (DA : TypeStar Γ A A') (DB : TypeStar Γ B B')
    (whnfA' : Whnf A') (whnfB' : Whnf B')
    (h : ConvTypeUp Γ A' B') : ConvTypeUp Γ A B := by
  rcases h with ⟨DA'', DB'', whnfA'', whnfB'', hDown⟩
  have eqA := whnfRedStar DA'' whnfA'
  have eqB := whnfRedStar DB'' whnfB'
  subst eqA eqB
  exact .mk DA DB whnfA'' whnfB'' hDown

/-- Weak-head expansion of algorithmic term equality (`reductionConv↑Term`). -/
theorem reductionConvTermUp {Γ : Context} {t t' u u' A B : Term}
    (DA : TypeStar Γ A B) (dt : Star Γ t t' B) (du : Star Γ u u' B)
    (whnfB : Whnf B) (whnft' : Whnf t') (whnfu' : Whnf u')
    (h : ConvTermUp Γ t' u' B) : ConvTermUp Γ t u A := by
  rcases h with ⟨DB', dt'', du'', whnfB', whnft'', whnfu'', hDown⟩
  have eqB := whnfRedStar DB' whnfB
  subst eqB
  have eqt := whnfRedStarTerm dt'' whnft'
  have equ := whnfRedStarTerm du'' whnfu'
  subst eqt equ
  exact .mk DA dt du whnfB' whnft'' whnfu'' hDown

private abbrev WkConvNeUpMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → ConvNeUp Δ (wk ρ t) (wk ρ u) (wk ρ A)

private abbrev WkConvNeDownMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → ConvNeDown Δ (wk ρ t) (wk ρ u) (wk ρ A)

private abbrev WkConvTypeUpMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → ConvTypeUp Δ (wk ρ A) (wk ρ B)

private abbrev WkConvTypeDownMotive (Γ : Context) (A B : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → ConvTypeDown Δ (wk ρ A) (wk ρ B)

private abbrev WkConvTermUpMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → ConvTermUp Δ (wk ρ t) (wk ρ u) (wk ρ A)

private abbrev WkConvTermDownMotive (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {ρ : Wk}, WkCtx ρ Δ Γ → CtxWf Δ → ConvTermDown Δ (wk ρ t) (wk ρ u) (wk ρ A)

private theorem wkConv_var_case {Γ : Context} {x y : Nat} {A : Term}
    (hx : HasType Γ (.var x) A) (hxy : x = y) :
    WkConvNeUpMotive Γ (.var x) (.var y) A :=
  fun {_Δ ρ} hρ hΔ ↦ .var (wkHasType hρ hΔ hx) (congrArg (wkVar ρ) hxy)

private theorem wkConv_app_case {Γ : Context} {k l t v F G : Term}
    (_hkl : ConvNeDown Γ k l (.pi F G)) (_htv : ConvTermUp Γ t v F)
    (ihkl : WkConvNeDownMotive Γ k l (.pi F G))
    (ihtv : WkConvTermUpMotive Γ t v F) :
    WkConvNeUpMotive Γ (.app k t) (.app l v) (subst0 G t) := by
  intro Δ ρ hρ hΔ
  rw [wk, wk, wk_beta (ρ := ρ) (a := t) G]
  exact .app (ihkl hρ hΔ) (ihtv hρ hΔ)

private theorem wkConv_natrec_case {Γ : Context} {k l h g a₀ b₀ F G : Term}
    (_hFG : ConvTypeUp (.nat :: Γ) F G)
    (_hab : ConvTermUp Γ a₀ b₀ (subst0 F .zero))
    (_hhg : ConvTermUp Γ h g (recStepType F))
    (_hkl : ConvNeDown Γ k l .nat)
    (ihFG : WkConvTypeUpMotive (.nat :: Γ) F G)
    (ihab : WkConvTermUpMotive Γ a₀ b₀ (subst0 F .zero))
    (ihhg : WkConvTermUpMotive Γ h g (recStepType F))
    (ihkl : WkConvNeDownMotive Γ k l .nat) :
    WkConvNeUpMotive Γ (.natrec F a₀ h k) (.natrec G b₀ g l) (subst0 F k) := by
  intro Δ ρ hρ hΔ
  have hρFG : ConvTypeUp (.nat :: Δ) (wk (.lift ρ) F) (wk (.lift ρ) G) :=
    ihFG (WkCtx.lift (A := .nat) hρ) (.cons hΔ (.nat hΔ))
  have hρab : ConvTermUp Δ (wk ρ a₀) (wk ρ b₀) (subst0 (wk (.lift ρ) F) .zero) := by
    have h' := ihab hρ hΔ
    rw [wk_beta (ρ := ρ) (a := .zero) F] at h'
    exact h'
  have hρhg : ConvTermUp Δ (wk ρ h) (wk ρ g) (recStepType (wk (.lift ρ) F)) := by
    have h' := ihhg hρ hΔ
    rw [wk_beta_natrec ρ F] at h'
    exact h'
  have hρkl : ConvNeDown Δ (wk ρ k) (wk ρ l) .nat := ihkl hρ hΔ
  rw [wk, wk, wk_beta (ρ := ρ) (a := k) F]
  exact .natrec hρFG hρab hρhg hρkl

private theorem wkConv_neDown_case {Γ : Context} {k l A B : Term}
    (D : TypeStar Γ A B) (hw : Whnf B) (_hkl : ConvNeUp Γ k l A)
    (ihkl : WkConvNeUpMotive Γ k l A) :
    WkConvNeDownMotive Γ k l B :=
  fun {_Δ ρ} hρ hΔ ↦ .mk (wkTypeStar hρ hΔ D) (hw.wk ρ) (ihkl hρ hΔ)

private theorem wkConv_typeUp_case {Γ : Context} {A B A' B' : Term}
    (DA : TypeStar Γ A A') (DB : TypeStar Γ B B')
    (hwA : Whnf A') (hwB : Whnf B')
    (_hAB : ConvTypeDown Γ A' B')
    (ihAB : WkConvTypeDownMotive Γ A' B') :
    WkConvTypeUpMotive Γ A B :=
  fun {_Δ ρ} hρ hΔ ↦
    .mk (wkTypeStar hρ hΔ DA) (wkTypeStar hρ hΔ DB) (hwA.wk ρ) (hwB.wk ρ) (ihAB hρ hΔ)

private theorem wkConv_univRefl_case {Γ : Context} (_hΓ : CtxWf Γ) :
    WkConvTypeDownMotive Γ .univ .univ :=
  fun _ hΔ ↦ .univRefl hΔ

private theorem wkConv_natRefl_case {Γ : Context} (_hΓ : CtxWf Γ) :
    WkConvTypeDownMotive Γ .nat .nat :=
  fun _ hΔ ↦ .natRefl hΔ

private theorem wkConv_neType_case {Γ : Context} {K L : Term}
    (_hKL : ConvNeDown Γ K L .univ) (ihKL : WkConvNeDownMotive Γ K L .univ) :
    WkConvTypeDownMotive Γ K L :=
  fun hρ hΔ ↦ .ne (ihKL hρ hΔ)

private theorem wkConv_piCong_case {Γ : Context} {F G H E : Term}
    (hF : TypeWf Γ F) (_hFH : ConvTypeUp Γ F H) (_hGE : ConvTypeUp (F :: Γ) G E)
    (ihFH : WkConvTypeUpMotive Γ F H)
    (ihGE : WkConvTypeUpMotive (F :: Γ) G E) :
    WkConvTypeDownMotive Γ (.pi F G) (.pi H E) :=
  fun hρ hΔ ↦
    let hρF := wkTypeWf hρ hΔ hF
    .piCong hρF (ihFH hρ hΔ) (ihGE (.lift hρ) (.cons hΔ hρF))

private theorem wkConv_termUp_case {Γ : Context} {t u A B t' u' : Term}
    (DA : TypeStar Γ A B) (dt : Star Γ t t' B) (du : Star Γ u u' B)
    (hwB : Whnf B) (hwt : Whnf t') (hwu : Whnf u')
    (_htu : ConvTermDown Γ t' u' B)
    (ihtu : WkConvTermDownMotive Γ t' u' B) :
    WkConvTermUpMotive Γ t u A :=
  fun {_Δ ρ} hρ hΔ ↦
    .mk (wkTypeStar hρ hΔ DA) (wkStar hρ hΔ dt) (wkStar hρ hΔ du)
      (hwB.wk ρ) (hwt.wk ρ) (hwu.wk ρ) (ihtu hρ hΔ)

private theorem wkConv_natIns_case {Γ : Context} {k l : Term}
    (_hkl : ConvNeDown Γ k l .nat) (ihkl : WkConvNeDownMotive Γ k l .nat) :
    WkConvTermDownMotive Γ k l .nat :=
  fun hρ hΔ ↦ .natIns (ihkl hρ hΔ)

private theorem wkConv_neIns_case {Γ : Context} {k l M N : Term}
    (hk : HasType Γ k N) (hl : HasType Γ l N) (neN : Neutral N)
    (_hkl : ConvNeDown Γ k l M) (ihkl : WkConvNeDownMotive Γ k l M) :
    WkConvTermDownMotive Γ k l N :=
  fun {_Δ ρ} hρ hΔ ↦
    .neIns (wkHasType hρ hΔ hk) (wkHasType hρ hΔ hl) (neN.wk ρ) (ihkl hρ hΔ)

private theorem wkConv_univ_case {Γ : Context} {A B : Term}
    (hA : HasType Γ A .univ) (hB : HasType Γ B .univ)
    (_hAB : ConvTypeDown Γ A B) (ihAB : WkConvTypeDownMotive Γ A B) :
    WkConvTermDownMotive Γ A B .univ :=
  fun hρ hΔ ↦ .univ (wkHasType hρ hΔ hA) (wkHasType hρ hΔ hB) (ihAB hρ hΔ)

private theorem wkConv_zeroRefl_case {Γ : Context} (_hΓ : CtxWf Γ) :
    WkConvTermDownMotive Γ .zero .zero .nat :=
  fun _ hΔ ↦ .zeroRefl hΔ

private theorem wkConv_succCong_case {Γ : Context} {m n : Term}
    (_hmn : ConvTermUp Γ m n .nat) (ihmn : WkConvTermUpMotive Γ m n .nat) :
    WkConvTermDownMotive Γ (.succ m) (.succ n) .nat :=
  fun hρ hΔ ↦ .succCong (ihmn hρ hΔ)

private theorem wkConv_etaEq_case {Γ : Context} {f g F G : Term}
    (hF : TypeWf Γ F) (hf : HasType Γ f (.pi F G)) (hg : HasType Γ g (.pi F G))
    (hwf : Whnf f) (hwg : Whnf g)
    (_hfg : ConvTermUp (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G)
    (ihfg : WkConvTermUpMotive (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G) :
    WkConvTermDownMotive Γ f g (.pi F G) := by
  intro Δ ρ hρ hΔ
  let hρF := wkTypeWf hρ hΔ hF
  have hfg' : ConvTermUp (wk ρ F :: Δ)
      (.app (wk (.lift ρ) (wk1 f)) (.var 0))
      (.app (wk (.lift ρ) (wk1 g)) (.var 0))
      (wk (.lift ρ) G) :=
    ihfg (.lift hρ) (.cons hΔ hρF)
  rw [← wk1_wk_eq_lift_wk1 ρ f, ← wk1_wk_eq_lift_wk1 ρ g] at hfg'
  exact .etaEq hρF (wkHasType hρ hΔ hf) (wkHasType hρ hΔ hg)
    (hwf.wk ρ) (hwg.wk ρ) hfg'

/-- Weakening of `ConvNeUp` (`wk~↑`). -/
theorem wkConvNeUp {Γ Δ : Context} {t u A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (d : ConvNeUp Γ t u A) :
    ConvNeUp Δ (wk ρ t) (wk ρ u) (wk ρ A) :=
  (ConvNeUp.rec
    (motive_1 := fun Γ t u A _ ↦ WkConvNeUpMotive Γ t u A)
    (motive_2 := fun Γ t u A _ ↦ WkConvNeDownMotive Γ t u A)
    (motive_3 := fun Γ A B _ ↦ WkConvTypeUpMotive Γ A B)
    (motive_4 := fun Γ A B _ ↦ WkConvTypeDownMotive Γ A B)
    (motive_5 := fun Γ t u A _ ↦ WkConvTermUpMotive Γ t u A)
    (motive_6 := fun Γ t u A _ ↦ WkConvTermDownMotive Γ t u A)
    (fun hx hxy ↦ wkConv_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ wkConv_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      wkConv_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ wkConv_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB hAB ihAB ↦ wkConv_typeUp_case DA DB hwA hwB hAB ihAB)
    (fun hΓ ↦ wkConv_univRefl_case hΓ)
    (fun hΓ ↦ wkConv_natRefl_case hΓ)
    (fun hKL ihKL ↦ wkConv_neType_case hKL ihKL)
    (fun hF hFH hGE ihFH ihGE ↦ wkConv_piCong_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu htu ihtu ↦
      wkConv_termUp_case DA dt du hwB hwt hwu htu ihtu)
    (fun hkl ihkl ↦ wkConv_natIns_case hkl ihkl)
    (fun hk hl neN hkl ihkl ↦ wkConv_neIns_case hk hl neN hkl ihkl)
    (fun hA hB hAB ihAB ↦ wkConv_univ_case hA hB hAB ihAB)
    (fun hΓ ↦ wkConv_zeroRefl_case hΓ)
    (fun hmn ihmn ↦ wkConv_succCong_case hmn ihmn)
    (fun hF hf hg hwf hwg hfg ihfg ↦ wkConv_etaEq_case hF hf hg hwf hwg hfg ihfg)
    d) hρ hΔ

/-- Weakening of `ConvNeDown` (`wk~↓`). -/
theorem wkConvNeDown {Γ Δ : Context} {t u A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) :
    ConvNeDown Γ t u A → ConvNeDown Δ (wk ρ t) (wk ρ u) (wk ρ A)
  | .mk D hw hkl => .mk (wkTypeStar hρ hΔ D) (hw.wk ρ) (wkConvNeUp hρ hΔ hkl)

/-- Weakening of `ConvTypeDown` (`wkConv↓`). -/
theorem wkConvTypeDown {Γ Δ : Context} {A B : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (d : ConvTypeDown Γ A B) :
    ConvTypeDown Δ (wk ρ A) (wk ρ B) :=
  (ConvTypeDown.rec
    (motive_1 := fun Γ t u A _ ↦ WkConvNeUpMotive Γ t u A)
    (motive_2 := fun Γ t u A _ ↦ WkConvNeDownMotive Γ t u A)
    (motive_3 := fun Γ A B _ ↦ WkConvTypeUpMotive Γ A B)
    (motive_4 := fun Γ A B _ ↦ WkConvTypeDownMotive Γ A B)
    (motive_5 := fun Γ t u A _ ↦ WkConvTermUpMotive Γ t u A)
    (motive_6 := fun Γ t u A _ ↦ WkConvTermDownMotive Γ t u A)
    (fun hx hxy ↦ wkConv_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ wkConv_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      wkConv_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ wkConv_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB hAB ihAB ↦ wkConv_typeUp_case DA DB hwA hwB hAB ihAB)
    (fun hΓ ↦ wkConv_univRefl_case hΓ)
    (fun hΓ ↦ wkConv_natRefl_case hΓ)
    (fun hKL ihKL ↦ wkConv_neType_case hKL ihKL)
    (fun hF hFH hGE ihFH ihGE ↦ wkConv_piCong_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu htu ihtu ↦
      wkConv_termUp_case DA dt du hwB hwt hwu htu ihtu)
    (fun hkl ihkl ↦ wkConv_natIns_case hkl ihkl)
    (fun hk hl neN hkl ihkl ↦ wkConv_neIns_case hk hl neN hkl ihkl)
    (fun hA hB hAB ihAB ↦ wkConv_univ_case hA hB hAB ihAB)
    (fun hΓ ↦ wkConv_zeroRefl_case hΓ)
    (fun hmn ihmn ↦ wkConv_succCong_case hmn ihmn)
    (fun hF hf hg hwf hwg hfg ihfg ↦ wkConv_etaEq_case hF hf hg hwf hwg hfg ihfg)
    d) hρ hΔ

/-- Weakening of `ConvTypeUp` (`wkConv↑`). -/
theorem wkConvTypeUp {Γ Δ : Context} {A B : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) :
    ConvTypeUp Γ A B → ConvTypeUp Δ (wk ρ A) (wk ρ B)
  | .mk DA DB hwA hwB hAB =>
      .mk (wkTypeStar hρ hΔ DA) (wkTypeStar hρ hΔ DB)
        (hwA.wk ρ) (hwB.wk ρ) (wkConvTypeDown hρ hΔ hAB)

/-- Weakening of `ConvTermDown` (`wkConv↓Term`). -/
theorem wkConvTermDown {Γ Δ : Context} {t u A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) (d : ConvTermDown Γ t u A) :
    ConvTermDown Δ (wk ρ t) (wk ρ u) (wk ρ A) :=
  (ConvTermDown.rec
    (motive_1 := fun Γ t u A _ ↦ WkConvNeUpMotive Γ t u A)
    (motive_2 := fun Γ t u A _ ↦ WkConvNeDownMotive Γ t u A)
    (motive_3 := fun Γ A B _ ↦ WkConvTypeUpMotive Γ A B)
    (motive_4 := fun Γ A B _ ↦ WkConvTypeDownMotive Γ A B)
    (motive_5 := fun Γ t u A _ ↦ WkConvTermUpMotive Γ t u A)
    (motive_6 := fun Γ t u A _ ↦ WkConvTermDownMotive Γ t u A)
    (fun hx hxy ↦ wkConv_var_case hx hxy)
    (fun hkl htv ihkl ihtv ↦ wkConv_app_case hkl htv ihkl ihtv)
    (fun hFG hab hhg hkl ihFG ihab ihhg ihkl ↦
      wkConv_natrec_case hFG hab hhg hkl ihFG ihab ihhg ihkl)
    (fun D hw hkl ihkl ↦ wkConv_neDown_case D hw hkl ihkl)
    (fun DA DB hwA hwB hAB ihAB ↦ wkConv_typeUp_case DA DB hwA hwB hAB ihAB)
    (fun hΓ ↦ wkConv_univRefl_case hΓ)
    (fun hΓ ↦ wkConv_natRefl_case hΓ)
    (fun hKL ihKL ↦ wkConv_neType_case hKL ihKL)
    (fun hF hFH hGE ihFH ihGE ↦ wkConv_piCong_case hF hFH hGE ihFH ihGE)
    (fun DA dt du hwB hwt hwu htu ihtu ↦
      wkConv_termUp_case DA dt du hwB hwt hwu htu ihtu)
    (fun hkl ihkl ↦ wkConv_natIns_case hkl ihkl)
    (fun hk hl neN hkl ihkl ↦ wkConv_neIns_case hk hl neN hkl ihkl)
    (fun hA hB hAB ihAB ↦ wkConv_univ_case hA hB hAB ihAB)
    (fun hΓ ↦ wkConv_zeroRefl_case hΓ)
    (fun hmn ihmn ↦ wkConv_succCong_case hmn ihmn)
    (fun hF hf hg hwf hwg hfg ihfg ↦ wkConv_etaEq_case hF hf hg hwf hwg hfg ihfg)
    d) hρ hΔ

/-- Weakening of `ConvTermUp` (`wkConv↑Term`). -/
theorem wkConvTermUp {Γ Δ : Context} {t u A : Term} {ρ : Wk}
    (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ) :
    ConvTermUp Γ t u A → ConvTermUp Δ (wk ρ t) (wk ρ u) (wk ρ A)
  | .mk DA dt du hwB hwt hwu htu =>
      .mk (wkTypeStar hρ hΔ DA) (wkStar hρ hΔ dt) (wkStar hρ hΔ du)
        (hwB.wk ρ) (hwt.wk ρ) (hwu.wk ρ) (wkConvTermDown hρ hΔ htu)

/-!
## Executable Adequacy and Fuel Monotonicity for `Algorithm.lean`
-/

/-- `neutralHead` characterizes `Neutral` exactly. -/
theorem neutralHead_iff_Neutral : ∀ t : Term, neutralHead t = true ↔ Neutral t
  | .univ => ⟨fun h ↦ (by cases h), fun h ↦ (by cases h)⟩
  | .pi _ _ => ⟨fun h ↦ (by cases h), fun h ↦ (by cases h)⟩
  | .nat => ⟨fun h ↦ (by cases h), fun h ↦ (by cases h)⟩
  | .var x => ⟨fun _ ↦ .var x, fun _ ↦ rfl⟩
  | .lam _ => ⟨fun h ↦ (by cases h), fun h ↦ (by cases h)⟩
  | .app k _ => by
      dsimp [neutralHead]
      constructor
      · intro h
        exact .app ((neutralHead_iff_Neutral k).mp h)
      · intro h
        cases h with
        | app hk => exact (neutralHead_iff_Neutral k).mpr hk
  | .zero => ⟨fun h ↦ (by cases h), fun h ↦ (by cases h)⟩
  | .succ _ => ⟨fun h ↦ (by cases h), fun h ↦ (by cases h)⟩
  | .natrec _ _ _ k => by
      dsimp [neutralHead]
      constructor
      · intro h
        exact .natrec ((neutralHead_iff_Neutral k).mp h)
      · intro h
        cases h with
        | natrec hk => exact (neutralHead_iff_Neutral k).mpr hk

/-- `lookupType` characterizes `Member` exactly. -/
theorem lookupType_iff_Member :
    ∀ (Γ : Context) (x : Nat) (A : Term), lookupType Γ x = some A ↔ Member x A Γ
  | [], _, _ => ⟨fun h ↦ (by cases h), fun h ↦ (by cases h)⟩
  | B :: _, 0, A => by
      dsimp [lookupType]
      constructor
      · intro h
        cases h
        exact .here
      · intro h
        cases h
        rfl
  | B :: Γ, x + 1, A => by
      dsimp [lookupType]
      constructor
      · intro h
        cases h' : lookupType Γ x with
        | none => rw [h'] at h; cases h
        | some A₀ =>
            rw [h'] at h
            cases h
            exact .there ((lookupType_iff_Member Γ x A₀).mp h')
      · intro h
        cases h with
        | @there _ A₀ _ _ hm =>
            have h' := (lookupType_iff_Member Γ x A₀).mpr hm
            rw [h']
            rfl

theorem lookupType_hasType {Γ : Context} {x : Nat} {A : Term}
    (hΓ : CtxWf Γ) (hl : lookupType Γ x = some A) : HasType Γ (.var x) A :=
  .var hΓ ((lookupType_iff_Member Γ x A).mp hl)

/-- Every successful result of `whnfFuel` is in `Whnf`. -/
theorem whnfFuel_whnf : ∀ {fuel : Nat} {t u : Term},
    whnfFuel fuel t = some u → Whnf u
  | 0, _, _, h => by cases h
  | fuel + 1, .univ, u, h => by cases h; exact .univ
  | fuel + 1, .pi _ _, u, h => by cases h; exact .pi
  | fuel + 1, .nat, u, h => by cases h; exact .nat
  | fuel + 1, .var x, u, h => by cases h; exact .neutral (.var x)
  | fuel + 1, .lam _, u, h => by cases h; exact .lam
  | fuel + 1, .zero, u, h => by cases h; exact .zero
  | fuel + 1, .succ _, u, h => by cases h; exact .succ
  | fuel + 1, .app f a, u, h => by
      dsimp [whnfFuel] at h
      cases hf : whnfFuel fuel f with
      | none => rw [hf] at h; cases h
      | some f' =>
          rw [hf] at h
          dsimp [Bind.bind, Option.bind] at h
          cases f' with
          | lam body => exact whnfFuel_whnf h
          | univ | pi _ _ | nat | zero | succ _ =>
              dsimp [neutralHead] at h
              cases h
          | var x =>
              dsimp [neutralHead] at h
              cases h
              exact .neutral (.app (.var x))
          | app k v =>
              by_cases hne : neutralHead (Term.app k v) = true
              · rw [if_pos hne] at h
                cases h
                exact .neutral (.app ((neutralHead_iff_Neutral _).mp hne))
              · rw [if_neg hne] at h
                cases h
          | natrec C z s k =>
              by_cases hne : neutralHead (Term.natrec C z s k) = true
              · rw [if_pos hne] at h
                cases h
                exact .neutral (.app ((neutralHead_iff_Neutral _).mp hne))
              · rw [if_neg hne] at h
                cases h
  | fuel + 1, .natrec A z s n, u, h => by
      dsimp [whnfFuel] at h
      cases hn : whnfFuel fuel n with
      | none => rw [hn] at h; cases h
      | some n' =>
          rw [hn] at h
          dsimp [Bind.bind, Option.bind] at h
          cases n' with
          | zero => exact whnfFuel_whnf h
          | succ k => exact whnfFuel_whnf h
          | univ | pi _ _ | nat | lam _ =>
              dsimp [neutralHead] at h
              cases h
          | var x =>
              dsimp [neutralHead] at h
              cases h
              exact .neutral (.natrec (.var x))
          | app k v =>
              by_cases hne : neutralHead (Term.app k v) = true
              · rw [if_pos hne] at h
                cases h
                exact .neutral (.natrec ((neutralHead_iff_Neutral _).mp hne))
              · rw [if_neg hne] at h
                cases h
          | natrec C z' s' k =>
              by_cases hne : neutralHead (Term.natrec C z' s' k) = true
              · rw [if_pos hne] at h
                cases h
                exact .neutral (.natrec ((neutralHead_iff_Neutral _).mp hne))
              · rw [if_neg hne] at h
                cases h

/-- Fuel monotonicity for `whnfFuel`: increasing fuel preserves any successful result. -/
theorem whnfFuel_mono : ∀ {f₁ f₂ : Nat} {t u : Term},
    f₁ ≤ f₂ → whnfFuel f₁ t = some u → whnfFuel f₂ t = some u
  | 0, _, _, _, _, h => by cases h
  | _ + 1, 0, _, _, hle, _ => by cases hle
  | f₁ + 1, f₂ + 1, .univ, _, _, h => h
  | f₁ + 1, f₂ + 1, .pi _ _, _, _, h => h
  | f₁ + 1, f₂ + 1, .nat, _, _, h => h
  | f₁ + 1, f₂ + 1, .var _, _, _, h => h
  | f₁ + 1, f₂ + 1, .lam _, _, _, h => h
  | f₁ + 1, f₂ + 1, .zero, _, _, h => h
  | f₁ + 1, f₂ + 1, .succ _, _, _, h => h
  | f₁ + 1, f₂ + 1, .app f a, u, hle, h => by
      have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
      dsimp [whnfFuel] at h ⊢
      cases hf : whnfFuel f₁ f with
      | none => rw [hf] at h; cases h
      | some f' =>
          rw [hf] at h
          rw [whnfFuel_mono hle' hf]
          dsimp [Bind.bind, Option.bind] at h ⊢
          cases f' with
          | lam body => exact whnfFuel_mono hle' h
          | _ => exact h
  | f₁ + 1, f₂ + 1, .natrec A z s n, u, hle, h => by
      have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
      dsimp [whnfFuel] at h ⊢
      cases hn : whnfFuel f₁ n with
      | none => rw [hn] at h; cases h
      | some n' =>
          rw [hn] at h
          rw [whnfFuel_mono hle' hn]
          dsimp [Bind.bind, Option.bind] at h ⊢
          cases n' with
          | zero => exact whnfFuel_mono hle' h
          | succ k => exact whnfFuel_mono hle' h
          | _ => exact h

/-- Every neutral term evaluates to itself under `whnfFuel` once fuel equals at least its spine depth. -/
theorem whnfFuel_of_Neutral {t : Term} (hn : Neutral t) :
    ∃ fuel, ∀ f, fuel ≤ f → whnfFuel f t = some t := by
  induction hn with
  | var x =>
      refine ⟨1, fun f hf ↦ ?_⟩
      cases f with
      | zero => cases hf
      | succ f => rfl
  | @app k u hk ih =>
      rcases ih with ⟨f₀, ih⟩
      refine ⟨f₀ + 1, fun f hf ↦ ?_⟩
      cases f with
      | zero => cases hf
      | succ f =>
          have hle : f₀ ≤ f := Nat.le_of_succ_le_succ hf
          dsimp [whnfFuel]
          rw [ih f hle]
          dsimp [Bind.bind, Option.bind]
          have hne : neutralHead k = true := (neutralHead_iff_Neutral k).mpr hk
          cases hk with
          | var _ => rfl
          | app _ => simp [hne]
          | natrec _ => simp [hne]
  | @natrec C z s k hk ih =>
      rcases ih with ⟨f₀, ih⟩
      refine ⟨f₀ + 1, fun f hf ↦ ?_⟩
      cases f with
      | zero => cases hf
      | succ f =>
          have hle : f₀ ≤ f := Nat.le_of_succ_le_succ hf
          dsimp [whnfFuel]
          rw [ih f hle]
          dsimp [Bind.bind, Option.bind]
          have hne : neutralHead k = true := (neutralHead_iff_Neutral k).mpr hk
          cases hk with
          | var _ => rfl
          | app _ => simp [hne]
          | natrec _ => simp [hne]

/-- Every WHNF term evaluates to itself under `whnfFuel` for sufficiently large fuel. -/
theorem whnfFuel_of_Whnf {t : Term} (hw : Whnf t) :
    ∃ fuel, ∀ f, fuel ≤ f → whnfFuel f t = some t := by
  cases hw with
  | univ | pi | nat | lam | zero | succ =>
      refine ⟨1, fun f hf ↦ ?_⟩
      cases f with
      | zero => cases hf
      | succ _ => rfl
  | neutral hn => exact whnfFuel_of_Neutral hn

/-- Single-step typed reduction is simulated backwards by `whnfFuel`. -/
theorem whnfFuel_step {Γ : Context} {t t' u A : Term} {fuel : Nat}
    (d : Step Γ t t' A) (hu : whnfFuel fuel t' = some u) :
    whnfFuel (fuel + 1) t = some u := by
  induction d generalizing u fuel with
  | conv _ _ ih => exact ih hu
  | @app _ _ f f' a _ _ ih =>
      cases fuel with
      | zero => cases hu
      | succ f₀ =>
          dsimp [whnfFuel] at hu
          cases hf' : whnfFuel f₀ f' with
          | none => rw [hf'] at hu; cases hu
          | some w =>
              rw [hf'] at hu
              have hf : whnfFuel (f₀ + 1) f = some w := ih hf'
              dsimp [whnfFuel]
              rw [hf]
              dsimp [Bind.bind, Option.bind] at hu ⊢
              cases w with
              | lam body => exact whnfFuel_mono (Nat.le_succ f₀) hu
              | _ => exact hu
  | @beta _ _ a body _ _ _ =>
      dsimp [whnfFuel]
      cases fuel with
      | zero => cases hu
      | succ f₀ =>
          have hbody : whnfFuel (f₀ + 1) (.lam body) = some (.lam body) := rfl
          rw [hbody]
          dsimp [Bind.bind, Option.bind]
          exact hu
  | @natrec z s n n' F _ _ _ _ ih =>
      cases fuel with
      | zero => cases hu
      | succ f₀ =>
          dsimp [whnfFuel] at hu
          cases hn' : whnfFuel f₀ n' with
          | none => rw [hn'] at hu; cases hu
          | some w =>
              rw [hn'] at hu
              have hn : whnfFuel (f₀ + 1) n = some w := ih hn'
              dsimp [whnfFuel]
              rw [hn]
              dsimp [Bind.bind, Option.bind] at hu ⊢
              cases w with
              | zero => exact whnfFuel_mono (Nat.le_succ f₀) hu
              | succ k => exact whnfFuel_mono (Nat.le_succ f₀) hu
              | _ => exact hu
  | @natrecZero z s F _ _ _ =>
      dsimp [whnfFuel]
      cases fuel with
      | zero => cases hu
      | succ f₀ =>
          have hzero : whnfFuel (f₀ + 1) .zero = some .zero := rfl
          rw [hzero]
          dsimp [Bind.bind, Option.bind]
          exact hu
  | @natrecSucc n z s F _ _ _ _ =>
      dsimp [whnfFuel]
      cases fuel with
      | zero => cases hu
      | succ f₀ =>
          have hsucc : whnfFuel (f₀ + 1) (.succ n) = some (.succ n) := rfl
          rw [hsucc]
          dsimp [Bind.bind, Option.bind]
          exact hu

/-- Multi-step typed term reduction to WHNF (`TermWhnf`) is computed by `whnfFuel`. -/
theorem whnfFuel_of_TermWhnf {Γ : Context} {t u A : Term} (h : TermWhnf Γ t u A) :
    ∃ fuel, ∀ f, fuel ≤ f → whnfFuel f t = some u := by
  rcases h with ⟨dStar, hwu⟩
  induction dStar with
  | refl _ => exact whnfFuel_of_Whnf hwu
  | step hStep _ ih =>
      rcases ih hwu with ⟨f₀, ih⟩
      refine ⟨f₀ + 1, fun f hf ↦ ?_⟩
      cases f with
      | zero => cases hf
      | succ f =>
          have hle : f₀ ≤ f := Nat.le_of_succ_le_succ hf
          exact whnfFuel_step hStep (ih f hle)

/-- Multi-step typed type reduction to WHNF (`TypeWhnf`) is computed by `whnfFuel`. -/
theorem whnfFuel_of_TypeWhnf {Γ : Context} {A B : Term} (h : TypeWhnf Γ A B) :
    ∃ fuel, ∀ f, fuel ≤ f → whnfFuel f A = some B := by
  rcases h with ⟨dStar, hwB⟩
  induction dStar with
  | refl _ => exact whnfFuel_of_Whnf hwB
  | step hStep _ ih =>
      cases hStep with
      | fromUniv hStepTerm =>
          rcases ih hwB with ⟨f₀, ih⟩
          refine ⟨f₀ + 1, fun f hf ↦ ?_⟩
          cases f with
          | zero => cases hf
          | succ f =>
              have hle : f₀ ≤ f := Nat.le_of_succ_le_succ hf
              exact whnfFuel_step hStepTerm (ih f hle)

/-- Combined fuel monotonicity for all six comparison functions in `Algorithm.lean`. -/
theorem compare_mono_bundle :
    ∀ f₁ : Nat,
      (∀ {f₂ : Nat} {Γ : Context} {k l : Term} {res : Option Term},
        f₁ ≤ f₂ → compareNeutralUp f₁ Γ k l = some res → compareNeutralUp f₂ Γ k l = some res) ∧
      (∀ {f₂ : Nat} {Γ : Context} {k l : Term} {res : Option Term},
        f₁ ≤ f₂ → compareNeutralDown f₁ Γ k l = some res → compareNeutralDown f₂ Γ k l = some res) ∧
      (∀ {f₂ : Nat} {Γ : Context} {A B : Term} {b : Bool},
        f₁ ≤ f₂ → compareTypeUp f₁ Γ A B = some b → compareTypeUp f₂ Γ A B = some b) ∧
      (∀ {f₂ : Nat} {Γ : Context} {A B : Term} {b : Bool},
        f₁ ≤ f₂ → compareTypeDown f₁ Γ A B = some b → compareTypeDown f₂ Γ A B = some b) ∧
      (∀ {f₂ : Nat} {Γ : Context} {t u A : Term} {b : Bool},
        f₁ ≤ f₂ → compareTermUp f₁ Γ t u A = some b → compareTermUp f₂ Γ t u A = some b) ∧
      (∀ {f₂ : Nat} {Γ : Context} {t u A : Term} {b : Bool},
        f₁ ≤ f₂ → compareTermDown f₁ Γ t u A = some b → compareTermDown f₂ Γ t u A = some b)
  | 0 =>
      ⟨fun _ h ↦ (by cases h),
       fun _ h ↦ (by cases h),
       fun _ h ↦ (by cases h),
       fun _ h ↦ (by cases h),
       fun _ h ↦ (by cases h),
       fun _ h ↦ (by cases h)⟩
  | f₁ + 1 =>
      let ⟨ihNeUp, ihNeDown, ihTyUp, ihTyDown, ihTmUp, ihTmDown⟩ := compare_mono_bundle f₁
      ⟨-- compareNeutralUp
       fun {f₂ Γ k l res} hle h ↦ by
         cases f₂ with
         | zero => cases hle
         | succ f₂ =>
             have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
             cases k <;> cases l <;> try exact h
             case app k t l v =>
               dsimp [compareNeutralUp] at h ⊢
               cases hinf : compareNeutralDown f₁ Γ k l with
               | none => rw [hinf] at h; cases h
               | some inf =>
                   rw [hinf] at h
                   rw [ihNeDown hle' hinf]
                   dsimp [Bind.bind, Option.bind] at h ⊢
                   cases inf with
                   | none => exact h
                   | some T =>
                       cases T with
                       | pi F G =>
                           dsimp at h ⊢
                           cases heq : compareTermUp f₁ Γ t v F with
                           | none => rw [heq] at h; cases h
                           | some b =>
                               rw [heq] at h
                               rw [ihTmUp hle' heq]
                               exact h
                       | _ => exact h
             case natrec F a₀ h₀ k G b₀ g₀ l =>
               dsimp [compareNeutralUp] at h ⊢
               cases hm : compareTypeUp f₁ (.nat :: Γ) F G with
               | none => rw [hm] at h; cases h
               | some bm =>
                   rw [hm] at h
                   rw [ihTyUp hle' hm]
                   dsimp [Bind.bind, Option.bind] at h ⊢
                   cases bm with
                   | false => exact h
                   | true =>
                       dsimp at h ⊢
                       cases hb : compareTermUp f₁ Γ a₀ b₀ (subst0 F .zero) with
                       | none => rw [hb] at h; cases h
                       | some bb =>
                           rw [hb] at h
                           rw [ihTmUp hle' hb]
                           dsimp [Bind.bind, Option.bind] at h ⊢
                           cases bb with
                           | false => exact h
                           | true =>
                               dsimp at h ⊢
                               cases hs : compareTermUp f₁ Γ h₀ g₀ (recStepType F) with
                               | none => rw [hs] at h; cases h
                               | some bs =>
                                   rw [hs] at h
                                   rw [ihTmUp hle' hs]
                                   dsimp [Bind.bind, Option.bind] at h ⊢
                                   cases bs with
                                   | false => exact h
                                   | true =>
                                       dsimp at h ⊢
                                       cases hi : compareNeutralDown f₁ Γ k l with
                                       | none => rw [hi] at h; cases h
                                       | some inf =>
                                           rw [hi] at h
                                           rw [ihNeDown hle' hi]
                                           exact h,
       -- compareNeutralDown
       fun {f₂ Γ k l res} hle h ↦ by
         cases f₂ with
         | zero => cases hle
         | succ f₂ =>
             have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
             dsimp [compareNeutralDown] at h ⊢
             cases hi : compareNeutralUp f₁ Γ k l with
             | none => rw [hi] at h; cases h
             | some inf =>
                 rw [hi] at h
                 rw [ihNeUp hle' hi]
                 dsimp [Bind.bind, Option.bind] at h ⊢
                 cases inf with
                 | none => exact h
                 | some A =>
                     dsimp at h ⊢
                     cases hw : whnfFuel f₁ A with
                     | none => rw [hw] at h; cases h
                     | some B =>
                         rw [hw] at h
                         rw [whnfFuel_mono hle' hw]
                         exact h,
       -- compareTypeUp
       fun {f₂ Γ A B b} hle h ↦ by
         cases f₂ with
         | zero => cases hle
         | succ f₂ =>
             have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
             dsimp [compareTypeUp] at h ⊢
             cases hA : whnfFuel f₁ A with
             | none => rw [hA] at h; cases h
             | some A' =>
                 rw [hA] at h
                 rw [whnfFuel_mono hle' hA]
                 dsimp [Bind.bind, Option.bind] at h ⊢
                 cases hB : whnfFuel f₁ B with
                 | none => rw [hB] at h; cases h
                 | some B' =>
                     rw [hB] at h
                     rw [whnfFuel_mono hle' hB]
                     dsimp [Bind.bind, Option.bind] at h ⊢
                     exact ihTyDown hle' h,
       -- compareTypeDown
       fun {f₂ Γ A B b} hle h ↦ by
         cases f₂ with
         | zero => cases hle
         | succ f₂ =>
             have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
             have hNeCase :
                 (if neutralHead A && neutralHead B then do
                   let inferred ← compareNeutralDown f₁ Γ A B
                   match inferred with
                   | some .univ => some true
                   | _ => some false
                 else some false) = some b →
                 (if neutralHead A && neutralHead B then do
                   let inferred ← compareNeutralDown f₂ Γ A B
                   match inferred with
                   | some .univ => some true
                   | _ => some false
                 else some false) = some b := by
               intro hne
               by_cases hcond : (neutralHead A && neutralHead B) = true
               · rw [if_pos hcond] at hne ⊢
                 cases hi : compareNeutralDown f₁ Γ A B with
                 | none => rw [hi] at hne; cases hne
                 | some inf =>
                     rw [hi] at hne
                     rw [ihNeDown hle' hi]
                     exact hne
               · rw [if_neg hcond] at hne ⊢
                 exact hne
             cases A <;> cases B <;> try exact hNeCase h
             case univ.univ => exact h
             case nat.nat => exact h
             case pi.pi F G H E =>
               dsimp [compareTypeDown] at h ⊢
               cases hd : compareTypeUp f₁ Γ F H with
               | none => rw [hd] at h; cases h
               | some bd =>
                   rw [hd] at h
                   rw [ihTyUp hle' hd]
                   dsimp [Bind.bind, Option.bind] at h ⊢
                   cases bd with
                   | false => exact h
                   | true =>
                       dsimp at h ⊢
                       exact ihTyUp hle' h,
       -- compareTermUp
       fun {f₂ Γ t u A b} hle h ↦ by
         cases f₂ with
         | zero => cases hle
         | succ f₂ =>
             have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
             dsimp [compareTermUp] at h ⊢
             cases hB : whnfFuel f₁ A with
             | none => rw [hB] at h; cases h
             | some B =>
                 rw [hB] at h
                 rw [whnfFuel_mono hle' hB]
                 dsimp [Bind.bind, Option.bind] at h ⊢
                 cases ht : whnfFuel f₁ t with
                 | none => rw [ht] at h; cases h
                 | some t' =>
                     rw [ht] at h
                     rw [whnfFuel_mono hle' ht]
                     dsimp [Bind.bind, Option.bind] at h ⊢
                     cases hu : whnfFuel f₁ u with
                     | none => rw [hu] at h; cases h
                     | some u' =>
                         rw [hu] at h
                         rw [whnfFuel_mono hle' hu]
                         dsimp [Bind.bind, Option.bind] at h ⊢
                         exact ihTmDown hle' h,
       -- compareTermDown
       fun {f₂ Γ t u A b} hle h ↦ by
         cases f₂ with
         | zero => cases hle
         | succ f₂ =>
             have hle' : f₁ ≤ f₂ := Nat.le_of_succ_le_succ hle
             have hNeInsCase :
                 (if neutralHead A && neutralHead t && neutralHead u then do
                   let inferred ← compareNeutralDown f₁ Γ t u
                   some inferred.isSome
                 else some false) = some b →
                 (if neutralHead A && neutralHead t && neutralHead u then do
                   let inferred ← compareNeutralDown f₂ Γ t u
                   some inferred.isSome
                 else some false) = some b := by
               intro hne
               by_cases hcond : (neutralHead A && neutralHead t && neutralHead u) = true
               · rw [if_pos hcond] at hne ⊢
                 cases hi : compareNeutralDown f₁ Γ t u with
                 | none => rw [hi] at hne; cases hne
                 | some inf =>
                     rw [hi] at hne
                     rw [ihNeDown hle' hi]
                     exact hne
               · rw [if_neg hcond] at hne ⊢
                 exact hne
             cases A with
             | univ =>
                 dsimp [compareTermDown] at h ⊢
                 exact ihTyDown hle' h
             | pi F G =>
                 dsimp [compareTermDown] at h ⊢
                 exact ihTmUp hle' h
             | nat =>
                 have hNatNeCase :
                     (if neutralHead t && neutralHead u then do
                       let inferred ← compareNeutralDown f₁ Γ t u
                       match inferred with
                       | some .nat => some true
                       | _ => some false
                     else some false) = some b →
                     (if neutralHead t && neutralHead u then do
                       let inferred ← compareNeutralDown f₂ Γ t u
                       match inferred with
                       | some .nat => some true
                       | _ => some false
                     else some false) = some b := by
                   intro hne
                   by_cases hcond : (neutralHead t && neutralHead u) = true
                   · rw [if_pos hcond] at hne ⊢
                     cases hi : compareNeutralDown f₁ Γ t u with
                     | none => rw [hi] at hne; cases hne
                     | some inf =>
                         rw [hi] at hne
                         rw [ihNeDown hle' hi]
                         exact hne
                   · rw [if_neg hcond] at hne ⊢
                     exact hne
                 cases t <;> cases u <;> try exact hNatNeCase h
                 case zero.zero => exact h
                 case succ.succ m n =>
                   dsimp [compareTermDown] at h ⊢
                   exact ihTmUp hle' h
             | var _ | app _ _ | natrec _ _ _ _ | lam _ | zero | succ _ =>
                 exact hNeInsCase h⟩

theorem compareNeutralUp_mono {f₁ f₂ : Nat} {Γ : Context} {k l : Term} {res : Option Term}
    (hle : f₁ ≤ f₂) (h : compareNeutralUp f₁ Γ k l = some res) :
    compareNeutralUp f₂ Γ k l = some res :=
  (compare_mono_bundle f₁).1 hle h

theorem compareNeutralDown_mono {f₁ f₂ : Nat} {Γ : Context} {k l : Term} {res : Option Term}
    (hle : f₁ ≤ f₂) (h : compareNeutralDown f₁ Γ k l = some res) :
    compareNeutralDown f₂ Γ k l = some res :=
  (compare_mono_bundle f₁).2.1 hle h

theorem compareTypeUp_mono {f₁ f₂ : Nat} {Γ : Context} {A B : Term} {b : Bool}
    (hle : f₁ ≤ f₂) (h : compareTypeUp f₁ Γ A B = some b) :
    compareTypeUp f₂ Γ A B = some b :=
  (compare_mono_bundle f₁).2.2.1 hle h

theorem compareTypeDown_mono {f₁ f₂ : Nat} {Γ : Context} {A B : Term} {b : Bool}
    (hle : f₁ ≤ f₂) (h : compareTypeDown f₁ Γ A B = some b) :
    compareTypeDown f₂ Γ A B = some b :=
  (compare_mono_bundle f₁).2.2.2.1 hle h

theorem compareTermUp_mono {f₁ f₂ : Nat} {Γ : Context} {t u A : Term} {b : Bool}
    (hle : f₁ ≤ f₂) (h : compareTermUp f₁ Γ t u A = some b) :
    compareTermUp f₂ Γ t u A = some b :=
  (compare_mono_bundle f₁).2.2.2.2.1 hle h

theorem compareTermDown_mono {f₁ f₂ : Nat} {Γ : Context} {t u A : Term} {b : Bool}
    (hle : f₁ ≤ f₂) (h : compareTermDown f₁ Γ t u A = some b) :
    compareTermDown f₂ Γ t u A = some b :=
  (compare_mono_bundle f₁).2.2.2.2.2 hle h

/-- Any two successful runs of `compareTypeUp` on the same inputs return the same Boolean. -/
theorem compareTypeUp_unique {f₁ f₂ : Nat} {Γ : Context} {A B : Term} {b₁ b₂ : Bool}
    (h₁ : compareTypeUp f₁ Γ A B = some b₁)
    (h₂ : compareTypeUp f₂ Γ A B = some b₂) : b₁ = b₂ := by
  have hm₁ : compareTypeUp (f₁ + f₂) Γ A B = some b₁ :=
    compareTypeUp_mono (Nat.le_add_right f₁ f₂) h₁
  have hm₂ : compareTypeUp (f₁ + f₂) Γ A B = some b₂ :=
    compareTypeUp_mono (Nat.le_add_left f₂ f₁) h₂
  rw [hm₁] at hm₂
  cases hm₂
  rfl

/-- Any two successful runs of `compareTermUp` on the same inputs return the same Boolean. -/
theorem compareTermUp_unique {f₁ f₂ : Nat} {Γ : Context} {t u A : Term} {b₁ b₂ : Bool}
    (h₁ : compareTermUp f₁ Γ t u A = some b₁)
    (h₂ : compareTermUp f₂ Γ t u A = some b₂) : b₁ = b₂ := by
  have hm₁ : compareTermUp (f₁ + f₂) Γ t u A = some b₁ :=
    compareTermUp_mono (Nat.le_add_right f₁ f₂) h₁
  have hm₂ : compareTermUp (f₁ + f₂) Γ t u A = some b₂ :=
    compareTermUp_mono (Nat.le_add_left f₂ f₁) h₂
  rw [hm₁] at hm₂
  cases hm₂
  rfl

/-- By fuel monotonicity, existence of one correct fuel run implies both convergence and
correctness of every successful run. -/
theorem compareTypeUp_all_runs_correct {Γ : Context} {A B : Term}
    (h : ∃ fuel b, compareTypeUp fuel Γ A B = some b ∧ (b = true ↔ TypeEq Γ A B)) :
    (∃ fuel b, compareTypeUp fuel Γ A B = some b) ∧
    (∀ fuel b, compareTypeUp fuel Γ A B = some b → (b = true ↔ TypeEq Γ A B)) := by
  rcases h with ⟨f₀, b₀, hf₀, hb₀⟩
  refine ⟨⟨f₀, b₀, hf₀⟩, fun f b hf ↦ ?_⟩
  have heq : b = b₀ := compareTypeUp_unique hf hf₀
  subst heq
  exact hb₀

/-- By fuel monotonicity, existence of one correct fuel run implies both convergence and
correctness of every successful run for terms. -/
theorem compareTermUp_all_runs_correct {Γ : Context} {t u A : Term}
    (h : ∃ fuel b, compareTermUp fuel Γ t u A = some b ∧ (b = true ↔ TermEq Γ t u A)) :
    (∃ fuel b, compareTermUp fuel Γ t u A = some b) ∧
    (∀ fuel b, compareTermUp fuel Γ t u A = some b → (b = true ↔ TermEq Γ t u A)) := by
  rcases h with ⟨f₀, b₀, hf₀, hb₀⟩
  refine ⟨⟨f₀, b₀, hf₀⟩, fun f b hf ↦ ?_⟩
  have heq : b = b₀ := compareTermUp_unique hf hf₀
  subst heq
  exact hb₀

end LogrelMLTT
