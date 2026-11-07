/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Conversion/Decidable.agda (Theorem 4.5),
Definition/Typed/Decidable.agda (Theorem 4.12),
and the executable adequacy target in formalization/abel2018/algorithm-goal.md.
-/
import Abel2018.Completeness

namespace Abel2018

/-!
## Uniqueness of Algorithmic Neutral Types (`Definition/Conversion/Decidable.agda`)
-/

/-- Uniqueness of inferred type in `ConvNeUp` (`unique~↑`). -/
theorem uniqueNeUp {Γ : Context} {t u A B : Term}
    (h₁ : ConvNeUp Γ t u A) (h₂ : ConvNeUp Γ t u B) : TypeEq Γ A B := by
  have wfΓ : CtxWf Γ := wfTermEq (soundnessNeUp h₁)
  rcases symNeUp (reflConEq wfΓ) h₂ with ⟨B', hBB', hut⟩
  exact .trans (transNeUp (reflConEq wfΓ) h₁ hut).2 (.symm hBB')

/-- Uniqueness of inferred WHNF type in `ConvNeDown` (`unique~↓`). -/
theorem uniqueNeDown {Γ : Context} {t u A B : Term}
    (h₁ : ConvNeDown Γ t u A) (h₂ : ConvNeDown Γ t u B) : TypeEq Γ A B := by
  have wfΓ : CtxWf Γ := wfTermEq (soundnessNeDown h₁)
  rcases symNeDown (reflConEq wfΓ) h₂ with ⟨B', _, hBB', hut⟩
  exact .trans (transNeDown (reflConEq wfΓ) h₁ hut).2 (.symm hBB')

/-- If `Γ ⊢ t ~ t₁ ↓ A` and `Γ ⊢ t ~ u ↓ B`, then `Γ ⊢ A ≡ B`. -/
theorem uniqueNeDownLeft {Γ : Context} {t t₁ u A B : Term}
    (h₁ : ConvNeDown Γ t t₁ A) (h₂ : ConvNeDown Γ t u B) : TypeEq Γ A B := by
  have wfΓ : CtxWf Γ := wfTermEq (soundnessNeDown h₁)
  rcases symNeDown (reflConEq wfΓ) h₁ with ⟨_, _, _, ht₁t⟩
  rcases symNeDown (reflConEq wfΓ) h₂ with ⟨_, _, _, hut⟩
  exact uniqueNeDown (transNeDown (reflConEq wfΓ) h₁ ht₁t).1
    (transNeDown (reflConEq wfΓ) h₂ hut).1

/-- If `⊢ Γ ≡ Δ`, `Δ ⊢ u ~ u₁ ↓ A`, and `Γ ⊢ t ~ u ↓ B`, then `Δ ⊢ B ≡ A`. -/
theorem uniqueNeDownRight {Γ Δ : Context} {t u u₁ A B : Term}
    (hΓΔ : CtxEq Γ Δ) (h₁ : ConvNeDown Δ u u₁ A) (h₂ : ConvNeDown Γ t u B) :
    TypeEq Δ B A := by
  rcases symNeDown hΓΔ h₂ with ⟨B', _, hBB', hut⟩
  exact .trans (stabilityEq hΓΔ hBB') (.symm (uniqueNeDownLeft h₁ hut))

/-!
## Executable Adequacy Predicates
-/

/-- Executable adequacy of `compareNeutralUp` on `(Γ, k, l)`. -/
def NeUpAdequate (Γ : Context) (k l : Term) : Prop :=
  ∃ fuel res, compareNeutralUp fuel Γ k l = some res ∧
    (∀ T, res = some T → ConvNeUp Γ k l T) ∧
    (res = none → ∀ T, ¬ ConvNeUp Γ k l T)

/-- Executable adequacy of `compareNeutralDown` on `(Γ, k, l)`. -/
def NeDownAdequate (Γ : Context) (k l : Term) : Prop :=
  ∃ fuel res, compareNeutralDown fuel Γ k l = some res ∧
    (∀ T, res = some T → ConvNeDown Γ k l T) ∧
    (res = none → ∀ T, ¬ ConvNeDown Γ k l T)

/-- Executable adequacy of `compareTypeUp` on `(Γ, A, B)`. -/
def TypeUpAdequate (Γ : Context) (A B : Term) : Prop :=
  ∃ fuel b, compareTypeUp fuel Γ A B = some b ∧ (b = true ↔ ConvTypeUp Γ A B)

/-- Executable adequacy of `compareTypeDown` on `(Γ, A, B)`. -/
def TypeDownAdequate (Γ : Context) (A B : Term) : Prop :=
  ∃ fuel b, compareTypeDown fuel Γ A B = some b ∧ (b = true ↔ ConvTypeDown Γ A B)

/-- Executable adequacy of `compareTermUp` on `(Γ, t, u, A)`. -/
def TermUpAdequate (Γ : Context) (t u A : Term) : Prop :=
  ∃ fuel b, compareTermUp fuel Γ t u A = some b ∧ (b = true ↔ ConvTermUp Γ t u A)

/-- Executable adequacy of `compareTermDown` on `(Γ, t, u, A)`. -/
def TermDownAdequate (Γ : Context) (t u A : Term) : Prop :=
  ∃ fuel b, compareTermDown fuel Γ t u A = some b ∧ (b = true ↔ ConvTermDown Γ t u A)

private abbrev AdeqNeUpMotive (Γ : Context) (t _t₁ _R : Term) : Prop :=
  ∀ {Γ' Δ : Context} {u u₁ S : Term},
    CtxEq Γ Γ' → CtxEq Γ' Δ → ConvNeUp Δ u u₁ S → NeUpAdequate Γ' t u

private abbrev AdeqNeDownMotive (Γ : Context) (t _t₁ _R : Term) : Prop :=
  ∀ {Γ' Δ : Context} {u u₁ S : Term},
    CtxEq Γ Γ' → CtxEq Γ' Δ → ConvNeDown Δ u u₁ S → NeDownAdequate Γ' t u

private abbrev AdeqTypeUpMotive (Γ : Context) (A _A₁ : Term) : Prop :=
  ∀ {Γ' Δ : Context} {B B₁ : Term},
    CtxEq Γ Γ' → CtxEq Γ' Δ → ConvTypeUp Δ B B₁ → TypeUpAdequate Γ' A B

private abbrev AdeqTypeDownMotive (Γ : Context) (A _A₁ : Term) : Prop :=
  ∀ {Γ' Δ : Context} {B B₁ : Term},
    CtxEq Γ Γ' → CtxEq Γ' Δ → ConvTypeDown Δ B B₁ → TypeDownAdequate Γ' A B

private abbrev AdeqTermUpMotive (Γ : Context) (t _t₁ A : Term) : Prop :=
  ∀ {Γ' Δ : Context} {u u₁ A' B : Term},
    CtxEq Γ Γ' → CtxEq Γ' Δ → ConvTermUp Δ u u₁ B →
    TypeEq Γ' A A' → TypeEq Δ A' B → TermUpAdequate Γ' t u A'

private abbrev AdeqTermDownMotive (Γ : Context) (t _t₁ A : Term) : Prop :=
  ∀ {Γ' Δ : Context} {u u₁ A' B : Term},
    CtxEq Γ Γ' → CtxEq Γ' Δ → ConvTermDown Δ u u₁ B →
    Whnf A' → TypeEq Γ' A A' → TypeEq Δ A' B → TermDownAdequate Γ' t u A'

/-!
## Case Lemmas for Mutual Adequacy and Decidability (`Definition/Conversion/Decidable.agda`)
-/

private theorem nat_beq_iff_eq (x z : Nat) : (x == z) = true ↔ x = z := by
  change decide (x = z) = true ↔ x = z
  cases instDecidableEqNat x z with
  | isTrue h => exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩
  | isFalse h => exact ⟨fun h' ↦ Bool.noConfusion h', fun h' ↦ False.elim (h h')⟩

private theorem adeq_var_case {Γ : Context} {x y : Nat} {R : Term}
    (hx : HasType Γ (.var x) R) (_hxy : x = y) :
    AdeqNeUpMotive Γ (.var x) (.var y) R := by
  intro Γ' Δ u u₁ S hΓ' _ du
  have wfΓ' : CtxWf Γ' := (contextConvSubst hΓ').2.1
  rcases inversion_var (stabilityTerm hΓ' hx) with ⟨A₀, hMem, _⟩
  have hLookup : lookupType Γ' x = some A₀ := (lookupType_iff_Member Γ' x A₀).mpr hMem
  cases du with
  | @var _ z _ _ _ _ =>
      cases hbeq : (x == z) with
      | true =>
          have hxz : x = z := (nat_beq_iff_eq x z).mp hbeq
          subst hxz
          refine ⟨1, some A₀, ?_, ?_, (fun h ↦ by cases h)⟩
          · change (if (x == x) = true then some (lookupType Γ' x) else some none) = some (some A₀)
            rw [hbeq, hLookup]
            rfl
          · intro T hT
            have hA₀T : A₀ = T := congrArg (fun opt ↦ opt.getD A₀) hT
            subst hA₀T
            exact .var (.var wfΓ' hMem) rfl
      | false =>
          refine ⟨1, none, ?_, (fun _ h ↦ by cases h), ?_⟩
          · change (if (x == z) = true then some (lookupType Γ' x) else some none) = some none
            rw [hbeq]
            rfl
          · intro _ T hConv
            cases hConv with
            | var _ hxz' =>
                have htrue : (x == z) = true := (nat_beq_iff_eq x z).mpr hxz'
                rw [hbeq] at htrue
                cases htrue
  | app _ _ =>
      refine ⟨1, none, rfl, (fun _ h ↦ by cases h), ?_⟩
      intro _ _ hConv
      cases hConv
  | natrec _ _ _ _ =>
      refine ⟨1, none, rfl, (fun _ h ↦ by cases h), ?_⟩
      intro _ _ hConv
      cases hConv

private theorem adeq_app_case {Γ : Context} {k k₁ t t₁ F G : Term}
    (hk : ConvNeDown Γ k k₁ (.pi F G)) (_ht : ConvTermUp Γ t t₁ F)
    (ihk : AdeqNeDownMotive Γ k k₁ (.pi F G))
    (iht : AdeqTermUpMotive Γ t t₁ F) :
    AdeqNeUpMotive Γ (.app k t) (.app k₁ t₁) (subst0 G t) := by
  intro Γ' Δ u u₁ S hΓ' hΔ du
  cases du with
  | var _ _ =>
      refine ⟨1, none, rfl, (fun _ h ↦ by cases h), ?_⟩
      intro _ _ hConv
      cases hConv
  | natrec _ _ _ _ =>
      refine ⟨1, none, rfl, (fun _ h ↦ by cases h), ?_⟩
      intro _ _ hConv
      cases hConv
  | @app _ l _ v _ F₂ G₂ hl hv =>
      rcases ihk hΓ' hΔ hl with ⟨f₁, res₁, hRun₁, hSome₁, hNone₁⟩
      cases res₁ with
      | none =>
          refine ⟨f₁ + 1, none, ?_, (fun _ h ↦ by cases h), ?_⟩
          · dsimp [compareNeutralUp]
            rw [hRun₁]
            rfl
          · intro _ T hConv
            cases hConv with
            | app hkl _ => exact hNone₁ rfl _ hkl
      | some M =>
          have hkl : ConvNeDown Γ' k l M := hSome₁ M rfl
          have hwM : Whnf M := (neConvNeDown hkl).1
          have hPiM : TypeEq Γ' (.pi F G) M :=
            uniqueNeDownLeft (stabilityNeDown hΓ' hk) hkl
          rcases pi_eq_A_whnf hPiM hwM with ⟨F', G', hM_eq⟩
          subst hM_eq
          have ⟨hFF', _⟩ := injectivity hPiM
          have hPi₂ : TypeEq Δ (.pi F' G') (.pi F₂ G₂) :=
            uniqueNeDownRight hΔ hl hkl
          have ⟨hF'F₂, _⟩ := injectivity hPi₂
          rcases iht hΓ' hΔ hv hFF' hF'F₂ with ⟨f₂, b, hRun₂, hIff₂⟩
          let fuel := Nat.max f₁ f₂
          have hRun₁' : compareNeutralDown fuel Γ' k l = some (some (.pi F' G')) :=
            compareNeutralDown_mono (Nat.le_max_left f₁ f₂) hRun₁
          have hRun₂' : compareTermUp fuel Γ' t v F' = some b :=
            compareTermUp_mono (Nat.le_max_right f₁ f₂) hRun₂
          cases b with
          | true =>
              refine ⟨fuel + 1, some (subst0 G' t), ?_, ?_, (fun h ↦ by cases h)⟩
              · dsimp [compareNeutralUp]
                rw [hRun₁']
                dsimp [Bind.bind, Option.bind]
                rw [hRun₂']
                rfl
              · intro T hT
                cases hT
                exact .app hkl (hIff₂.mp rfl)
          | false =>
              refine ⟨fuel + 1, none, ?_, (fun _ h ↦ by cases h), ?_⟩
              · dsimp [compareNeutralUp]
                rw [hRun₁']
                dsimp [Bind.bind, Option.bind]
                rw [hRun₂']
                rfl
              · intro _ T hConv
                cases hConv with
                | app hkl' htv' =>
                    have hPiEq' : TypeEq Γ' (.pi F' G') _ := uniqueNeDown hkl hkl'
                    have ⟨hF'F'', _⟩ := injectivity hPiEq'
                    have htv_F' : ConvTermUp Γ' t v F' :=
                      convConvTerm htv' (.symm hF'F'')
                    exact Bool.noConfusion (hIff₂.mpr htv_F')

private theorem adeq_natrec_case {Γ : Context} {k k₁ h h₁ a₀ b₀ F F₁ : Term}
    (_hFF : ConvTypeUp (.nat :: Γ) F F₁)
    (_haa : ConvTermUp Γ a₀ b₀ (subst0 F .zero))
    (_hhh : ConvTermUp Γ h h₁ (recStepType F))
    (hkk : ConvNeDown Γ k k₁ .nat)
    (ihF : AdeqTypeUpMotive (.nat :: Γ) F F₁)
    (iha : AdeqTermUpMotive Γ a₀ b₀ (subst0 F .zero))
    (ihh : AdeqTermUpMotive Γ h h₁ (recStepType F))
    (ihk : AdeqNeDownMotive Γ k k₁ .nat) :
    AdeqNeUpMotive Γ (.natrec F a₀ h k) (.natrec F₁ b₀ h₁ k₁) (subst0 F k) := by
  intro Γ' Δ u u₁ S hΓ' hΔ du
  cases du with
  | var _ _ =>
      refine ⟨1, none, rfl, (fun _ h ↦ by cases h), ?_⟩
      intro _ _ hConv
      cases hConv
  | app _ _ =>
      refine ⟨1, none, rfl, (fun _ h ↦ by cases h), ?_⟩
      intro _ _ hConv
      cases hConv
  | @natrec _ l _ g _ b₂ _ G _ hGG hbb hgg hll =>
      rcases contextConvSubst hΓ' with ⟨wfΓ, wfΓ', _⟩
      rcases contextConvSubst hΔ with ⟨_, wfΔ, _⟩
      rcases ihF (.cons hΓ' (.refl (.nat wfΓ))) (.cons hΔ (.refl (.nat wfΓ'))) hGG with
        ⟨f₁, b₁, hRun₁, hIff₁⟩
      cases b₁ with
      | false =>
          refine ⟨f₁ + 1, none, ?_, (fun _ h ↦ by cases h), ?_⟩
          · dsimp [compareNeutralUp]
            rw [hRun₁]
            rfl
          · intro _ T hConv
            cases hConv with
            | natrec hFG' _ _ _ => exact Bool.noConfusion (hIff₁.mpr hFG')
      | true =>
          have hFG : ConvTypeUp (.nat :: Γ') F G := hIff₁.mp rfl
          have hFG_eq : TypeEq (.nat :: Γ') F G := soundnessConvUp hFG
          have wfF_Γ' : TypeWf (.nat :: Γ') F := (syntacticEq hFG_eq).1
          have hF0_refl : TypeEq Γ' (subst0 F .zero) (subst0 F .zero) :=
            .refl (substType wfF_Γ' (.zero wfΓ'))
          have hFG_Δ : TypeEq (.nat :: Δ) F G :=
            stabilityEq (.cons hΔ (.refl (.nat wfΓ'))) hFG_eq
          have hF0G0_Δ : TypeEq Δ (subst0 F .zero) (subst0 G .zero) :=
            substTypeEq hFG_Δ (.refl (.zero wfΔ))
          rcases iha hΓ' hΔ hbb hF0_refl hF0G0_Δ with ⟨f₂, b₂, hRun₂, hIff₂⟩
          cases b₂ with
          | false =>
              let fuel := Nat.max f₁ f₂
              have hRun₁' := compareTypeUp_mono (Nat.le_max_left f₁ f₂) hRun₁
              have hRun₂' := compareTermUp_mono (Nat.le_max_right f₁ f₂) hRun₂
              refine ⟨fuel + 1, none, ?_, (fun _ h ↦ by cases h), ?_⟩
              · dsimp [compareNeutralUp]
                rw [hRun₁']
                dsimp [Bind.bind, Option.bind]
                rw [hRun₂']
                rfl
              · intro _ T hConv
                cases hConv with
                | natrec _ hab' _ _ => exact Bool.noConfusion (hIff₂.mpr hab')
          | true =>
              have hab : ConvTermUp Γ' a₀ b₂ (subst0 F .zero) := hIff₂.mp rfl
              have hStep_refl : TypeEq Γ' (recStepType F) (recStepType F) :=
                sucCong (.refl wfF_Γ')
              have hStep_Δ : TypeEq Δ (recStepType F) (recStepType G) :=
                sucCong hFG_Δ
              rcases ihh hΓ' hΔ hgg hStep_refl hStep_Δ with ⟨f₃, b₃, hRun₃, hIff₃⟩
              cases b₃ with
              | false =>
                  let m23 := Nat.max f₂ f₃
                  let fuel := Nat.max f₁ m23
                  have hRun₁' := compareTypeUp_mono (Nat.le_max_left f₁ m23) hRun₁
                  have hRun₂' := compareTermUp_mono
                    (Nat.le_trans (Nat.le_max_left f₂ f₃) (Nat.le_max_right f₁ m23)) hRun₂
                  have hRun₃' := compareTermUp_mono
                    (Nat.le_trans (Nat.le_max_right f₂ f₃) (Nat.le_max_right f₁ m23)) hRun₃
                  refine ⟨fuel + 1, none, ?_, (fun _ h ↦ by cases h), ?_⟩
                  · dsimp [compareNeutralUp]
                    rw [hRun₁']
                    dsimp [Bind.bind, Option.bind]
                    rw [hRun₂']
                    dsimp [Bind.bind, Option.bind]
                    rw [hRun₃']
                    rfl
                  · intro _ T hConv
                    cases hConv with
                    | natrec _ _ hhg' _ => exact Bool.noConfusion (hIff₃.mpr hhg')
              | true =>
                  have hhg : ConvTermUp Γ' h g (recStepType F) := hIff₃.mp rfl
                  rcases ihk hΓ' hΔ hll with ⟨f₄, res₄, hRun₄, hSome₄, hNone₄⟩
                  let m12 := Nat.max f₁ f₂
                  let m34 := Nat.max f₃ f₄
                  let fuel := Nat.max m12 m34
                  have hRun₁' := compareTypeUp_mono
                    (Nat.le_trans (Nat.le_max_left f₁ f₂) (Nat.le_max_left m12 m34)) hRun₁
                  have hRun₂' := compareTermUp_mono
                    (Nat.le_trans (Nat.le_max_right f₁ f₂) (Nat.le_max_left m12 m34)) hRun₂
                  have hRun₃' := compareTermUp_mono
                    (Nat.le_trans (Nat.le_max_left f₃ f₄) (Nat.le_max_right m12 m34)) hRun₃
                  have hRun₄' := compareNeutralDown_mono
                    (Nat.le_trans (Nat.le_max_right f₃ f₄) (Nat.le_max_right m12 m34)) hRun₄
                  cases res₄ with
                  | none =>
                      refine ⟨fuel + 1, none, ?_, (fun _ h ↦ by cases h), ?_⟩
                      · dsimp [compareNeutralUp]
                        rw [hRun₁']
                        dsimp [Bind.bind, Option.bind]
                        rw [hRun₂']
                        dsimp [Bind.bind, Option.bind]
                        rw [hRun₃']
                        dsimp [Bind.bind, Option.bind]
                        rw [hRun₄']
                      · intro _ T hConv
                        cases hConv with
                        | natrec _ _ _ hkl' => exact hNone₄ rfl .nat hkl'
                  | some M =>
                      have hkl : ConvNeDown Γ' k l M := hSome₄ M rfl
                      have hNatM : TypeEq Γ' .nat M :=
                        uniqueNeDownLeft (stabilityNeDown hΓ' hkk) hkl
                      have hM_eq : M = .nat := nat_eq_A_whnf hNatM (neConvNeDown hkl).1
                      subst hM_eq
                      refine ⟨fuel + 1, some (subst0 F k), ?_, ?_, (fun h ↦ by cases h)⟩
                      · dsimp [compareNeutralUp]
                        rw [hRun₁']
                        dsimp [Bind.bind, Option.bind]
                        rw [hRun₂']
                        dsimp [Bind.bind, Option.bind]
                        rw [hRun₃']
                        dsimp [Bind.bind, Option.bind]
                        rw [hRun₄']
                      · intro T hT
                        cases hT
                        exact .natrec hFG hab hhg hkl

private theorem adeq_neDown_case {Γ : Context} {k k₁ A B : Term}
    (_D : TypeStar Γ A B) (_hw : Whnf B) (_hkk : ConvNeUp Γ k k₁ A)
    (ihk : AdeqNeUpMotive Γ k k₁ A) :
    AdeqNeDownMotive Γ k k₁ B := by
  intro Γ' Δ u u₁ S hΓ' hΔ du
  cases du with
  | mk _ _ huu =>
      rcases ihk hΓ' hΔ huu with ⟨f₁, res₁, hRun₁, hSome₁, hNone₁⟩
      cases res₁ with
      | none =>
          refine ⟨f₁ + 1, none, ?_, (fun _ h ↦ by cases h), ?_⟩
          · dsimp [compareNeutralDown]
            rw [hRun₁]
            rfl
          · intro _ T hConv
            cases hConv with
            | mk _ _ hku => exact hNone₁ rfl _ hku
      | some A' =>
          have hku : ConvNeUp Γ' k u A' := hSome₁ A' rfl
          have wfA' : TypeWf Γ' A' := (syntacticEqTerm (soundnessNeUp hku)).1
          rcases whNorm wfA' with ⟨B', hwB', DB'⟩
          rcases whnfFuel_of_TypeWhnf ⟨DB'.reduction, hwB'⟩ with ⟨f₂, hf₂⟩
          let fuel := Nat.max f₁ f₂
          have hRun₁' := compareNeutralUp_mono (Nat.le_max_left f₁ f₂) hRun₁
          have hRun₂' := hf₂ fuel (Nat.le_max_right f₁ f₂)
          refine ⟨fuel + 1, some B', ?_, ?_, (fun h ↦ by cases h)⟩
          · dsimp [compareNeutralDown]
            rw [hRun₁']
            dsimp [Bind.bind, Option.bind]
            rw [hRun₂']
          · intro T hT
            cases hT
            exact .mk DB'.reduction hwB' hku

private theorem adeq_typeUp_case {Γ : Context} {A A₁ A' A₁' : Term}
    (DA : TypeStar Γ A A') (_DA₁ : TypeStar Γ A₁ A₁')
    (hwA' : Whnf A') (_hwA₁' : Whnf A₁')
    (_hDown : ConvTypeDown Γ A' A₁')
    (ihDown : AdeqTypeDownMotive Γ A' A₁') :
    AdeqTypeUpMotive Γ A A₁ := by
  intro Γ' Δ B B₁ hΓ' hΔ dB
  cases dB with
  | @mk _ _ _ B' _ DB _ hwB' _ hDownB =>
      have DA_Γ' : TypeStar Γ' A A' := stabilityRedStar hΓ' DA
      have DB_Γ' : TypeStar Γ' B B' := stabilityRedStar (symConEq hΔ) DB
      rcases whnfFuel_of_TypeWhnf ⟨DA_Γ', hwA'⟩ with ⟨fA, hfA⟩
      rcases whnfFuel_of_TypeWhnf ⟨DB_Γ', hwB'⟩ with ⟨fB, hfB⟩
      rcases ihDown hΓ' hΔ hDownB with ⟨fD, b, hRunD, hIffD⟩
      let mBD := Nat.max fB fD
      let fuel := Nat.max fA mBD
      have hRunA := hfA fuel (Nat.le_max_left fA mBD)
      have hRunB := hfB fuel (Nat.le_trans (Nat.le_max_left fB fD) (Nat.le_max_right fA mBD))
      have hRunD' := compareTypeDown_mono
        (Nat.le_trans (Nat.le_max_right fB fD) (Nat.le_max_right fA mBD)) hRunD
      refine ⟨fuel + 1, b, ?_, ?_⟩
      · dsimp [compareTypeUp]
        rw [hRunA]
        dsimp [Bind.bind, Option.bind]
        rw [hRunB]
        dsimp [Bind.bind, Option.bind]
        exact hRunD'
      · constructor
        · intro hb
          exact .mk DA_Γ' DB_Γ' hwA' hwB' (hIffD.mp hb)
        · intro hConv
          cases hConv with
          | @mk _ _ _ A'' B'' DA'' DB'' hwA'' hwB'' hDown'' =>
              have eqA : A'' = A' := whrDetStar ⟨DA'', hwA''⟩ ⟨DA_Γ', hwA'⟩
              have eqB : B'' = B' := whrDetStar ⟨DB'', hwB''⟩ ⟨DB_Γ', hwB'⟩
              subst eqA eqB
              exact hIffD.mpr hDown''

private theorem adeq_typeDown_univ_case {Γ : Context} (_hΓ : CtxWf Γ) :
    AdeqTypeDownMotive Γ .univ .univ := by
  intro Γ' Δ B B₁ hΓ' _ dB
  have wfΓ' : CtxWf Γ' := (contextConvSubst hΓ').2.1
  cases dB with
  | univRefl _ =>
      exact ⟨1, true, rfl, ⟨fun _ ↦ .univRefl wfΓ', fun _ ↦ rfl⟩⟩
  | natRefl _ =>
      refine ⟨1, false, rfl, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      intro hConv
      generalize hU : Term.univ = U₀ at hConv
      cases hConv with
      | ne hne => subst hU; cases (neConvNeDown hne).2.1
      | _ => cases hU
  | piCong _ _ _ =>
      refine ⟨1, false, rfl, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      intro hConv
      generalize hU : Term.univ = U₀ at hConv
      cases hConv with
      | ne hne => subst hU; cases (neConvNeDown hne).2.1
      | _ => cases hU
  | ne hneB =>
      have neB : Neutral B := (neConvNeDown hneB).2.1
      refine ⟨1, false, ?_, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      · cases neB <;> rfl
      · intro hConv
        generalize hU : Term.univ = U₀ at hConv
        cases hConv with
        | univRefl _ => cases neB
        | ne hne => subst hU; cases (neConvNeDown hne).2.1
        | _ => cases hU

private theorem adeq_typeDown_nat_case {Γ : Context} (_hΓ : CtxWf Γ) :
    AdeqTypeDownMotive Γ .nat .nat := by
  intro Γ' Δ B B₁ hΓ' _ dB
  have wfΓ' : CtxWf Γ' := (contextConvSubst hΓ').2.1
  cases dB with
  | natRefl _ =>
      exact ⟨1, true, rfl, ⟨fun _ ↦ .natRefl wfΓ', fun _ ↦ rfl⟩⟩
  | univRefl _ =>
      refine ⟨1, false, rfl, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      intro hConv
      generalize hN : Term.nat = N₀ at hConv
      cases hConv with
      | ne hne => subst hN; cases (neConvNeDown hne).2.1
      | _ => cases hN
  | piCong _ _ _ =>
      refine ⟨1, false, rfl, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      intro hConv
      generalize hN : Term.nat = N₀ at hConv
      cases hConv with
      | ne hne => subst hN; cases (neConvNeDown hne).2.1
      | _ => cases hN
  | ne hneB =>
      have neB : Neutral B := (neConvNeDown hneB).2.1
      refine ⟨1, false, ?_, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      · cases neB <;> rfl
      · intro hConv
        generalize hN : Term.nat = N₀ at hConv
        cases hConv with
        | natRefl _ => cases neB
        | ne hne => subst hN; cases (neConvNeDown hne).2.1
        | _ => cases hN

private theorem adeq_typeDown_ne_case {Γ : Context} {K K₁ : Term}
    (hKK : ConvNeDown Γ K K₁ .univ)
    (ihK : AdeqNeDownMotive Γ K K₁ .univ) :
    AdeqTypeDownMotive Γ K K₁ := by
  intro Γ' Δ B B₁ hΓ' hΔ dB
  have neK : Neutral K := (neConvNeDown hKK).2.1
  have hnhK : neutralHead K = true := (neutralHead_iff_Neutral K).mpr neK
  cases dB with
  | univRefl _ =>
      have hcond : ¬ ((neutralHead K && neutralHead .univ) = true) := by
        dsimp [neutralHead]; rw [Bool.and_false]; intro h; cases h
      refine ⟨1, false, ?_, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      · cases neK <;> (dsimp [compareTypeDown]; rw [if_neg hcond])
      · intro hConv
        cases hConv with
        | univRefl _ => cases neK
        | ne hne => cases (neConvNeDown hne).2.2
  | natRefl _ =>
      have hcond : ¬ ((neutralHead K && neutralHead .nat) = true) := by
        dsimp [neutralHead]; rw [Bool.and_false]; intro h; cases h
      refine ⟨1, false, ?_, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      · cases neK <;> (dsimp [compareTypeDown]; rw [if_neg hcond])
      · intro hConv
        cases hConv with
        | natRefl _ => cases neK
        | ne hne => cases (neConvNeDown hne).2.2
  | @piCong _ H E _ _ _ _ _ =>
      have hcond : ¬ ((neutralHead K && neutralHead (.pi H E)) = true) := by
        dsimp [neutralHead]; rw [Bool.and_false]; intro h; cases h
      refine ⟨1, false, ?_, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      · cases neK <;> (dsimp [compareTypeDown]; rw [if_neg hcond])
      · intro hConv
        cases hConv with
        | piCong _ _ _ => cases neK
        | ne hne => cases (neConvNeDown hne).2.2
  | ne hLL =>
      have neB : Neutral B := (neConvNeDown hLL).2.1
      have hnhB : neutralHead B = true := (neutralHead_iff_Neutral B).mpr neB
      have hcond : (neutralHead K && neutralHead B) = true := by rw [hnhK, hnhB]; rfl
      rcases ihK hΓ' hΔ hLL with ⟨f, res, hRun, hSome, hNone⟩
      cases res with
      | none =>
          refine ⟨f + 1, false, ?_, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
          · cases neK <;> cases neB <;>
              (dsimp [compareTypeDown]; rw [if_pos hcond, hRun]; rfl)
          · intro hConv
            cases hConv with
            | univRefl _ => cases neK
            | natRefl _ => cases neK
            | piCong _ _ _ => cases neK
            | ne hKL => exact False.elim (hNone rfl .univ hKL)
      | some M =>
          have hKL : ConvNeDown Γ' K B M := hSome M rfl
          have hUM : TypeEq Γ' .univ M :=
            uniqueNeDownLeft (stabilityNeDown hΓ' hKK) hKL
          have hM_eq : M = .univ := U_eq_A hUM
          subst hM_eq
          refine ⟨f + 1, true, ?_, ⟨fun _ ↦ .ne hKL, fun _ ↦ rfl⟩⟩
          · cases neK <;> cases neB <;>
              (dsimp [compareTypeDown]; rw [if_pos hcond, hRun]; rfl)

private theorem adeq_typeDown_pi_case {Γ : Context} {F G F₁ G₁ : Term}
    (hF : TypeWf Γ F)
    (_hFF : ConvTypeUp Γ F F₁) (_hGG : ConvTypeUp (F :: Γ) G G₁)
    (ihF : AdeqTypeUpMotive Γ F F₁) (ihG : AdeqTypeUpMotive (F :: Γ) G G₁) :
    AdeqTypeDownMotive Γ (.pi F G) (.pi F₁ G₁) := by
  intro Γ' Δ B B₁ hΓ' hΔ dB
  cases dB with
  | univRefl _ =>
      refine ⟨1, false, rfl, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      intro hConv
      generalize hP : Term.pi F G = P₀ at hConv
      cases hConv with
      | ne hne => subst hP; cases (neConvNeDown hne).2.1
      | _ => cases hP
  | natRefl _ =>
      refine ⟨1, false, rfl, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      intro hConv
      generalize hP : Term.pi F G = P₀ at hConv
      cases hConv with
      | ne hne => subst hP; cases (neConvNeDown hne).2.1
      | _ => cases hP
  | ne hLL =>
      have neB : Neutral B := (neConvNeDown hLL).2.1
      refine ⟨1, false, ?_, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      · cases neB <;> rfl
      · intro hConv
        generalize hP : Term.pi F G = P₀ at hConv
        cases hConv with
        | piCong _ _ _ => cases neB
        | ne hne => subst hP; cases (neConvNeDown hne).2.1
        | _ => cases hP
  | @piCong _ H E _ _ _ hHH hEE =>
      rcases ihF hΓ' hΔ hHH with ⟨f₁, b₁, hRun₁, hIff₁⟩
      cases b₁ with
      | false =>
          refine ⟨f₁ + 1, false, ?_, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
          · dsimp [compareTypeDown]
            rw [hRun₁]
            rfl
          · intro hConv
            cases hConv with
            | ne hne => cases (neConvNeDown hne).2.1
            | piCong _ hFH' _ => exact Bool.noConfusion (hIff₁.mpr hFH')
      | true =>
          have hFH : ConvTypeUp Γ' F H := hIff₁.mp rfl
          have hFH_eq : TypeEq Γ' F H := soundnessConvUp hFH
          rcases ihG (.cons hΓ' (.refl hF)) (.cons hΔ hFH_eq) hEE with
            ⟨f₂, b₂, hRun₂, hIff₂⟩
          let fuel := Nat.max f₁ f₂
          have hRun₁' := compareTypeUp_mono (Nat.le_max_left f₁ f₂) hRun₁
          have hRun₂' := compareTypeUp_mono (Nat.le_max_right f₁ f₂) hRun₂
          refine ⟨fuel + 1, b₂, ?_, ?_⟩
          · dsimp [compareTypeDown]
            rw [hRun₁']
            dsimp [Bind.bind, Option.bind]
            exact hRun₂'
          · constructor
            · intro hb₂
              exact .piCong (stability hΓ' hF) hFH (hIff₂.mp hb₂)
            · intro hConv
              cases hConv with
              | ne hne => cases (neConvNeDown hne).2.1
              | piCong _ _ hGE' => exact hIff₂.mpr hGE'

private theorem adeq_termUp_case {Γ : Context} {t t₁ A B t' t₁' : Term}
    (DA : TypeStar Γ A B) (dt : Star Γ t t' B) (_dt₁ : Star Γ t₁ t₁' B)
    (_hwB : Whnf B) (hwt' : Whnf t') (_hwt₁' : Whnf t₁')
    (_htu : ConvTermDown Γ t' t₁' B)
    (ihtu : AdeqTermDownMotive Γ t' t₁' B) :
    AdeqTermUpMotive Γ t t₁ A := by
  intro Γ' Δ u u₁ A' B₀ hΓ' hΔ du hAA' hA'B₀
  cases du with
  | @mk _ _ _ _ C₀ u' _ DB₀ du' _ _ hwu' _ huu =>
      have wfA' : TypeWf Γ' A' := (syntacticEq hAA').2
      rcases whNorm wfA' with ⟨B', hwB', DB'⟩
      have DA_Γ' : TypeStar Γ' A B := stabilityRedStar hΓ' DA
      have hBB' : TypeEq Γ' B B' :=
        .trans (.symm (subsetStar DA_Γ')) (.trans hAA' (subsetStar DB'.reduction))
      have hB'C₀ : TypeEq Δ B' C₀ :=
        .trans (.symm (stabilityEq hΔ (subsetStar DB'.reduction)))
          (.trans hA'B₀ (subsetStar DB₀))
      have hB'C₀_Γ' : TypeEq Γ' B' C₀ := stabilityEq (symConEq hΔ) hB'C₀
      have dt_B' : Star Γ' t t' B' := (stabilityRedStarTerm hΓ' dt).conv hBB'
      have du_B' : Star Γ' u u' B' :=
        (stabilityRedStarTerm (symConEq hΔ) du').conv (.symm hB'C₀_Γ')
      rcases whnfFuel_of_TypeWhnf ⟨DB'.reduction, hwB'⟩ with ⟨fA, hfA⟩
      rcases whnfFuel_of_TermWhnf ⟨dt_B', hwt'⟩ with ⟨ft, hft⟩
      rcases whnfFuel_of_TermWhnf ⟨du_B', hwu'⟩ with ⟨fu, hfu⟩
      rcases ihtu hΓ' hΔ huu hwB' hBB' hB'C₀ with ⟨fD, b, hRunD, hIffD⟩
      let mAt := Nat.max fA ft
      let mUD := Nat.max fu fD
      let fuel := Nat.max mAt mUD
      have hRunA := hfA fuel (Nat.le_trans (Nat.le_max_left fA ft) (Nat.le_max_left mAt mUD))
      have hRunt := hft fuel (Nat.le_trans (Nat.le_max_right fA ft) (Nat.le_max_left mAt mUD))
      have hRunu := hfu fuel (Nat.le_trans (Nat.le_max_left fu fD) (Nat.le_max_right mAt mUD))
      have hRunD' := compareTermDown_mono
        (Nat.le_trans (Nat.le_max_right fu fD) (Nat.le_max_right mAt mUD)) hRunD
      refine ⟨fuel + 1, b, ?_, ?_⟩
      · dsimp [compareTermUp]
        rw [hRunA]
        dsimp [Bind.bind, Option.bind]
        rw [hRunt]
        dsimp [Bind.bind, Option.bind]
        rw [hRunu]
        dsimp [Bind.bind, Option.bind]
        exact hRunD'
      · constructor
        · intro hb
          exact .mk DB'.reduction dt_B' du_B' hwB' hwt' hwu' (hIffD.mp hb)
        · intro hConv
          cases hConv with
          | @mk _ _ _ _ B'' t'' u'' DA'' dt'' du'' hwB'' hwt'' hwu'' hDown'' =>
              have eqB : B'' = B' := whrDetStar ⟨DA'', hwB''⟩ ⟨DB'.reduction, hwB'⟩
              subst eqB
              have eqt : t'' = t' := whrDetStarTerm ⟨dt'', hwt''⟩ ⟨dt_B', hwt'⟩
              have equ : u'' = u' := whrDetStarTerm ⟨du'', hwu''⟩ ⟨du_B', hwu'⟩
              subst eqt equ
              exact hIffD.mpr hDown''

private theorem adeq_termDown_natIns_case {Γ : Context} {k k₁ : Term}
    (hkk : ConvNeDown Γ k k₁ .nat)
    (ihk : AdeqNeDownMotive Γ k k₁ .nat) :
    AdeqTermDownMotive Γ k k₁ .nat := by
  intro Γ' Δ u u₁ A' B₀ hΓ' hΔ du hwA' hAA' hA'B₀
  have hA'_eq : A' = .nat := nat_eq_A_whnf hAA' hwA'
  subst hA'_eq
  have hB₀_eq : B₀ = .nat := nat_eq_A_whnf hA'B₀ (whnfConvTermDown du).1
  have neK : Neutral k := (neConvNeDown hkk).2.1
  have hnhK : neutralHead k = true := (neutralHead_iff_Neutral k).mpr neK
  cases du with
  | univ _ _ _ => cases hB₀_eq
  | etaEq _ _ _ _ _ _ => cases hB₀_eq
  | neIns _ _ neB₀ _ => subst hB₀_eq; cases neB₀
  | zeroRefl _ =>
      have hcond : ¬ ((neutralHead k && neutralHead .zero) = true) := by
        dsimp [neutralHead]; rw [Bool.and_false]; intro h; cases h
      refine ⟨1, false, ?_, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      · cases neK <;> (dsimp [compareTermDown]; rw [if_neg hcond])
      · intro hConv
        generalize hz : Term.zero = z₀ at hConv
        cases hConv with
        | natIns hne => subst hz; cases (neConvNeDown hne).2.2
        | neIns _ _ _ hne => subst hz; cases (neConvNeDown hne).2.2
        | zeroRefl _ => cases neK
        | _ => cases hz
  | @succCong _ n _ _ =>
      have hcond : ¬ ((neutralHead k && neutralHead (.succ n)) = true) := by
        dsimp [neutralHead]; rw [Bool.and_false]; intro h; cases h
      refine ⟨1, false, ?_, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      · cases neK <;> (dsimp [compareTermDown]; rw [if_neg hcond])
      · intro hConv
        generalize hs : Term.succ n = s₀ at hConv
        cases hConv with
        | natIns hne => subst hs; cases (neConvNeDown hne).2.2
        | neIns _ _ _ hne => subst hs; cases (neConvNeDown hne).2.2
        | succCong _ => cases neK
        | _ => cases hs
  | natIns hll =>
      have neU : Neutral u := (neConvNeDown hll).2.1
      have hnhU : neutralHead u = true := (neutralHead_iff_Neutral u).mpr neU
      have hcond : (neutralHead k && neutralHead u) = true := by rw [hnhK, hnhU]; rfl
      rcases ihk hΓ' hΔ hll with ⟨f, res, hRun, hSome, hNone⟩
      cases res with
      | none =>
          refine ⟨f + 1, false, ?_, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
          · cases neK <;> cases neU <;>
              (dsimp [compareTermDown]; rw [if_pos hcond, hRun]; rfl)
          · intro hConv
            generalize hN : Term.nat = N₀ at hConv
            cases hConv with
            | natIns hkl => exact False.elim (hNone rfl .nat hkl)
            | neIns _ _ neN _ => subst hN; cases neN
            | zeroRefl _ => cases neK
            | succCong _ => cases neK
            | _ => cases hN
      | some M =>
          have hkl : ConvNeDown Γ' k u M := hSome M rfl
          have hNatM : TypeEq Γ' .nat M :=
            uniqueNeDownLeft (stabilityNeDown hΓ' hkk) hkl
          have hM_eq : M = .nat := nat_eq_A_whnf hNatM (neConvNeDown hkl).1
          subst hM_eq
          refine ⟨f + 1, true, ?_, ⟨fun _ ↦ .natIns hkl, fun _ ↦ rfl⟩⟩
          · cases neK <;> cases neU <;>
              (dsimp [compareTermDown]; rw [if_pos hcond, hRun]; rfl)

private theorem adeq_termDown_neIns_case {Γ : Context} {k k₁ M N : Term}
    (hk : HasType Γ k N) (_hk₁ : HasType Γ k₁ N) (neN : Neutral N)
    (hkk : ConvNeDown Γ k k₁ M)
    (ihk : AdeqNeDownMotive Γ k k₁ M) :
    AdeqTermDownMotive Γ k k₁ N := by
  intro Γ' Δ u u₁ A' B₀ hΓ' hΔ du hwA' hAA' hA'B₀
  have neA' : Neutral A' := ne_eq_A_whnf neN hAA' hwA'
  have neB₀ : Neutral B₀ := ne_eq_A_whnf neA' hA'B₀ (whnfConvTermDown du).1
  have neK : Neutral k := (neConvNeDown hkk).2.1
  have hnhA' : neutralHead A' = true := (neutralHead_iff_Neutral A').mpr neA'
  have hnhK : neutralHead k = true := (neutralHead_iff_Neutral k).mpr neK
  cases du with
  | univ _ _ _ => cases neB₀
  | natIns _ => cases neB₀
  | zeroRefl _ => cases neB₀
  | succCong _ => cases neB₀
  | etaEq _ _ _ _ _ _ => cases neB₀
  | neIns hl _ _ hll =>
      have neU : Neutral u := (neConvNeDown hll).2.1
      have hnhU : neutralHead u = true := (neutralHead_iff_Neutral u).mpr neU
      have hcond : (neutralHead A' && neutralHead k && neutralHead u) = true := by
        rw [hnhA', hnhK, hnhU]; rfl
      rcases ihk hΓ' hΔ hll with ⟨f, res, hRun, hSome, hNone⟩
      cases res with
      | none =>
          refine ⟨f + 1, false, ?_, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
          · cases neA' <;>
              (dsimp [compareTermDown]; rw [if_pos hcond, hRun]; rfl)
          · intro hConv
            cases hConv with
            | natIns _ => cases neA'
            | univ _ _ _ => cases neA'
            | zeroRefl _ => cases neA'
            | succCong _ => cases neA'
            | etaEq _ _ _ _ _ _ => cases neA'
            | neIns _ _ _ hkl => exact False.elim (hNone rfl _ hkl)
      | some M' =>
          have hkl : ConvNeDown Γ' k u M' := hSome M' rfl
          have hk_A' : HasType Γ' k A' := .conv (stabilityTerm hΓ' hk) hAA'
          have hu_A' : HasType Γ' u A' :=
            stabilityTerm (symConEq hΔ) (.conv hl (.symm hA'B₀))
          refine ⟨f + 1, true, ?_, ⟨fun _ ↦ .neIns hk_A' hu_A' neA' hkl, fun _ ↦ rfl⟩⟩
          · cases neA' <;>
              (dsimp [compareTermDown]; rw [if_pos hcond, hRun]; rfl)

private theorem adeq_termDown_univ_case {Γ : Context} {A A₁ : Term}
    (hA : HasType Γ A .univ) (_hA₁ : HasType Γ A₁ .univ)
    (_hAA : ConvTypeDown Γ A A₁)
    (ihA : AdeqTypeDownMotive Γ A A₁) :
    AdeqTermDownMotive Γ A A₁ .univ := by
  intro Γ' Δ B B₁ A' B₀ hΓ' hΔ dB _ hAA' hA'B₀
  have hA'_eq : A' = .univ := U_eq_A hAA'
  subst hA'_eq
  have hB₀_eq : B₀ = .univ := U_eq_A hA'B₀
  cases dB with
  | natIns _ => cases hB₀_eq
  | zeroRefl _ => cases hB₀_eq
  | succCong _ => cases hB₀_eq
  | etaEq _ _ _ _ _ _ => cases hB₀_eq
  | neIns _ _ neB₀ _ => subst hB₀_eq; cases neB₀
  | univ hB _ hBB =>
      rcases ihA hΓ' hΔ hBB with ⟨f, b, hRun, hIff⟩
      refine ⟨f + 1, b, hRun, ?_⟩
      constructor
      · intro hb
        exact .univ (stabilityTerm hΓ' hA) (stabilityTerm (symConEq hΔ) hB) (hIff.mp hb)
      · intro hConv
        generalize hU : Term.univ = U₀ at hConv
        cases hConv with
        | neIns _ _ neU _ => subst hU; cases neU
        | univ _ _ hAB => exact hIff.mpr hAB
        | _ => cases hU

private theorem adeq_termDown_zero_case {Γ : Context} (_hΓ : CtxWf Γ) :
    AdeqTermDownMotive Γ .zero .zero .nat := by
  intro Γ' Δ u u₁ A' B₀ hΓ' _ du hwA' hAA' hA'B₀
  have wfΓ' : CtxWf Γ' := (contextConvSubst hΓ').2.1
  have hA'_eq : A' = .nat := nat_eq_A_whnf hAA' hwA'
  subst hA'_eq
  have hB₀_eq : B₀ = .nat := nat_eq_A_whnf hA'B₀ (whnfConvTermDown du).1
  cases du with
  | univ _ _ _ => cases hB₀_eq
  | etaEq _ _ _ _ _ _ => cases hB₀_eq
  | neIns _ _ neB₀ _ => subst hB₀_eq; cases neB₀
  | zeroRefl _ =>
      exact ⟨1, true, rfl, ⟨fun _ ↦ .zeroRefl wfΓ', fun _ ↦ rfl⟩⟩
  | succCong _ =>
      refine ⟨1, false, rfl, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      intro hConv
      generalize hz : Term.zero = z₀ at hConv
      cases hConv with
      | natIns hne => subst hz; cases (neConvNeDown hne).2.1
      | neIns _ _ _ hne => subst hz; cases (neConvNeDown hne).2.1
      | _ => cases hz
  | natIns hll =>
      have neU : Neutral u := (neConvNeDown hll).2.1
      refine ⟨1, false, ?_, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      · cases neU <;> rfl
      · intro hConv
        generalize hz : Term.zero = z₀ at hConv
        cases hConv with
        | zeroRefl _ => cases neU
        | natIns hne => subst hz; cases (neConvNeDown hne).2.1
        | neIns _ _ _ hne => subst hz; cases (neConvNeDown hne).2.1
        | _ => cases hz

private theorem adeq_termDown_succ_case {Γ : Context} {m m₁ : Term}
    (_hmm : ConvTermUp Γ m m₁ .nat)
    (ihm : AdeqTermUpMotive Γ m m₁ .nat) :
    AdeqTermDownMotive Γ (.succ m) (.succ m₁) .nat := by
  intro Γ' Δ u u₁ A' B₀ hΓ' hΔ du hwA' hAA' hA'B₀
  have wfΓ' : CtxWf Γ' := (contextConvSubst hΓ').2.1
  have wfΔ : CtxWf Δ := (contextConvSubst hΔ).2.1
  have hA'_eq : A' = .nat := nat_eq_A_whnf hAA' hwA'
  subst hA'_eq
  have hB₀_eq : B₀ = .nat := nat_eq_A_whnf hA'B₀ (whnfConvTermDown du).1
  cases du with
  | univ _ _ _ => cases hB₀_eq
  | etaEq _ _ _ _ _ _ => cases hB₀_eq
  | neIns _ _ neB₀ _ => subst hB₀_eq; cases neB₀
  | zeroRefl _ =>
      refine ⟨1, false, rfl, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      intro hConv
      generalize hs : Term.succ m = s₀ at hConv
      cases hConv with
      | natIns hne => subst hs; cases (neConvNeDown hne).2.1
      | neIns _ _ _ hne => subst hs; cases (neConvNeDown hne).2.1
      | _ => cases hs
  | natIns hll =>
      have neU : Neutral u := (neConvNeDown hll).2.1
      refine ⟨1, false, ?_, ⟨fun h ↦ Bool.noConfusion h, ?_⟩⟩
      · cases neU <;> rfl
      · intro hConv
        generalize hs : Term.succ m = s₀ at hConv
        cases hConv with
        | succCong _ => cases neU
        | natIns hne => subst hs; cases (neConvNeDown hne).2.1
        | neIns _ _ _ hne => subst hs; cases (neConvNeDown hne).2.1
        | _ => cases hs
  | succCong hnn =>
      rcases ihm hΓ' hΔ hnn (.refl (.nat wfΓ')) (.refl (.nat wfΔ)) with
        ⟨f, b, hRun, hIff⟩
      refine ⟨f + 1, b, hRun, ?_⟩
      constructor
      · intro hb
        exact .succCong (hIff.mp hb)
      · intro hConv
        generalize hs : Term.succ m = s₀ at hConv
        cases hConv with
        | natIns hne => subst hs; cases (neConvNeDown hne).2.1
        | neIns _ _ _ hne => subst hs; cases (neConvNeDown hne).2.1
        | succCong hmn =>
            injection hs with hm_eq'
            subst hm_eq'
            exact hIff.mpr hmn
        | _ => cases hs

private theorem adeq_termDown_eta_case {Γ : Context} {f f₁ F G : Term}
    (_hF : TypeWf Γ F) (hf : HasType Γ f (.pi F G)) (_hf₁ : HasType Γ f₁ (.pi F G))
    (hwf : Whnf f) (_hwf₁ : Whnf f₁)
    (_hApp : ConvTermUp (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 f₁) (.var 0)) G)
    (ihApp : AdeqTermUpMotive (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 f₁) (.var 0)) G) :
    AdeqTermDownMotive Γ f f₁ (.pi F G) := by
  intro Γ' Δ u u₁ A' B₀ hΓ' hΔ du hwA' hAA' hA'B₀
  rcases pi_eq_A_whnf hAA' hwA' with ⟨F', G', hA'_eq⟩
  subst hA'_eq
  have ⟨hFF', hGG'_F⟩ := injectivity hAA'
  have wfΓ' : CtxWf Γ' := (contextConvSubst hΓ').2.1
  have ⟨_, wfF'⟩ := syntacticEq hFF'
  have hGG' : TypeEq (F' :: Γ') G G' :=
    stabilityEq (.cons (reflConEq wfΓ') hFF') hGG'_F
  rcases pi_eq_A_whnf hA'B₀ (whnfConvTermDown du).1 with ⟨F₂, G₂, hB₀_eq⟩
  cases du with
  | univ _ _ _ => cases hB₀_eq
  | natIns _ => cases hB₀_eq
  | zeroRefl _ => cases hB₀_eq
  | succCong _ => cases hB₀_eq
  | neIns _ _ neB₀ _ => subst hB₀_eq; cases neB₀
  | @etaEq _ _ _ F₂' G₂' _ hg _ hwg _ hApp_g =>
      injection hB₀_eq with hF₂_eq hG₂_eq
      subst hF₂_eq hG₂_eq
      have ⟨hF'F₂, hG'G₂_F'⟩ := injectivity hA'B₀
      have wfΔ : CtxWf Δ := (contextConvSubst hΔ).2.1
      have hG'G₂ : TypeEq (F₂' :: Δ) G' G₂' :=
        stabilityEq (.cons (reflConEq wfΔ) hF'F₂) hG'G₂_F'
      have hΓ'' : CtxEq (F :: Γ) (F' :: Γ') :=
        .cons hΓ' (stabilityEq (symConEq hΓ') hFF')
      have hΔ'' : CtxEq (F' :: Γ') (F₂' :: Δ) :=
        .cons hΔ (stabilityEq (symConEq hΔ) hF'F₂)
      rcases ihApp hΓ'' hΔ'' hApp_g hGG' hG'G₂ with ⟨fuel, b, hRun, hIff⟩
      refine ⟨fuel + 1, b, hRun, ?_⟩
      constructor
      · intro hb
        have hf_Γ' : HasType Γ' f (.pi F' G') := .conv (stabilityTerm hΓ' hf) hAA'
        have hu_Γ' : HasType Γ' u (.pi F' G') :=
          stabilityTerm (symConEq hΔ) (.conv hg (.symm hA'B₀))
        exact .etaEq wfF' hf_Γ' hu_Γ' hwf hwg (hIff.mp hb)
      · intro hConv
        generalize hP : Term.pi F' G' = P₀ at hConv
        cases hConv with
        | neIns _ _ neP _ => subst hP; cases neP
        | etaEq _ _ _ _ _ hfg =>
            injection hP with hF'_eq hG'_eq
            subst hF'_eq hG'_eq
            exact hIff.mpr hfg
        | _ => cases hP

/-!
## Main Mutual Adequacy Theorems (`compareNeutral*`, `compareType*`, `compareTerm*`)
-/

/-- Executable adequacy of `compareNeutralUp`. -/
theorem compareNeutralUp_adequate {Γ Δ : Context} {t t₁ u u₁ R S : Term}
    (dt : ConvNeUp Γ t t₁ R) (du : ConvNeUp Δ u u₁ S) (hΓΔ : CtxEq Γ Δ) :
    NeUpAdequate Γ t u :=
  (@ConvNeUp.rec
    (fun Γ t t₁ R _ ↦ AdeqNeUpMotive Γ t t₁ R)
    (fun Γ t t₁ R _ ↦ AdeqNeDownMotive Γ t t₁ R)
    (fun Γ A A₁ _ ↦ AdeqTypeUpMotive Γ A A₁)
    (fun Γ A A₁ _ ↦ AdeqTypeDownMotive Γ A A₁)
    (fun Γ t t₁ A _ ↦ AdeqTermUpMotive Γ t t₁ A)
    (fun Γ t t₁ A _ ↦ AdeqTermDownMotive Γ t t₁ A)
    (fun hx hxy ↦ adeq_var_case hx hxy)
    (fun hk ht ihk iht ↦ adeq_app_case hk ht ihk iht)
    (fun hFF haa hhh hkk ihF iha ihh ihk ↦
      adeq_natrec_case hFF haa hhh hkk ihF iha ihh ihk)
    (fun D hw hkk ihk ↦ adeq_neDown_case D hw hkk ihk)
    (fun DA DA₁ hwA' hwA₁' hDown ihDown ↦
      adeq_typeUp_case DA DA₁ hwA' hwA₁' hDown ihDown)
    (fun hΓ ↦ adeq_typeDown_univ_case hΓ)
    (fun hΓ ↦ adeq_typeDown_nat_case hΓ)
    (fun hKK ihK ↦ adeq_typeDown_ne_case hKK ihK)
    (fun hF hFF hGG ihF ihG ↦ adeq_typeDown_pi_case hF hFF hGG ihF ihG)
    (fun DA dt dt₁ hwB hwt' hwt₁' htu ihtu ↦
      adeq_termUp_case DA dt dt₁ hwB hwt' hwt₁' htu ihtu)
    (fun hkk ihk ↦ adeq_termDown_natIns_case hkk ihk)
    (fun hk hk₁ neN hkk ihk ↦ adeq_termDown_neIns_case hk hk₁ neN hkk ihk)
    (fun hA hA₁ hAA ihA ↦ adeq_termDown_univ_case hA hA₁ hAA ihA)
    (fun hΓ ↦ adeq_termDown_zero_case hΓ)
    (fun hmm ihm ↦ adeq_termDown_succ_case hmm ihm)
    (fun hF hf hf₁ hwf hwf₁ hApp ihApp ↦
      adeq_termDown_eta_case hF hf hf₁ hwf hwf₁ hApp ihApp)
    Γ t t₁ R dt) (reflConEq (contextConvSubst hΓΔ).1) hΓΔ du

/-- Executable adequacy of `compareNeutralDown`. -/
theorem compareNeutralDown_adequate {Γ Δ : Context} {t t₁ u u₁ R S : Term}
    (dt : ConvNeDown Γ t t₁ R) (du : ConvNeDown Δ u u₁ S) (hΓΔ : CtxEq Γ Δ) :
    NeDownAdequate Γ t u :=
  match dt with
  | .mk D hw hkk =>
      adeq_neDown_case D hw hkk
        (fun hΓ' hΔ' du' ↦
          compareNeutralUp_adequate (stabilityNeUp hΓ' hkk) du' hΔ')
        (reflConEq (contextConvSubst hΓΔ).1) hΓΔ du

/-- Executable adequacy of `compareTypeDown`. -/
theorem compareTypeDown_adequate {Γ Δ : Context} {A A₁ B B₁ : Term}
    (dA : ConvTypeDown Γ A A₁) (dB : ConvTypeDown Δ B B₁) (hΓΔ : CtxEq Γ Δ) :
    TypeDownAdequate Γ A B :=
  (@ConvTypeDown.rec
    (fun Γ t t₁ R _ ↦ AdeqNeUpMotive Γ t t₁ R)
    (fun Γ t t₁ R _ ↦ AdeqNeDownMotive Γ t t₁ R)
    (fun Γ A A₁ _ ↦ AdeqTypeUpMotive Γ A A₁)
    (fun Γ A A₁ _ ↦ AdeqTypeDownMotive Γ A A₁)
    (fun Γ t t₁ A _ ↦ AdeqTermUpMotive Γ t t₁ A)
    (fun Γ t t₁ A _ ↦ AdeqTermDownMotive Γ t t₁ A)
    (fun hx hxy ↦ adeq_var_case hx hxy)
    (fun hk ht ihk iht ↦ adeq_app_case hk ht ihk iht)
    (fun hFF haa hhh hkk ihF iha ihh ihk ↦
      adeq_natrec_case hFF haa hhh hkk ihF iha ihh ihk)
    (fun D hw hkk ihk ↦ adeq_neDown_case D hw hkk ihk)
    (fun DA DA₁ hwA' hwA₁' hDown ihDown ↦
      adeq_typeUp_case DA DA₁ hwA' hwA₁' hDown ihDown)
    (fun hΓ ↦ adeq_typeDown_univ_case hΓ)
    (fun hΓ ↦ adeq_typeDown_nat_case hΓ)
    (fun hKK ihK ↦ adeq_typeDown_ne_case hKK ihK)
    (fun hF hFF hGG ihF ihG ↦ adeq_typeDown_pi_case hF hFF hGG ihF ihG)
    (fun DA dt dt₁ hwB hwt' hwt₁' htu ihtu ↦
      adeq_termUp_case DA dt dt₁ hwB hwt' hwt₁' htu ihtu)
    (fun hkk ihk ↦ adeq_termDown_natIns_case hkk ihk)
    (fun hk hk₁ neN hkk ihk ↦ adeq_termDown_neIns_case hk hk₁ neN hkk ihk)
    (fun hA hA₁ hAA ihA ↦ adeq_termDown_univ_case hA hA₁ hAA ihA)
    (fun hΓ ↦ adeq_termDown_zero_case hΓ)
    (fun hmm ihm ↦ adeq_termDown_succ_case hmm ihm)
    (fun hF hf hf₁ hwf hwf₁ hApp ihApp ↦
      adeq_termDown_eta_case hF hf hf₁ hwf hwf₁ hApp ihApp)
    Γ A A₁ dA) (reflConEq (contextConvSubst hΓΔ).1) hΓΔ dB

/-- Executable adequacy of `compareTypeUp`. -/
theorem compareTypeUp_adequate {Γ Δ : Context} {A A₁ B B₁ : Term}
    (dA : ConvTypeUp Γ A A₁) (dB : ConvTypeUp Δ B B₁) (hΓΔ : CtxEq Γ Δ) :
    TypeUpAdequate Γ A B :=
  match dA with
  | .mk DA DA₁ hwA' hwA₁' hDown =>
      adeq_typeUp_case DA DA₁ hwA' hwA₁' hDown
        (fun hΓ' hΔ' dB' ↦
          compareTypeDown_adequate (stabilityConvDown hΓ' hDown) dB' hΔ')
        (reflConEq (contextConvSubst hΓΔ).1) hΓΔ dB

/-- Executable adequacy of `compareTermDown`. -/
theorem compareTermDown_adequate {Γ Δ : Context} {t t₁ u u₁ A B : Term}
    (dt : ConvTermDown Γ t t₁ A) (du : ConvTermDown Δ u u₁ B)
    (hΓΔ : CtxEq Γ Δ) (hAB : TypeEq Δ A B) :
    TermDownAdequate Γ t u A :=
  (@ConvTermDown.rec
    (fun Γ t t₁ R _ ↦ AdeqNeUpMotive Γ t t₁ R)
    (fun Γ t t₁ R _ ↦ AdeqNeDownMotive Γ t t₁ R)
    (fun Γ A A₁ _ ↦ AdeqTypeUpMotive Γ A A₁)
    (fun Γ A A₁ _ ↦ AdeqTypeDownMotive Γ A A₁)
    (fun Γ t t₁ A _ ↦ AdeqTermUpMotive Γ t t₁ A)
    (fun Γ t t₁ A _ ↦ AdeqTermDownMotive Γ t t₁ A)
    (fun hx hxy ↦ adeq_var_case hx hxy)
    (fun hk ht ihk iht ↦ adeq_app_case hk ht ihk iht)
    (fun hFF haa hhh hkk ihF iha ihh ihk ↦
      adeq_natrec_case hFF haa hhh hkk ihF iha ihh ihk)
    (fun D hw hkk ihk ↦ adeq_neDown_case D hw hkk ihk)
    (fun DA DA₁ hwA' hwA₁' hDown ihDown ↦
      adeq_typeUp_case DA DA₁ hwA' hwA₁' hDown ihDown)
    (fun hΓ ↦ adeq_typeDown_univ_case hΓ)
    (fun hΓ ↦ adeq_typeDown_nat_case hΓ)
    (fun hKK ihK ↦ adeq_typeDown_ne_case hKK ihK)
    (fun hF hFF hGG ihF ihG ↦ adeq_typeDown_pi_case hF hFF hGG ihF ihG)
    (fun DA dt dt₁ hwB hwt' hwt₁' htu ihtu ↦
      adeq_termUp_case DA dt dt₁ hwB hwt' hwt₁' htu ihtu)
    (fun hkk ihk ↦ adeq_termDown_natIns_case hkk ihk)
    (fun hk hk₁ neN hkk ihk ↦ adeq_termDown_neIns_case hk hk₁ neN hkk ihk)
    (fun hA hA₁ hAA ihA ↦ adeq_termDown_univ_case hA hA₁ hAA ihA)
    (fun hΓ ↦ adeq_termDown_zero_case hΓ)
    (fun hmm ihm ↦ adeq_termDown_succ_case hmm ihm)
    (fun hF hf hf₁ hwf hwf₁ hApp ihApp ↦
      adeq_termDown_eta_case hF hf hf₁ hwf hwf₁ hApp ihApp)
    Γ t t₁ A dt) (reflConEq (contextConvSubst hΓΔ).1) hΓΔ du
    (whnfConvTermDown dt).1 (.refl (syntacticEqTerm (soundnessConvDownTerm dt)).1) hAB

/-- Executable adequacy of `compareTermUp`. -/
theorem compareTermUp_adequate {Γ Δ : Context} {t t₁ u u₁ A B : Term}
    (dt : ConvTermUp Γ t t₁ A) (du : ConvTermUp Δ u u₁ B)
    (hΓΔ : CtxEq Γ Δ) (hAB : TypeEq Δ A B) :
    TermUpAdequate Γ t u A :=
  match dt with
  | .mk DA dt₁ dt₂ hwB hwt₁ hwt₂ htu =>
      adeq_termUp_case DA dt₁ dt₂ hwB hwt₁ hwt₂ htu
        (fun hΓ' hΔ' du' hwA'' hBA'' hA''B' ↦
          compareTermDown_adequate
            (convConvDownTerm hΓ' (stabilityEq (symConEq hΓ') hBA'') hwA'' htu)
            du' hΔ' hA''B')
        (reflConEq (contextConvSubst hΓΔ).1) hΓΔ du
        (.refl (syntacticEqTerm (soundnessConvUpTerm (.mk DA dt₁ dt₂ hwB hwt₁ hwt₂ htu))).1) hAB

/-!
## Decidability of Algorithmic Equality (`Definition/Conversion/Decidable.agda`, Theorem 4.5)
-/

/-- Decidability of `ConvNeUp` (`dec~↑`, Theorem 4.5). -/
theorem decConvNeUp {Γ Δ : Context} {t u R S : Term}
    (dt : ConvNeUp Γ t t R) (du : ConvNeUp Δ u u S) (hΓΔ : CtxEq Γ Δ) :
    (∃ T, ConvNeUp Γ t u T) ∨ ¬ (∃ T, ConvNeUp Γ t u T) := by
  rcases compareNeutralUp_adequate dt du hΓΔ with ⟨_, res, _, hSome, hNone⟩
  cases res with
  | some T => exact .inl ⟨T, hSome T rfl⟩
  | none => exact .inr (fun ⟨T, h⟩ ↦ hNone rfl T h)

/-- Decidability of `ConvNeDown` (`dec~↓`, Theorem 4.5). -/
theorem decConvNeDown {Γ Δ : Context} {t u R S : Term}
    (dt : ConvNeDown Γ t t R) (du : ConvNeDown Δ u u S) (hΓΔ : CtxEq Γ Δ) :
    (∃ T, ConvNeDown Γ t u T) ∨ ¬ (∃ T, ConvNeDown Γ t u T) := by
  rcases compareNeutralDown_adequate dt du hΓΔ with ⟨_, res, _, hSome, hNone⟩
  cases res with
  | some T => exact .inl ⟨T, hSome T rfl⟩
  | none => exact .inr (fun ⟨T, h⟩ ↦ hNone rfl T h)

/-- Decidability of `ConvTypeUp` (`decConv↑`, Theorem 4.5). -/
theorem decConvTypeUp {Γ Δ : Context} {A B : Term}
    (dA : ConvTypeUp Γ A A) (dB : ConvTypeUp Δ B B) (hΓΔ : CtxEq Γ Δ) :
    ConvTypeUp Γ A B ∨ ¬ ConvTypeUp Γ A B := by
  rcases compareTypeUp_adequate dA dB hΓΔ with ⟨_, b, _, hIff⟩
  cases b with
  | true => exact .inl (hIff.mp rfl)
  | false => exact .inr (fun h ↦ Bool.noConfusion (hIff.mpr h))

/-- Decidability of `ConvTypeDown` (`decConv↓`, Theorem 4.5). -/
theorem decConvTypeDown {Γ Δ : Context} {A B : Term}
    (dA : ConvTypeDown Γ A A) (dB : ConvTypeDown Δ B B) (hΓΔ : CtxEq Γ Δ) :
    ConvTypeDown Γ A B ∨ ¬ ConvTypeDown Γ A B := by
  rcases compareTypeDown_adequate dA dB hΓΔ with ⟨_, b, _, hIff⟩
  cases b with
  | true => exact .inl (hIff.mp rfl)
  | false => exact .inr (fun h ↦ Bool.noConfusion (hIff.mpr h))

/-- Decidability of `ConvTermUp` (`decConv↑Term`, Theorem 4.5). -/
theorem decConvTermUp {Γ Δ : Context} {t u A B : Term}
    (dt : ConvTermUp Γ t t A) (du : ConvTermUp Δ u u B)
    (hΓΔ : CtxEq Γ Δ) (hAB : TypeEq Δ A B) :
    ConvTermUp Γ t u A ∨ ¬ ConvTermUp Γ t u A := by
  rcases compareTermUp_adequate dt du hΓΔ hAB with ⟨_, b, _, hIff⟩
  cases b with
  | true => exact .inl (hIff.mp rfl)
  | false => exact .inr (fun h ↦ Bool.noConfusion (hIff.mpr h))

/-- Decidability of `ConvTermDown` (`decConv↓Term`, Theorem 4.5). -/
theorem decConvTermDown {Γ Δ : Context} {t u A B : Term}
    (dt : ConvTermDown Γ t t A) (du : ConvTermDown Δ u u B)
    (hΓΔ : CtxEq Γ Δ) (hAB : TypeEq Δ A B) :
    ConvTermDown Γ t u A ∨ ¬ ConvTermDown Γ t u A := by
  rcases compareTermDown_adequate dt du hΓΔ hAB with ⟨_, b, _, hIff⟩
  cases b with
  | true => exact .inl (hIff.mp rfl)
  | false => exact .inr (fun h ↦ Bool.noConfusion (hIff.mpr h))

/-!
## Decidability of Judgmental Equality (`Definition/Typed/Decidable.agda`, Theorem 4.12)
and Executable Adequacy Target (`formalization/abel2018/algorithm-goal.md`)
-/

/-- Decidability of judgmental type equality (`dec`, Theorem 4.12). -/
theorem dec {Γ : Context} {A B : Term} (hA : TypeWf Γ A) (hB : TypeWf Γ B) :
    TypeEq Γ A B ∨ ¬ TypeEq Γ A B := by
  rcases decConvTypeUp (completeEq (.refl hA)) (completeEq (.refl hB)) (reflConEq (wfType hA)) with
    hConv | hNotConv
  · exact .inl (soundnessConvUp hConv)
  · exact .inr (fun hEq ↦ hNotConv (completeEq hEq))

/-- Decidability of judgmental term equality (`decTerm`, Theorem 4.12). -/
theorem decTerm {Γ : Context} {t u A : Term} (ht : HasType Γ t A) (hu : HasType Γ u A) :
    TermEq Γ t u A ∨ ¬ TermEq Γ t u A := by
  have wfA : TypeWf Γ A := syntacticTerm ht
  rcases decConvTermUp (completeEqTerm (.refl ht)) (completeEqTerm (.refl hu))
      (reflConEq (wfTerm ht)) (.refl wfA) with
    hConv | hNotConv
  · exact .inl (soundnessConvUpTerm hConv)
  · exact .inr (fun hEq ↦ hNotConv (completeEqTerm hEq))

/-- Executable adequacy and correctness of `compareTypeUp` on well-formed types
(`formalization/abel2018/algorithm-goal.md`). -/
theorem compareTypeUp_decides_typeEq {Γ : Context} {A B : Term}
    (hA : TypeWf Γ A) (hB : TypeWf Γ B) :
    (∃ fuel b, compareTypeUp fuel Γ A B = some b) ∧
    (∀ fuel b, compareTypeUp fuel Γ A B = some b → (b = true ↔ TypeEq Γ A B)) := by
  apply compareTypeUp_all_runs_correct
  rcases compareTypeUp_adequate (completeEq (.refl hA)) (completeEq (.refl hB))
      (reflConEq (wfType hA)) with ⟨fuel, b, hRun, hIff⟩
  refine ⟨fuel, b, hRun, ?_⟩
  exact hIff.trans ⟨soundnessConvUp, completeEq⟩

/-- Executable adequacy and correctness of `compareTermUp` on well-typed terms
(`formalization/abel2018/algorithm-goal.md`). -/
theorem compareTermUp_decides_termEq {Γ : Context} {t u A : Term}
    (ht : HasType Γ t A) (hu : HasType Γ u A) :
    (∃ fuel b, compareTermUp fuel Γ t u A = some b) ∧
    (∀ fuel b, compareTermUp fuel Γ t u A = some b → (b = true ↔ TermEq Γ t u A)) := by
  apply compareTermUp_all_runs_correct
  have wfA : TypeWf Γ A := syntacticTerm ht
  rcases compareTermUp_adequate (completeEqTerm (.refl ht)) (completeEqTerm (.refl hu))
      (reflConEq (wfTerm ht)) (.refl wfA) with ⟨fuel, b, hRun, hIff⟩
  refine ⟨fuel, b, hRun, ?_⟩
  exact hIff.trans ⟨soundnessConvUpTerm, completeEqTerm⟩

/-- Combined computational Theorem 4.12 (`formalization/abel2018/algorithm-goal.md`):
both `compareTypeUp` on well-formed types and `compareTermUp` on well-typed terms
terminate for some finite fuel budget and return the exact judgmental equality decision
at every successful fuel budget. -/
theorem theorem_4_12_computational :
    (∀ (Γ : Context) (A B : Term), TypeWf Γ A → TypeWf Γ B →
      (∃ fuel b, compareTypeUp fuel Γ A B = some b) ∧
      (∀ fuel b, compareTypeUp fuel Γ A B = some b →
        (b = true ↔ TypeEq Γ A B))) ∧
    (∀ (Γ : Context) (t u A : Term), HasType Γ t A → HasType Γ u A →
      (∃ fuel b, compareTermUp fuel Γ t u A = some b) ∧
      (∀ fuel b, compareTermUp fuel Γ t u A = some b →
        (b = true ↔ TermEq Γ t u A))) :=
  ⟨fun _ _ _ hA hB ↦ compareTypeUp_decides_typeEq hA hB,
   fun _ _ _ _ ht hu ↦ compareTermUp_decides_termEq ht hu⟩

end Abel2018
