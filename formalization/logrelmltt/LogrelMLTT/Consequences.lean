/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Typed/Consequences/Syntactic.agda,
Definition/Typed/Consequences/Injectivity.agda,
Definition/Typed/Consequences/Equality.agda,
Definition/Typed/Consequences/Inequality.agda,
Definition/Typed/Consequences/Substitution.agda,
Definition/Typed/Consequences/Inversion.agda,
Definition/Typed/Consequences/InverseUniv.agda,
Definition/Typed/Consequences/NeTypeEq.agda,
Definition/Typed/Consequences/SucCong.agda,
Definition/Typed/Consequences/Reduction.agda,
Definition/Typed/Consequences/Canonicity.agda,
Definition/Typed/Consequences/Consistency.agda.
-/
import LogrelMLTT.Fundamental

namespace LogrelMLTT

/-!
## Single-Sort Induction Helpers for `CtxWf`, `TypeWf`, and `TypeEq`
-/

theorem CtxWf.indOnly
    {motive : ∀ (Γ : Context), CtxWf Γ → Prop}
    (nil : motive [] .nil)
    (cons : ∀ {Γ A} (hΓ : CtxWf Γ) (hA : TypeWf Γ A),
      motive Γ hΓ → motive (A :: Γ) (.cons hΓ hA))
    {Γ : Context} (d : CtxWf Γ) : motive Γ d :=
  @CtxWf.rec
    motive
    (fun _ _ _ ↦ True)
    (fun _ _ _ _ ↦ True)
    (fun _ _ _ _ ↦ True)
    (fun _ _ _ _ _ ↦ True)
    nil
    (fun hΓ hA ihΓ _ ↦ cons hΓ hA ihΓ)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
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
    Γ d

theorem TypeWf.indOnly
    {motive : ∀ (Γ : Context) (A : Term), TypeWf Γ A → Prop}
    (nat : ∀ {Γ} (hΓ : CtxWf Γ), motive Γ .nat (.nat hΓ))
    (univ : ∀ {Γ} (hΓ : CtxWf Γ), motive Γ .univ (.univ hΓ))
    (pi : ∀ {Γ F G} (hF : TypeWf Γ F) (hG : TypeWf (F :: Γ) G),
      motive Γ F hF → motive (F :: Γ) G hG → motive Γ (.pi F G) (.pi hF hG))
    (fromUniv : ∀ {Γ A} (hA : HasType Γ A .univ), motive Γ A (.fromUniv hA))
    {Γ : Context} {A : Term} (d : TypeWf Γ A) : motive Γ A d :=
  @TypeWf.rec
    (fun _ _ ↦ True)
    motive
    (fun _ _ _ _ ↦ True)
    (fun _ _ _ _ ↦ True)
    (fun _ _ _ _ _ ↦ True)
    trivial
    (fun _ _ _ _ ↦ trivial)
    (fun hΓ _ ↦ nat hΓ)
    (fun hΓ _ ↦ univ hΓ)
    (fun hF hG ihF ihG ↦ pi hF hG ihF ihG)
    (fun hA _ ↦ fromUniv hA)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
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
    Γ A d

theorem TypeEq.indOnly
    {motive : ∀ (Γ : Context) (A B : Term), TypeEq Γ A B → Prop}
    (fromUniv : ∀ {Γ A B} (h : TermEq Γ A B .univ), motive Γ A B (.fromUniv h))
    (refl : ∀ {Γ A} (hA : TypeWf Γ A), motive Γ A A (.refl hA))
    (symm : ∀ {Γ A B} (h : TypeEq Γ A B), motive Γ A B h → motive Γ B A (.symm h))
    (trans : ∀ {Γ A B C} (h₁ : TypeEq Γ A B) (h₂ : TypeEq Γ B C),
      motive Γ A B h₁ → motive Γ B C h₂ → motive Γ A C (.trans h₁ h₂))
    (pi : ∀ {Γ F H G E} (hF : TypeWf Γ F) (hFH : TypeEq Γ F H) (hGE : TypeEq (F :: Γ) G E),
      motive Γ F H hFH → motive (F :: Γ) G E hGE →
      motive Γ (.pi F G) (.pi H E) (.pi hF hFH hGE))
    {Γ : Context} {A B : Term} (d : TypeEq Γ A B) : motive Γ A B d :=
  @TypeEq.rec
    (fun _ _ ↦ True)
    (fun _ _ _ ↦ True)
    (fun _ _ _ _ ↦ True)
    motive
    (fun _ _ _ _ _ ↦ True)
    trivial
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ ↦ trivial)
    (fun _ _ _ _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ trivial)
    (fun h _ ↦ fromUniv h)
    (fun hA _ ↦ refl hA)
    (fun h ih ↦ symm h ih)
    (fun h₁ h₂ ih₁ ih₂ ↦ trans h₁ h₂ ih₁ ih₂)
    (fun hF hFH hGE _ ihFH ihGE ↦ pi hF hFH hGE ihFH ihGE)
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
    Γ A B d

/-!
## Syntactic Validity (`Definition/Typed/Consequences/Syntactic.agda`, Theorem 3.24)
-/

/-- Syntactic validity of type equality (`syntacticEq`). -/
theorem syntacticEq {Γ : Context} {A B : Term} (hAB : TypeEq Γ A B) :
    TypeWf Γ A ∧ TypeWf Γ B := by
  rcases reducibleEq (eqrel := synEqRel) hAB with ⟨pA, pB, _⟩
  exact ⟨escape pA, escape pB⟩

/-- Syntactic validity of terms: the type of a well-formed term is well-formed (`syntacticTerm`). -/
theorem syntacticTerm {Γ : Context} {t A : Term} (ht : HasType Γ t A) :
    TypeWf Γ A := by
  rcases reducibleTerm (eqrel := synEqRel) ht with ⟨pA, _⟩
  exact escape pA

/-- Syntactic validity of term equality (`syntacticEqTerm`). -/
theorem syntacticEqTerm {Γ : Context} {t u A : Term} (htu : TermEq Γ t u A) :
    TypeWf Γ A ∧ HasType Γ t A ∧ HasType Γ u A := by
  rcases fundamentalTermEq (eqrel := synEqRel) htu with ⟨vΓ, vA, vt, vu, _⟩
  exact ⟨escape (reducibleValid vΓ vA),
    escapeTerm (reducibleValid vΓ vA) (reducibleValidTerm vΓ vA vt),
    escapeTerm (reducibleValid vΓ vA) (reducibleValidTerm vΓ vA vu)⟩

/-- Syntactic validity of type reduction (`syntacticRed`). -/
theorem syntacticRed {Γ : Context} {A B : Term} (hAB : TypeStar Γ A B) :
    TypeWf Γ A ∧ TypeWf Γ B :=
  syntacticEq (subsetStar hAB)

/-- Syntactic validity of term reduction (`syntacticRedTerm`). -/
theorem syntacticRedTerm {Γ : Context} {t u A : Term} (htu : Star Γ t u A) :
    TypeWf Γ A ∧ HasType Γ t A ∧ HasType Γ u A :=
  syntacticEqTerm (subsetStarTerm htu)

/-- Syntactic validity of `Π`-types (`syntacticΠ`). -/
theorem syntacticPi {Γ : Context} {F G : Term} (hPi : TypeWf Γ (.pi F G)) :
    TypeWf Γ F ∧ TypeWf (F :: Γ) G := by
  have pPi := reducible (eqrel := synEqRel) hPi
  rcases elimPiAt' (.refl hPi) pPi with ⟨_, piA⟩
  exact ⟨piA.hF, piA.hG⟩

/-!
## Injectivity of `Π`-Types (`Definition/Typed/Consequences/Injectivity.agda`, Theorem 3.26)
-/

/-- Injectivity of `Π` for type equality (`injectivity`, Theorem 3.26). -/
theorem injectivity {Γ : Context} {F G H E : Term}
    (h : TypeEq Γ (.pi F G) (.pi H E)) :
    TypeEq Γ F H ∧ TypeEq (F :: Γ) G E := by
  rcases reducibleEq (eqrel := synEqRel) h with ⟨pFG, _pHE, hEq⟩
  rcases elimPiAt' (.refl (escape pFG)) pFG with ⟨l₀, piFG⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ rel ↦ LogRelAt synEqRel l₀ Δ (wk ρ F) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ a rel ↦ LogRelAt synEqRel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel
  have hAt : LogRelAt synEqRel l₀ Γ (.pi F G) (RedPiRel synEqRel Γ F G relF₀ relG₀) :=
    .pi piFG.D piFG.hF piFG.hG piFG.AeqA relF₀ relG₀
      piFG.redF (fun _ _ _ hr ↦ hr) piFG.redG (fun _ _ _ _ hs ↦ hs) piFG.Gext
  have pFG₀ : RedType synEqRel l₀ Γ (.pi F G) := ⟨_, hAt⟩
  have hPiEq : RedPiEq synEqRel Γ F G relF₀ relG₀ (.pi H E) :=
    (RedEq_of_LogRelAt hAt pFG₀).mp (irrelevanceEq pFG pFG₀ hEq)
  rcases hPiEq with ⟨F', G', D', _AeqB, FeqF', GeqG'⟩
  have hHE : Term.pi H E = Term.pi F' G' := whnfRedStar D' .pi
  injection hHE with hH hE
  subst hH hE
  have hΓ : CtxWf Γ := wfType piFG.hF
  have hFH_wk : TypeEq Γ (wk .id F) (wk .id H) :=
    escapeEq (piFG.redF .id hΓ) (FeqF' .id hΓ)
  rw [wk_id, wk_id] at hFH_wk
  have hρ₁ : WkCtx (.step .id) (F :: Γ) Γ := .step .id
  have hΔ₁ : CtxWf (F :: Γ) := .cons hΓ piFG.hF
  have hVar0 : HasType (F :: Γ) (.var 0) (wk (.step .id) F) := .var hΔ₁ .here
  have ha0 : RedTerm (piFG.redF hρ₁ hΔ₁) (.var 0) :=
    neuTerm (piFG.redF hρ₁ hΔ₁) (.var 0) hVar0 (.refl hVar0)
  have hGE_wk : TypeEq (F :: Γ)
      (subst0 (wk (.lift (.step .id)) G) (.var 0))
      (subst0 (wk (.lift (.step .id)) E) (.var 0)) :=
    escapeEq (piFG.redG hρ₁ hΔ₁ ha0) (GeqG' hρ₁ hΔ₁ ha0)
  rw [wkSingleSubstId, wkSingleSubstId] at hGE_wk
  exact ⟨hFH_wk, hGE_wk⟩

/-!
## Equality Characterization (`Definition/Typed/Consequences/Equality.agda`, Theorem 3.33)
-/

/-- The only type equal to `U` is `U` (`U≡A`). -/
theorem U_eq_A {Γ : Context} {A : Term} (h : TypeEq Γ .univ A) : A = .univ := by
  rcases reducibleEq (eqrel := synEqRel) h with ⟨pU, _pA, hEq⟩
  have hU := elimU pU
  rcases hU with ⟨l', lt, wf⟩
  have hAt : LogRelAt synEqRel .one Γ .univ
      (RedURel synEqRel (logRelRec synEqRel .one l' lt) Γ) :=
    .U ⟨lt, wf⟩
  exact (RedEq_of_LogRelAt hAt pU).mp hEq

/-- Any type equal to `U` reduces to `U`. -/
theorem U_eq_A_star {Γ : Context} {A : Term} (h : TypeEq Γ .univ A) :
    TypeStar Γ A .univ := by
  have hA := U_eq_A h
  subst hA
  exact .refl (syntacticEq h).1

/-- Any type equal to `ℕ` reduces to `ℕ` (`ℕ≡A`). -/
theorem nat_eq_A {Γ : Context} {A : Term} (h : TypeEq Γ .nat A) :
    TypeStar Γ A .nat := by
  rcases reducibleEq (eqrel := synEqRel) h with ⟨pNat, _pA, hEq⟩
  have D := elimNat pNat
  have hAt : LogRelAt synEqRel .one Γ .nat (RedNatRel synEqRel Γ) := .nat D
  exact (RedEq_of_LogRelAt hAt pNat).mp hEq

/-- Any type equal to a neutral type reduces to a neutral type (`ne≡A`). -/
theorem ne_eq_A {Γ : Context} {K A : Term} (neK : Neutral K) (h : TypeEq Γ K A) :
    ∃ M, TypeStarWf Γ A M ∧ Neutral M := by
  rcases reducibleEq (eqrel := synEqRel) h with ⟨pK, _pA, hEq⟩
  have neA := elimNeAt' (.refl (escape pK)) neK pK
  have hAt : LogRelAt synEqRel .one Γ K (RedNeRel synEqRel Γ K) := .ne neA
  rcases (RedEq_of_LogRelAt hAt pK).mp hEq with ⟨M, D', neM, _⟩
  exact ⟨M, D', neM⟩

/-- Any type equal to a `Π`-type reduces to a `Π`-type (`Π≡A`). -/
theorem pi_eq_A {Γ : Context} {F G A : Term} (h : TypeEq Γ (.pi F G) A) :
    ∃ H E, TypeStar Γ A (.pi H E) := by
  rcases reducibleEq (eqrel := synEqRel) h with ⟨pFG, _pA, hEq⟩
  rcases elimPiAt' (.refl (escape pFG)) pFG with ⟨l₀, piFG⟩
  let relF₀ : Wk → Context → RedRel → Prop :=
    fun ρ Δ rel ↦ LogRelAt synEqRel l₀ Δ (wk ρ F) rel
  let relG₀ : Wk → Context → Term → RedRel → Prop :=
    fun ρ Δ a rel ↦ LogRelAt synEqRel l₀ Δ (subst0 (wk (.lift ρ) G) a) rel
  have hAt : LogRelAt synEqRel l₀ Γ (.pi F G) (RedPiRel synEqRel Γ F G relF₀ relG₀) :=
    .pi piFG.D piFG.hF piFG.hG piFG.AeqA relF₀ relG₀
      piFG.redF (fun _ _ _ hr ↦ hr) piFG.redG (fun _ _ _ _ hs ↦ hs) piFG.Gext
  have pFG₀ : RedType synEqRel l₀ Γ (.pi F G) := ⟨_, hAt⟩
  rcases (RedEq_of_LogRelAt hAt pFG₀).mp (irrelevanceEq pFG pFG₀ hEq) with ⟨H, E, D', _, _, _⟩
  exact ⟨H, E, D'⟩

/-!
## Inequality of Type Constructors (`Definition/Typed/Consequences/Inequality.agda`, Theorem 3.25)
-/

/-- `U` is not judgmentally equal to `ℕ` (`U≢ℕ`). -/
theorem U_ne_nat {Γ : Context} : ¬ TypeEq Γ .univ .nat := by
  intro h
  have hEq := U_eq_A h
  cases hEq

/-- `U` is not judgmentally equal to any type reducing to `ℕ` (`U≢ℕ-red`). -/
theorem U_ne_nat_red {Γ : Context} {A : Term} (hU : TypeEq Γ .univ A) (D : TypeStar Γ A .nat) :
    False :=
  U_ne_nat (.trans hU (subsetStar D))

/-- `U` is not judgmentally equal to any `Π`-type (`U≢Π`). -/
theorem U_ne_pi {Γ : Context} {F G : Term} : ¬ TypeEq Γ .univ (.pi F G) := by
  intro h
  have hEq := U_eq_A h
  cases hEq

/-- `U` is not judgmentally equal to any type reducing to a `Π`-type (`U≢Π-red`). -/
theorem U_ne_pi_red {Γ : Context} {A F G : Term}
    (hU : TypeEq Γ .univ A) (D : TypeStar Γ A (.pi F G)) : False :=
  U_ne_pi (.trans hU (subsetStar D))

/-- `U` is not judgmentally equal to any neutral type (`U≢ne`). -/
theorem U_ne_ne {Γ : Context} {K : Term} (neK : Neutral K) : ¬ TypeEq Γ .univ K := by
  intro h
  have hEq := U_eq_A h
  subst hEq
  cases neK

/-- `U` is not judgmentally equal to any type reducing to a neutral type (`U≢ne-red`). -/
theorem U_ne_ne_red {Γ : Context} {A K : Term} (neK : Neutral K)
    (hU : TypeEq Γ .univ A) (D : TypeStar Γ A K) : False :=
  U_ne_ne neK (.trans hU (subsetStar D))

/-- `ℕ` is not judgmentally equal to any `Π`-type (`ℕ≢Π`). -/
theorem nat_ne_pi {Γ : Context} {F G : Term} : ¬ TypeEq Γ .nat (.pi F G) := by
  intro h
  have hRed := nat_eq_A h
  have hEq := whnfRedStar hRed .pi
  cases hEq

/-- Any type reducing to `ℕ` is not judgmentally equal to any type reducing to `Π` (`ℕ≢Π-red`). -/
theorem nat_ne_pi_red {Γ : Context} {A B F G : Term}
    (hAB : TypeEq Γ A B) (DA : TypeStar Γ A .nat) (DB : TypeStar Γ B (.pi F G)) : False :=
  nat_ne_pi (.trans (.symm (subsetStar DA)) (.trans hAB (subsetStar DB)))

/-- `ℕ` is not judgmentally equal to any neutral type (`ℕ≢ne`). -/
theorem nat_ne_ne {Γ : Context} {K : Term} (neK : Neutral K) : ¬ TypeEq Γ .nat K := by
  intro h
  have hRed := nat_eq_A h
  have hEq := whnfRedStar hRed (.neutral neK)
  subst hEq
  cases neK

/-- Any type reducing to `ℕ` is not judgmentally equal to any type reducing to a neutral (`ℕ≢ne-red`). -/
theorem nat_ne_ne_red {Γ : Context} {A B K : Term} (neK : Neutral K)
    (hAB : TypeEq Γ A B) (DA : TypeStar Γ A .nat) (DB : TypeStar Γ B K) : False :=
  nat_ne_ne neK (.trans (.symm (subsetStar DA)) (.trans hAB (subsetStar DB)))

/-- A `Π`-type is not judgmentally equal to any neutral type (`Π≢ne`). -/
theorem pi_ne_ne {Γ : Context} {F G K : Term} (neK : Neutral K) : ¬ TypeEq Γ (.pi F G) K := by
  intro h
  rcases pi_eq_A h with ⟨H, E, hRed⟩
  have hEq := whnfRedStar hRed (.neutral neK)
  subst hEq
  cases neK

/-- Any type reducing to `Π` is not judgmentally equal to any type reducing to a neutral (`Π≢ne-red`). -/
theorem pi_ne_ne_red {Γ : Context} {A B F G K : Term} (neK : Neutral K)
    (hAB : TypeEq Γ A B) (DA : TypeStar Γ A (.pi F G)) (DB : TypeStar Γ B K) : False :=
  pi_ne_ne neK (.trans (.symm (subsetStar DA)) (.trans hAB (subsetStar DB)))

/-!
## Syntactic Substitution Consequences (`Definition/Typed/Consequences/Substitution.agda`, Theorem 3.32)
-/

/-- Syntactic substitution of well-formed types (`substitution`, Theorem 3.32). -/
theorem substitution {Γ Δ : Context} {A : Term} {σ : Subst}
    (hA : TypeWf Γ A) (hσ : SubstWf Δ σ Γ) (hΔ : CtxWf Δ) :
    TypeWf Δ (subst σ A) := by
  rcases fundamental (eqrel := synEqRel) hA with ⟨vΓ, vA⟩
  rcases fundamentalSubst (eqrel := synEqRel) (soundContext vΓ) hΔ hσ with ⟨_, vσ⟩
  exact escape (vA hΔ vσ).red

/-- Syntactic substitution of type equality (`substitutionEq`, Theorem 3.32). -/
theorem substitutionEq {Γ Δ : Context} {A B : Term} {σ σ' : Subst}
    (hAB : TypeEq Γ A B) (hσσ' : SubstEq Δ σ σ' Γ) (hΔ : CtxWf Δ) :
    TypeEq Δ (subst σ A) (subst σ' B) := by
  rcases fundamentalEq (eqrel := synEqRel) hAB with ⟨vΓ, vA, vB, vAB⟩
  rcases fundamentalSubstEq (eqrel := synEqRel) (soundContext vΓ) hΔ hσσ' with ⟨_, vσ, vσ', vσσ'⟩
  exact escapeEq (vA hΔ vσ).red
    (transEq (vA hΔ vσ).red (vA hΔ vσ').red (vB hΔ vσ').red
      ((vA hΔ vσ).eq vσ' vσσ')
      (vAB hΔ vσ'))

/-- Syntactic substitution of well-formed terms (`substitutionTerm`, Theorem 3.32). -/
theorem substitutionTerm {Γ Δ : Context} {t A : Term} {σ : Subst}
    (ht : HasType Γ t A) (hσ : SubstWf Δ σ Γ) (hΔ : CtxWf Δ) :
    HasType Δ (subst σ t) (subst σ A) := by
  rcases fundamentalTerm (eqrel := synEqRel) ht with ⟨vΓ, vA, vt⟩
  rcases fundamentalSubst (eqrel := synEqRel) (soundContext vΓ) hΔ hσ with ⟨_, vσ⟩
  exact escapeTerm (vA hΔ vσ).red (vt hΔ vσ).term

/-- Syntactic substitution of term equality (`substitutionEqTerm`, Theorem 3.32). -/
theorem substitutionEqTerm {Γ Δ : Context} {t u A : Term} {σ σ' : Subst}
    (htu : TermEq Γ t u A) (hσσ' : SubstEq Δ σ σ' Γ) (hΔ : CtxWf Δ) :
    TermEq Δ (subst σ t) (subst σ' u) (subst σ A) := by
  rcases fundamentalTermEq (eqrel := synEqRel) htu with ⟨vΓ, vA, _vt, vu, vtu⟩
  rcases fundamentalSubstEq (eqrel := synEqRel) (soundContext vΓ) hΔ hσσ' with ⟨_, vσ, vσ', vσσ'⟩
  have pσA := (vA hΔ vσ).red
  exact escapeTermEq pσA
    (transEqTerm pσA (vtu hΔ vσ) ((vu hΔ vσ).eq vσ' vσσ'))

/-- Reflexivity of well-formed substitution (`substRefl`). -/
theorem substRefl {Γ Δ : Context} {σ : Subst} (hσ : SubstWf Δ σ Γ) :
    SubstEq Δ σ σ Γ := by
  induction hσ with
  | nil => exact .nil
  | cons _ hHead ih => exact .cons ih (.refl hHead)

/-- Weakening of well-formed substitution (`wkSubst′`). -/
theorem wkSubst' {ρ : Wk} {σ : Subst} {Γ Δ Δ' : Context}
    (hΓ : CtxWf Γ) (_hΔ : CtxWf Δ) (hΔ' : CtxWf Δ')
    (hρ : WkCtx ρ Δ' Δ) (hσ : SubstWf Δ σ Γ) :
    SubstWf Δ' (wkSubst ρ σ) Γ := by
  induction hσ with
  | nil => exact .nil
  | @cons Γ A σ _ hHead ih =>
      cases hΓ with
      | cons wfΓ _ =>
          refine .cons (ih wfΓ) ?_
          have hHead' : HasType Δ' (wk ρ (headSubst σ)) (wk ρ (subst (tailSubst σ) A)) :=
            wkHasType hρ hΔ' hHead
          rwa [wk_subst] at hHead'

/-- Weakening of well-formed substitution by one variable (`wk1Subst′`). -/
theorem wk1Subst' {F : Term} {σ : Subst} {Γ Δ : Context}
    (hΓ : CtxWf Γ) (hΔ : CtxWf Δ) (hF : TypeWf Δ F) (hσ : SubstWf Δ σ Γ) :
    SubstWf (F :: Δ) (wk1Subst σ) Γ :=
  wkSubst' hΓ hΔ (.cons hΔ hF) (.step .id) hσ

/-- Lifting of well-formed substitution (`liftSubst′`). -/
theorem liftSubst' {F : Term} {σ : Subst} {Γ Δ : Context}
    (hΓ : CtxWf Γ) (hΔ : CtxWf Δ) (hF : TypeWf Γ F) (hσ : SubstWf Δ σ Γ) :
    SubstWf (subst σ F :: Δ) (liftSubst σ) (F :: Γ) := by
  have wfσF : TypeWf Δ (subst σ F) := substitution hF hσ hΔ
  have wfΔF : CtxWf (subst σ F :: Δ) := .cons hΔ wfσF
  refine .cons (wkSubst' hΓ hΔ wfΔF (.step .id) hσ) ?_
  have hVar0 : HasType (subst σ F :: Δ) (.var 0) (wk (.step .id) (subst σ F)) :=
    .var wfΔF .here
  change HasType (subst σ F :: Δ) (.var 0) (subst (wkSubst (.step .id) σ) F)
  rwa [← wk_subst]

/-- Well-formed identity substitution (`idSubst′`). -/
theorem idSubst' {Γ : Context} (hΓ : CtxWf Γ) : SubstWf Γ idSubst Γ := by
  induction hΓ using CtxWf.indOnly with
  | nil => exact .nil
  | @cons Γ A wfΓ wfA ih =>
      refine .cons (wk1Subst' wfΓ wfΓ wfA ih) ?_
      have hVar0 : HasType (A :: Γ) (.var 0) (wk1 A) := .var (.cons wfΓ wfA) .here
      rwa [wk1_tailId] at hVar0

/-- Well-formed substitution composition (`substComp′`). -/
theorem substComp' {σ σ' : Subst} {Γ Δ Δ' : Context}
    (hΓ : CtxWf Γ) (_hΔ : CtxWf Δ) (hΔ' : CtxWf Δ')
    (hσ : SubstWf Δ' σ Δ) (hσ' : SubstWf Δ σ' Γ) :
    SubstWf Δ' (compSubst σ σ') Γ := by
  induction hσ' with
  | nil => exact .nil
  | @cons Γ A σ' _ hHead ih =>
      cases hΓ with
      | cons wfΓ _ =>
          refine .cons (ih wfΓ) ?_
          have hHead' : HasType Δ' (subst σ (headSubst σ')) (subst σ (subst (tailSubst σ') A)) :=
            substitutionTerm hHead hσ hΔ'
          rwa [substCompEq] at hHead'

/-- Well-formed singleton substitution (`singleSubst`). -/
theorem singleSubst {Γ : Context} {A t : Term} (ht : HasType Γ t A) :
    SubstWf Γ (sgSubst t) (A :: Γ) := by
  have hΓ := wfTerm ht
  refine .cons (idSubst' hΓ) ?_
  change HasType Γ t (subst idSubst A)
  rwa [subst_id]

/-- Well-formed singleton substitution equality (`singleSubstEq`). -/
theorem singleSubstEq {Γ : Context} {A t u : Term} (htu : TermEq Γ t u A) :
    SubstEq Γ (sgSubst t) (sgSubst u) (A :: Γ) := by
  have hΓ := wfTermEq htu
  refine .cons (substRefl (idSubst' hΓ)) ?_
  change TermEq Γ t u (subst idSubst A)
  rwa [subst_id]

/-- Well-formed lifted singleton substitution (`singleSubst↑`). -/
theorem singleSubstUp {Γ : Context} {A t : Term} (ht : HasType (A :: Γ) t (wk1 A)) :
    SubstWf (A :: Γ) (consSubst (wk1Subst idSubst) t) (A :: Γ) := by
  cases wfTerm ht with
  | cons wfΓ wfA =>
      refine .cons (wk1Subst' wfΓ wfΓ wfA (idSubst' wfΓ)) ?_
      change HasType (A :: Γ) t (subst (wkSubst (.step .id) idSubst) A)
      rw [← wk_subst, subst_id]
      exact ht

/-- Well-formed lifted singleton substitution equality (`singleSubst↑Eq`). -/
theorem singleSubstUpEq {Γ : Context} {A t u : Term}
    (htu : TermEq (A :: Γ) t u (wk1 A)) :
    SubstEq (A :: Γ) (consSubst (wk1Subst idSubst) t) (consSubst (wk1Subst idSubst) u) (A :: Γ) := by
  cases wfTermEq htu with
  | cons wfΓ wfA =>
      refine .cons (substRefl (wk1Subst' wfΓ wfΓ wfA (idSubst' wfΓ))) ?_
      change TermEq (A :: Γ) t u (subst (wkSubst (.step .id) idSubst) A)
      rw [← wk_subst, subst_id]
      exact htu

/-- Single variable substitution in types (`substType`). -/
theorem substType {Γ : Context} {F G t : Term}
    (hG : TypeWf (F :: Γ) G) (ht : HasType Γ t F) :
    TypeWf Γ (subst0 G t) :=
  substitution hG (singleSubst ht) (wfTerm ht)

/-- Single variable substitution in type equality (`substTypeEq`). -/
theorem substTypeEq {Γ : Context} {F G E t u : Term}
    (hGE : TypeEq (F :: Γ) G E) (htu : TermEq Γ t u F) :
    TypeEq Γ (subst0 G t) (subst0 E u) :=
  substitutionEq hGE (singleSubstEq htu) (wfTermEq htu)

/-- Single variable substitution in terms (`substTerm`). -/
theorem substTerm {Γ : Context} {F G t f : Term}
    (hf : HasType (F :: Γ) f G) (ht : HasType Γ t F) :
    HasType Γ (subst0 f t) (subst0 G t) :=
  substitutionTerm hf (singleSubst ht) (wfTerm ht)

/-- Single variable substitution in the codomain of a well-formed `Π`-type (`substTypeΠ`). -/
theorem substTypePi {Γ : Context} {F G t : Term}
    (hPi : TypeWf Γ (.pi F G)) (ht : HasType Γ t F) :
    TypeWf Γ (subst0 G t) :=
  substType (syntacticPi hPi).2 ht

/-- Lifted single variable substitution in types (`subst↑Type`). -/
theorem substUpType {Γ : Context} {F G t : Term}
    (hG : TypeWf (F :: Γ) G) (ht : HasType (F :: Γ) t (wk1 F)) :
    TypeWf (F :: Γ) (substKeep G t) :=
  substitution hG (singleSubstUp ht) (wfTerm ht)

/-- Lifted single variable substitution in type equality (`subst↑TypeEq`). -/
theorem substUpTypeEq {Γ : Context} {F G E t u : Term}
    (hGE : TypeEq (F :: Γ) G E) (htu : TermEq (F :: Γ) t u (wk1 F)) :
    TypeEq (F :: Γ) (substKeep G t) (substKeep E u) :=
  substitutionEq hGE (singleSubstUpEq htu) (wfTermEq htu)

/-!
## Inversion of Typing (`Definition/Typed/Consequences/Inversion.agda`)
-/

/-- Inversion of typing for variables. -/
theorem inversion_var {Γ : Context} {x : Nat} {A : Term}
    (h : HasType Γ (.var x) A) :
    ∃ B, Member x B Γ ∧ TypeEq Γ A B := by
  generalize ht : Term.var x = t at h
  induction h using HasType.indOnly with
  | var hΓ hx =>
      injection ht with hx'
      subst hx'
      exact ⟨_, hx, .refl (syntacticTerm (.var hΓ hx))⟩
  | conv _ hAB ih =>
      rcases ih ht with ⟨B, hx, hEq⟩
      exact ⟨B, hx, .trans (.symm hAB) hEq⟩
  | _ => cases ht

/-- Inversion of typing for `ℕ` (`inversion-ℕ`). -/
theorem inversion_nat {Γ : Context} {A : Term}
    (h : HasType Γ .nat A) : TypeEq Γ A .univ := by
  generalize ht : Term.nat = t at h
  induction h using HasType.indOnly with
  | nat hΓ => exact .refl (.univ hΓ)
  | conv _ hAB ih => exact .trans (.symm hAB) (ih ht)
  | _ => cases ht

/-- Inversion of typing for `Π F ▹ G` (`inversion-Π`). -/
theorem inversion_pi {Γ : Context} {F G A : Term}
    (h : HasType Γ (.pi F G) A) :
    HasType Γ F .univ ∧ HasType (F :: Γ) G .univ ∧ TypeEq Γ A .univ := by
  generalize ht : Term.pi F G = t at h
  induction h using HasType.indOnly with
  | pi hF hG =>
      injection ht with hF' hG'
      subst hF' hG'
      exact ⟨hF, hG, .refl (.univ (wfTerm hF))⟩
  | conv _ hAB ih =>
      rcases ih ht with ⟨hF, hG, hEq⟩
      exact ⟨hF, hG, .trans (.symm hAB) hEq⟩
  | _ => cases ht

/-- Inversion of typing for `zero` (`inversion-zero`). -/
theorem inversion_zero {Γ : Context} {A : Term}
    (h : HasType Γ .zero A) : TypeEq Γ A .nat := by
  generalize ht : Term.zero = t at h
  induction h using HasType.indOnly with
  | zero hΓ => exact .refl (.nat hΓ)
  | conv _ hAB ih => exact .trans (.symm hAB) (ih ht)
  | _ => cases ht

/-- Inversion of typing for `suc n` (`inversion-suc`). -/
theorem inversion_suc {Γ : Context} {n A : Term}
    (h : HasType Γ (.succ n) A) :
    HasType Γ n .nat ∧ TypeEq Γ A .nat := by
  generalize ht : Term.succ n = t at h
  induction h using HasType.indOnly with
  | succ hn =>
      injection ht with hn'
      subst hn'
      exact ⟨hn, .refl (.nat (wfTerm hn))⟩
  | conv _ hAB ih =>
      rcases ih ht with ⟨hn, hEq⟩
      exact ⟨hn, .trans (.symm hAB) hEq⟩
  | _ => cases ht

/-- Inversion of typing for `natrec F z s n` (`inversion-natrec`). -/
theorem inversion_natrec {Γ : Context} {F z s n A : Term}
    (h : HasType Γ (.natrec F z s n) A) :
    TypeWf (.nat :: Γ) F ∧ HasType Γ z (subst0 F .zero) ∧
    HasType Γ s (recStepType F) ∧ HasType Γ n .nat ∧
    TypeEq Γ A (subst0 F n) := by
  generalize ht : Term.natrec F z s n = t at h
  induction h using HasType.indOnly with
  | natrec hF hz hs hn =>
      injection ht with hF' hz' hs' hn'
      subst hF' hz' hs' hn'
      exact ⟨hF, hz, hs, hn, .refl (substType hF hn)⟩
  | conv _ hAB ih =>
      rcases ih ht with ⟨hF, hz, hs, hn, hEq⟩
      exact ⟨hF, hz, hs, hn, .trans (.symm hAB) hEq⟩
  | _ => cases ht

/-- Inversion of typing for `f ∘ a` (`inversion-∘`). -/
theorem inversion_app {Γ : Context} {f a A : Term}
    (h : HasType Γ (.app f a) A) :
    ∃ F G, HasType Γ f (.pi F G) ∧ HasType Γ a F ∧ TypeEq Γ A (subst0 G a) := by
  generalize ht : Term.app f a = t at h
  induction h using HasType.indOnly with
  | app hf ha =>
      injection ht with hf' ha'
      subst hf' ha'
      exact ⟨_, _, hf, ha, .refl (substTypePi (syntacticTerm hf) ha)⟩
  | conv _ hAB ih =>
      rcases ih ht with ⟨F, G, hf, ha, hEq⟩
      exact ⟨F, G, hf, ha, .trans (.symm hAB) hEq⟩
  | _ => cases ht

/-- Inversion of typing for `lam t` (`inversion-lam`). -/
theorem inversion_lam {Γ : Context} {t A : Term}
    (h : HasType Γ (.lam t) A) :
    ∃ F G, TypeWf Γ F ∧ HasType (F :: Γ) t G ∧ TypeEq Γ A (.pi F G) := by
  generalize ht : Term.lam t = u at h
  induction h using HasType.indOnly with
  | lam hF htBody =>
      injection ht with ht'
      subst ht'
      exact ⟨_, _, hF, htBody, .refl (.pi hF (syntacticTerm htBody))⟩
  | conv _ hAB ih =>
      rcases ih ht with ⟨F, G, hF, htBody, hEq⟩
      exact ⟨F, G, hF, htBody, .trans (.symm hAB) hEq⟩
  | _ => cases ht

/-!
## Universe Inversion (`Definition/Typed/Consequences/InverseUniv.agda`)
-/

/-- Predicate characterizing terms that contain `U` (`UFull`). -/
inductive UFull : Term → Prop where
  | univ : UFull .univ
  | pi1 {F G : Term} : UFull F → UFull (.pi F G)
  | pi2 {F G : Term} : UFull G → UFull (.pi F G)

/-- Well-typed terms cannot contain `U` (`noU`). -/
theorem noU {Γ : Context} {t A : Term} (ht : HasType Γ t A) : ¬ UFull t := by
  induction ht using HasType.indOnly with
  | pi _ _ ihF ihG =>
      intro hU
      cases hU with
      | pi1 uF => exact ihF uF
      | pi2 uG => exact ihG uG
  | conv _ _ ih => exact ih
  | _ => intro hU; cases hU

/-- Neutral terms cannot contain `U` (`noUNe`). -/
theorem noUNe {A : Term} (neA : Neutral A) : ¬ UFull A := by
  intro hU
  cases neA <;> cases hU

/-- If a well-formed type `A` does not contain `U`, then `A` is a term of `U` (`inverseUniv`). -/
theorem inverseUniv {Γ : Context} {A : Term}
    (hNotU : ¬ UFull A) (hA : TypeWf Γ A) : HasType Γ A .univ := by
  induction hA using TypeWf.indOnly with
  | nat hΓ => exact .nat hΓ
  | univ _ => exact False.elim (hNotU .univ)
  | pi _ _ ihF ihG =>
      exact .pi (ihF (fun uF ↦ hNotU (.pi1 uF))) (ihG (fun uG ↦ hNotU (.pi2 uG)))
  | fromUniv hA => exact hA

/-- If a neutral term `A` is a well-formed type, then `A` is a term of `U` (`inverseUnivNe`). -/
theorem inverseUnivNe {Γ : Context} {A : Term}
    (neA : Neutral A) (hA : TypeWf Γ A) : HasType Γ A .univ :=
  inverseUniv (noUNe neA) hA

/-- Helper for `inverseUnivEq`: if at least one endpoint of `Γ ⊢ A ≡ B` does not contain `U`,
then `Γ ⊢ A ≡ B ∷ U` (`inverseUnivEq′`). -/
theorem inverseUnivEq' {Γ : Context} {A B : Term}
    (hNotU : (¬ UFull A) ∨ (¬ UFull B)) (hAB : TypeEq Γ A B) :
    TermEq Γ A B .univ := by
  induction hAB using TypeEq.indOnly with
  | fromUniv h => exact h
  | refl hA =>
      rcases hNotU with hNotA | hNotA
      · exact .refl (inverseUniv hNotA hA)
      · exact .refl (inverseUniv hNotA hA)
  | symm _ ih =>
      exact .symm (ih hNotU.symm)
  | trans _ _ ih₁ ih₂ =>
      rcases hNotU with hNotA | hNotC
      · have w := ih₁ (.inl hNotA)
        have ⟨_, _, hB⟩ := syntacticEqTerm w
        exact .trans w (ih₂ (.inl (noU hB)))
      · have w := ih₂ (.inr hNotC)
        have ⟨_, hB, _⟩ := syntacticEqTerm w
        exact .trans (ih₁ (.inr (noU hB))) w
  | pi hF _ _ ihF ihG =>
      rcases hNotU with hNotFG | hNotHE
      · exact .pi hF
          (ihF (.inl (fun uF ↦ hNotFG (.pi1 uF))))
          (ihG (.inl (fun uG ↦ hNotFG (.pi2 uG))))
      · exact .pi hF
          (ihF (.inr (fun uH ↦ hNotHE (.pi1 uH))))
          (ihG (.inr (fun uE ↦ hNotHE (.pi2 uE))))

/-- If `Γ ⊢ A ∷ U` and `Γ ⊢ A ≡ B`, then `Γ ⊢ A ≡ B ∷ U` (`inverseUnivEq`). -/
theorem inverseUnivEq {Γ : Context} {A B : Term}
    (hA : HasType Γ A .univ) (hAB : TypeEq Γ A B) :
    TermEq Γ A B .univ :=
  inverseUnivEq' (.inl (noU hA)) hAB

/-!
## Uniqueness of Neutral Types (`Definition/Typed/Consequences/NeTypeEq.agda`)
-/

/-- The same variable index in a context has a unique lookup type (`varTypeEq′`). -/
theorem varTypeEq' {Γ : Context} {n : Nat} {R T : Term}
    (hR : Member n R Γ) (hT : Member n T Γ) : R = T := by
  induction hR generalizing T with
  | here =>
      cases hT with
      | here => rfl
  | there hR' ih =>
      cases hT with
      | there hT' =>
          rw [ih hT']

/-- The same variable in a context has judgmentally equal types (`varTypeEq`). -/
theorem varTypeEq {Γ : Context} {x : Nat} {A B : Term}
    (hA : TypeWf Γ A) (_hB : TypeWf Γ B)
    (hxA : Member x A Γ) (hxB : Member x B Γ) : TypeEq Γ A B := by
  rw [← varTypeEq' hxA hxB]
  exact .refl hA

/-- Any neutral term has a unique type up to judgmental type equality (`neTypeEq`). -/
theorem neTypeEq {Γ : Context} {t A B : Term}
    (neT : Neutral t) (htA : HasType Γ t A) (htB : HasType Γ t B) :
    TypeEq Γ A B := by
  induction neT generalizing A B with
  | var x =>
      rcases inversion_var htA with ⟨A₀, hxA₀, hAA₀⟩
      rcases inversion_var htB with ⟨B₀, hxB₀, hBB₀⟩
      have hEq := varTypeEq' hxA₀ hxB₀
      subst hEq
      exact .trans hAA₀ (.symm hBB₀)
  | app neF ih =>
      rcases inversion_app htA with ⟨F₁, G₁, hf₁, ha₁, hAG₁⟩
      rcases inversion_app htB with ⟨F₂, G₂, hf₂, _ha₂, hBG₂⟩
      have hPiEq : TypeEq Γ (.pi F₁ G₁) (.pi F₂ G₂) := ih hf₁ hf₂
      have ⟨_, hG₁G₂⟩ := injectivity hPiEq
      exact .trans hAG₁ (.trans (substTypeEq hG₁G₂ (.refl ha₁)) (.symm hBG₂))
  | natrec _ =>
      rcases inversion_natrec htA with ⟨_, _, _, _, hAFn⟩
      rcases inversion_natrec htB with ⟨_, _, _, _, hBFn⟩
      exact .trans hAFn (.symm hBFn)

/-!
## Congruence of `recStepType` (`Definition/Typed/Consequences/SucCong.agda`)
-/

/-- Congruence of the successor step type in `natrec` (`sucCong`). -/
theorem sucCong {Γ : Context} {F G : Term}
    (hFG : TypeEq (.nat :: Γ) F G) :
    TypeEq Γ (recStepType F) (recStepType G) := by
  have wfΓNat : CtxWf (.nat :: Γ) := wfTypeEq hFG
  cases wfΓNat with
  | cons wfΓ wfNat =>
      have ⟨wfF, _⟩ := syntacticEq hFG
      have hSucVar0 : HasType (.nat :: Γ) (.succ (.var 0)) (wk1 .nat) :=
        .succ (.var (.cons wfΓ wfNat) (Member.here (A := .nat)))
      exact .pi wfNat (.refl wfNat)
        (.pi wfF hFG
          (wkTypeEq (.step .id) (.cons (.cons wfΓ wfNat) wfF)
            (substUpTypeEq hFG (.refl hSucVar0))))

/-!
## Weak-Head Normalization (`Definition/Typed/Consequences/Reduction.agda`, Theorem 3.28)
-/

/-- Every reducible type reduces to a weak-head normal form (`whNorm′`). -/
theorem whNorm' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (pA : RedType eqrel l Γ A) :
    ∃ B, Whnf B ∧ TypeStarWf Γ A B := by
  rcases pA with ⟨rel, hAt⟩
  cases logRelShape_of_LogRelAt hAt with
  | U hU => exact ⟨.univ, .univ, idRedWf (.univ hU.wf)⟩
  | nat D => exact ⟨.nat, .nat, D⟩
  | ne neA => exact ⟨_, .neutral neA.neK, neA.D⟩
  | pi D _ _ _ _ _ _ _ _ _ _ => exact ⟨_, .pi, D⟩

/-- Every well-formed type reduces to a weak-head normal form (`whNorm`, Theorem 3.28). -/
theorem whNorm {Γ : Context} {A : Term} (hA : TypeWf Γ A) :
    ∃ B, Whnf B ∧ TypeStarWf Γ A B :=
  whNorm' (reducible (eqrel := synEqRel) hA)

/-- Every reducible term reduces to a weak-head normal form (`whNormTerm′`). -/
theorem whNormTerm' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A a : Term}
    (pA : RedType eqrel l Γ A) (ha : RedTerm pA a) :
    ∃ b, Whnf b ∧ StarWf Γ a b A := by
  rcases ha with ⟨rel, hAt, ha⟩
  cases logRelShape_of_LogRelAt hAt with
  | U _ =>
      rcases ha with ⟨b, d, typeB, _, _⟩
      exact ⟨b, typeB.toWhnf, d⟩
  | nat D =>
      rcases ha with ⟨_, n, d, _, prop⟩
      exact ⟨n, (natural_of_NaturalProp prop).toWhnf,
        convStarWf d (.symm (subsetStar D.reduction))⟩
  | ne neA =>
      rcases ha with ⟨k, d, nf⟩
      exact ⟨k, .neutral nf.neK,
        convStarWf d (.symm (subsetStar neA.D.reduction))⟩
  | pi D _ _ _ _ _ _ _ _ _ _ =>
      rcases ha with ⟨f, d, funcF, _, _, _⟩
      exact ⟨f, funcF.toWhnf,
        convStarWf d (.symm (subsetStar D.reduction))⟩

/-- Every well-formed term reduces to a weak-head normal form (`whNormTerm`, Theorem 3.28). -/
theorem whNormTerm {Γ : Context} {a A : Term} (ha : HasType Γ a A) :
    ∃ b, Whnf b ∧ StarWf Γ a b A := by
  rcases reducibleTerm (eqrel := synEqRel) ha with ⟨pA, pa⟩
  exact whNormTerm' pA pa

/-!
## Canonicity (`Definition/Typed/Consequences/Canonicity.agda`, Theorem 3.31)
-/

/-- Numeral representation `sucᵏ k` of a natural number `k` (`sucᵏ`). -/
def suck : Nat → Term
  | 0 => .zero
  | n + 1 => .succ (suck n)

/-- Canonicity helper on `RedNatTerm` in the empty context (`canonicity′` / `canonicity″`). -/
theorem canonicity' {t : Term} (ht : RedNatTerm synEqRel [] t) :
    ∃ k, TermEq [] t (suck k) .nat :=
  @RedNatTerm.rec synEqRel []
    (fun t _ ↦ ∃ k, TermEq [] t (suck k) .nat)
    (fun n _ ↦ ∃ k, TermEq [] n (suck k) .nat)
    (fun _ _ d _ _ ih ↦ by
      rcases ih with ⟨k, hk⟩
      exact ⟨k, .trans (subsetStarTerm d.reduction) hk⟩)
    (fun _ ih ↦ by
      rcases ih with ⟨k, hk⟩
      exact ⟨k + 1, .succ hk⟩)
    ⟨0, .refl (.zero .nil)⟩
    (fun nf ↦ False.elim (noNe nf.hk nf.neK))
    t ht

/-- Canonicity for closed terms of type `ℕ` (`canonicity`, Theorem 3.31). -/
theorem canonicity {t : Term} (ht : HasType [] t .nat) :
    ∃ k, TermEq [] t (suck k) .nat := by
  rcases reducibleTerm (eqrel := synEqRel) ht with ⟨pNat, pt⟩
  have hAt : LogRelAt synEqRel .one [] .nat (RedNatRel synEqRel []) := .nat (elimNat pNat)
  exact canonicity' ((RedTerm_of_LogRelAt hAt pNat).mp pt)

/-!
## Consistency (`Definition/Typed/Consequences/Consistency.agda`, Theorem 3.35)
-/

/-- `zero` is not judgmentally equal to `suc n` in any context. -/
theorem zero_ne_succ {Γ : Context} {n : Term} :
    ¬ TermEq Γ .zero (.succ n) .nat := by
  intro h
  rcases reducibleEqTerm (eqrel := synEqRel) h with ⟨pNat, htu⟩
  have hAt : LogRelAt synEqRel .one Γ .nat (RedNatRel synEqRel Γ) := .nat (elimNat pNat)
  rcases (RedTermEq_of_LogRelAt hAt pNat).mp htu with ⟨_, _, k, k', d, d', _, prop⟩
  have hk : .zero = k := whnfRedStarTerm d.reduction .zero
  have hk' : .succ n = k' := whnfRedStarTerm d'.reduction .succ
  subst hk hk'
  cases prop with
  | ne nf => cases nf.neK

/-- Consistency: `zero` and `suc zero` are not judgmentally equal (`zero≢one`, Theorem 3.35). -/
theorem zero_ne_one : ¬ TermEq [] .zero (.succ .zero) .nat :=
  zero_ne_succ

end LogrelMLTT
