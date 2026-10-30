/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Typed.agda. Judgments express inhabitation of the source derivation types.
Contexts are newest-first lists rather than snoc lists. This definition layer makes no
claim to reproduce the source's metatheoretic absence of K in Lean's own metatheory.
-/
import Abel2018.Syntax

namespace Abel2018

/-- Variable lookup includes the source's shifts across every context extension. -/
inductive Member : Nat → Term → Context → Prop where
  | here {Γ A} : Member 0 (wk1 A) (A :: Γ)
  | there {Γ A B x} : Member x A Γ → Member (x + 1) (wk1 A) (B :: Γ)

mutual
  inductive CtxWf : Context → Prop where
    | nil : CtxWf []
    | cons {Γ A} : CtxWf Γ → TypeWf Γ A → CtxWf (A :: Γ)

  inductive TypeWf : Context → Term → Prop where
    | nat {Γ} : CtxWf Γ → TypeWf Γ .nat
    | univ {Γ} : CtxWf Γ → TypeWf Γ .univ
    | pi {Γ F G} : TypeWf Γ F → TypeWf (F :: Γ) G → TypeWf Γ (.pi F G)
    | fromUniv {Γ A} : HasType Γ A .univ → TypeWf Γ A

  inductive HasType : Context → Term → Term → Prop where
    | nat {Γ} : CtxWf Γ → HasType Γ .nat .univ
    | pi {Γ F G} : HasType Γ F .univ → HasType (F :: Γ) G .univ →
        HasType Γ (.pi F G) .univ
    | var {Γ A x} : CtxWf Γ → Member x A Γ → HasType Γ (.var x) A
    | lam {Γ F G t} : TypeWf Γ F → HasType (F :: Γ) t G →
        HasType Γ (.lam t) (.pi F G)
    | app {Γ g a F G} : HasType Γ g (.pi F G) → HasType Γ a F →
        HasType Γ (.app g a) (subst0 G a)
    | zero {Γ} : CtxWf Γ → HasType Γ .zero .nat
    | succ {Γ n} : HasType Γ n .nat → HasType Γ (.succ n) .nat
    | natrec {Γ G s z n} : TypeWf (.nat :: Γ) G → HasType Γ z (subst0 G .zero) →
        HasType Γ s (recStepType G) → HasType Γ n .nat →
        HasType Γ (.natrec G z s n) (subst0 G n)
    | conv {Γ t A B} : HasType Γ t A → TypeEq Γ A B → HasType Γ t B

  inductive TypeEq : Context → Term → Term → Prop where
    | fromUniv {Γ A B} : TermEq Γ A B .univ → TypeEq Γ A B
    | refl {Γ A} : TypeWf Γ A → TypeEq Γ A A
    | symm {Γ A B} : TypeEq Γ A B → TypeEq Γ B A
    | trans {Γ A B C} : TypeEq Γ A B → TypeEq Γ B C → TypeEq Γ A C
    | pi {Γ F H G E} : TypeWf Γ F → TypeEq Γ F H → TypeEq (F :: Γ) G E →
        TypeEq Γ (.pi F G) (.pi H E)

  inductive TermEq : Context → Term → Term → Term → Prop where
    | refl {Γ t A} : HasType Γ t A → TermEq Γ t t A
    | symm {Γ t u A} : TermEq Γ t u A → TermEq Γ u t A
    | trans {Γ t u r A} : TermEq Γ t u A → TermEq Γ u r A → TermEq Γ t r A
    | conv {Γ A B t u} : TermEq Γ t u A → TypeEq Γ A B → TermEq Γ t u B
    | pi {Γ E F G H} : TypeWf Γ F → TermEq Γ F H .univ →
        TermEq (F :: Γ) G E .univ → TermEq Γ (.pi F G) (.pi H E) .univ
    | app {Γ a b f g F G} : TermEq Γ f g (.pi F G) → TermEq Γ a b F →
        TermEq Γ (.app f a) (.app g b) (subst0 G a)
    | beta {Γ a t F G} : TypeWf Γ F → HasType (F :: Γ) t G → HasType Γ a F →
        TermEq Γ (.app (.lam t) a) (subst0 t a) (subst0 G a)
    | eta {Γ f g F G} : TypeWf Γ F → HasType Γ f (.pi F G) →
        HasType Γ g (.pi F G) →
        TermEq (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G →
        TermEq Γ f g (.pi F G)
    | succ {Γ m n} : TermEq Γ m n .nat → TermEq Γ (.succ m) (.succ n) .nat
    | natrec {Γ z z' s s' n n' F F'} : TypeEq (.nat :: Γ) F F' →
        TermEq Γ z z' (subst0 F .zero) → TermEq Γ s s' (recStepType F) →
        TermEq Γ n n' .nat →
        TermEq Γ (.natrec F z s n) (.natrec F' z' s' n') (subst0 F n)
    | natrecZero {Γ z s F} : TypeWf (.nat :: Γ) F → HasType Γ z (subst0 F .zero) →
        HasType Γ s (recStepType F) →
        TermEq Γ (.natrec F z s .zero) z (subst0 F .zero)
    | natrecSucc {Γ n z s F} : HasType Γ n .nat → TypeWf (.nat :: Γ) F →
        HasType Γ z (subst0 F .zero) → HasType Γ s (recStepType F) →
        TermEq Γ (.natrec F z s (.succ n)) (.app (.app s n) (.natrec F z s n))
          (subst0 F (.succ n))
end

/-- Typed weak-head reduction; in particular there is no reduction under a lambda or successor. -/
inductive Step (Γ : Context) : Term → Term → Term → Prop where
  | conv {A B t u} : Step Γ t u A → TypeEq Γ A B → Step Γ t u B
  | app {A B t u a} : Step Γ t u (.pi A B) → HasType Γ a A →
      Step Γ (.app t a) (.app u a) (subst0 B a)
  | beta {A B a t} : TypeWf Γ A → HasType (A :: Γ) t B → HasType Γ a A →
      Step Γ (.app (.lam t) a) (subst0 t a) (subst0 B a)
  | natrec {z s n n' F} : TypeWf (.nat :: Γ) F → HasType Γ z (subst0 F .zero) →
      HasType Γ s (recStepType F) → Step Γ n n' .nat →
      Step Γ (.natrec F z s n) (.natrec F z s n') (subst0 F n)
  | natrecZero {z s F} : TypeWf (.nat :: Γ) F → HasType Γ z (subst0 F .zero) →
      HasType Γ s (recStepType F) → Step Γ (.natrec F z s .zero) z (subst0 F .zero)
  | natrecSucc {n z s F} : HasType Γ n .nat → TypeWf (.nat :: Γ) F →
      HasType Γ z (subst0 F .zero) → HasType Γ s (recStepType F) →
      Step Γ (.natrec F z s (.succ n)) (.app (.app s n) (.natrec F z s n))
        (subst0 F (.succ n))

inductive TypeStep (Γ : Context) : Term → Term → Prop where
  | fromUniv {A B} : Step Γ A B .univ → TypeStep Γ A B

/-- Source reflexive-transitive closure, whose reflexive case requires a typing derivation. -/
inductive Star (Γ : Context) : Term → Term → Term → Prop where
  | refl {A t} : HasType Γ t A → Star Γ t t A
  | step {A t t' u} : Step Γ t t' A → Star Γ t' u A → Star Γ t u A

inductive TypeStar (Γ : Context) : Term → Term → Prop where
  | refl {A} : TypeWf Γ A → TypeStar Γ A A
  | step {A A' B} : TypeStep Γ A A' → TypeStar Γ A' B → TypeStar Γ A B

def TypeWhnf (Γ : Context) (A B : Term) : Prop := TypeStar Γ A B ∧ Whnf B

def TermWhnf (Γ : Context) (t u A : Term) : Prop := Star Γ t u A ∧ Whnf u

/-- The source's type equality bundled with well-formed endpoints. -/
def TypeEqWf (Γ : Context) (A B : Term) : Prop :=
  TypeWf Γ A ∧ TypeWf Γ B ∧ TypeEq Γ A B

/-- The source's term equality bundled with well-typed endpoints. -/
def TermEqWf (Γ : Context) (t u A : Term) : Prop :=
  HasType Γ t A ∧ HasType Γ u A ∧ TermEq Γ t u A

structure TypeStarWf (Γ : Context) (A B : Term) : Prop where
  source : TypeWf Γ A
  target : TypeWf Γ B
  reduction : TypeStar Γ A B

structure StarWf (Γ : Context) (t u A : Term) : Prop where
  source : HasType Γ t A
  target : HasType Γ u A
  reduction : Star Γ t u A

/-- The source's substitution judgment; it does not assert ambient context validity. -/
inductive SubstWf (Δ : Context) : Subst → Context → Prop where
  | nil {σ} : SubstWf Δ σ []
  | cons {Γ A σ} : SubstWf Δ (tailSubst σ) Γ →
      HasType Δ (headSubst σ) (subst (tailSubst σ) A) → SubstWf Δ σ (A :: Γ)

inductive SubstEq (Δ : Context) : Subst → Subst → Context → Prop where
  | nil {σ σ'} : SubstEq Δ σ σ' []
  | cons {Γ A σ σ'} : SubstEq Δ (tailSubst σ) (tailSubst σ') Γ →
      TermEq Δ (headSubst σ) (headSubst σ') (subst (tailSubst σ) A) →
      SubstEq Δ σ σ' (A :: Γ)

end Abel2018
