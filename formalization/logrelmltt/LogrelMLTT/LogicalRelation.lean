/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/LogicalRelation.agda, Definition/LogicalRelation/ShapeView.agda,
Definition/LogicalRelation/Irrelevance.agda,
Definition/LogicalRelation/Properties/Escape.agda,
Definition/LogicalRelation/Properties/Reflexivity.agda,
Definition/LogicalRelation/Properties/MaybeEmb.agda.
The Σ, Unit and Empty cases follow mr-ohman/logrel-mltt master, commit
9d6e290064962a1987c9e1a131c2fb967d6ef928 (same files). As in the rest of this port, the
logical relation is a Prop-valued indexed inductive that carries the decoded relations
(`RedRel`) as an index; Σ reuses the Π encoding of domain/codomain families.
-/
import LogrelMLTT.TypedProperties

namespace LogrelMLTT

/-!
## Reducibility of Neutrals (`Definition/LogicalRelation.agda` lines 22–80)
-/

/-- Reducible neutral type with explicit WHNF `K` (`Γ ⊩ne A`). -/
structure RedNeAt (eqrel : EqRelSet) (Γ : Context) (A K : Term) : Prop where
  D : TypeStarWf Γ A K
  neK : Neutral K
  KeqK : eqrel.NeEqRel Γ K K .univ

/-- Reducible neutral type (`Γ ⊩ne A`). -/
inductive RedNe (eqrel : EqRelSet) (Γ : Context) (A : Term) : Prop where
  | mk (K : Term) (D : TypeStarWf Γ A K) (neK : Neutral K) (KeqK : eqrel.NeEqRel Γ K K .univ)

/-- Reducible neutral type equality (`Γ ⊩ne A ≡ B / [A]`). -/
inductive RedNeEq (eqrel : EqRelSet) (Γ : Context) (K B : Term) : Prop where
  | mk (M : Term) (D' : TypeStarWf Γ B M) (neM : Neutral M) (KeqM : eqrel.NeEqRel Γ K M .univ)

/-- Reducible neutral term in WHNF (`Γ ⊩neNf k ∷ A`). -/
structure RedNeNf (eqrel : EqRelSet) (Γ : Context) (k A : Term) : Prop where
  neK : Neutral k
  hk : HasType Γ k A
  keqk : eqrel.NeEqRel Γ k k A

/-- Reducible neutral term (`Γ ⊩ne t ∷ A / [A]`). -/
inductive RedNeTerm (eqrel : EqRelSet) (Γ : Context) (K t : Term) : Prop where
  | mk (k : Term) (d : StarWf Γ t k K) (nf : RedNeNf eqrel Γ k K)

/-- Reducible neutral term equality in WHNF (`Γ ⊩neNf k ≡ m ∷ A`). -/
structure RedNeNfEq (eqrel : EqRelSet) (Γ : Context) (k m A : Term) : Prop where
  neK : Neutral k
  neM : Neutral m
  keqm : eqrel.NeEqRel Γ k m A

/-- Reducible neutral term equality (`Γ ⊩ne t ≡ u ∷ A / [A]`). -/
inductive RedNeTermEq (eqrel : EqRelSet) (Γ : Context) (K t u : Term) : Prop where
  | mk (k m : Term) (d : StarWf Γ t k K) (d' : StarWf Γ u m K) (nf : RedNeNfEq eqrel Γ k m K)

/-!
## Reducibility of Natural Numbers (`Definition/LogicalRelation.agda` lines 81–128)
-/

/-- Reducible natural number type (`Γ ⊩ℕ A`). -/
abbrev RedNat (Γ : Context) (A : Term) : Prop :=
  TypeStarWf Γ A .nat

/-- Reducible natural number type equality (`Γ ⊩ℕ A ≡ B`). -/
abbrev RedNatEq (Γ : Context) (B : Term) : Prop :=
  TypeStar Γ B .nat

mutual
  /-- Reducible natural number term (`Γ ⊩ℕ t ∷ℕ`). -/
  inductive RedNatTerm (eqrel : EqRelSet) (Γ : Context) : Term → Prop where
    | mk (t n : Term)
        (d : StarWf Γ t n .nat)
        (neqn : eqrel.TermEqRel Γ n n .nat)
        (prop : NaturalProp eqrel Γ n) :
        RedNatTerm eqrel Γ t

  /-- WHNF property of reducible natural number terms (`Natural-prop`). -/
  inductive NaturalProp (eqrel : EqRelSet) (Γ : Context) : Term → Prop where
    | suc {n : Term} : RedNatTerm eqrel Γ n → NaturalProp eqrel Γ (.succ n)
    | zero : NaturalProp eqrel Γ .zero
    | ne {n : Term} : RedNeNf eqrel Γ n .nat → NaturalProp eqrel Γ n
end

mutual
  /-- Reducible natural number term equality (`Γ ⊩ℕ t ≡ u ∷ℕ`). -/
  inductive RedNatTermEq (eqrel : EqRelSet) (Γ : Context) : Term → Term → Prop where
    | mk (t u k k' : Term)
        (d : StarWf Γ t k .nat)
        (d' : StarWf Γ u k' .nat)
        (keqk' : eqrel.TermEqRel Γ k k' .nat)
        (prop : NaturalEqProp eqrel Γ k k') :
        RedNatTermEq eqrel Γ t u

  /-- WHNF property of reducible natural number term equality (`[Natural]-prop`). -/
  inductive NaturalEqProp (eqrel : EqRelSet) (Γ : Context) : Term → Term → Prop where
    | suc {n n' : Term} : RedNatTermEq eqrel Γ n n' → NaturalEqProp eqrel Γ (.succ n) (.succ n')
    | zero : NaturalEqProp eqrel Γ .zero .zero
    | ne {n n' : Term} : RedNeNfEq eqrel Γ n n' .nat → NaturalEqProp eqrel Γ n n'
end

/-- Extraction of `NaturalView` from `NaturalProp` (`natural`). -/
theorem natural_of_NaturalProp {eqrel : EqRelSet} {Γ : Context} {n : Term} :
    NaturalProp eqrel Γ n → NaturalView n
  | .suc _ => .succ
  | .zero => .zero
  | .ne nf => .neutral nf.neK

/-- Extraction of `NaturalView` pair from `NaturalEqProp` (`split`). -/
theorem split_of_NaturalEqProp {eqrel : EqRelSet} {Γ : Context} {a b : Term} :
    NaturalEqProp eqrel Γ a b → NaturalView a ∧ NaturalView b
  | .suc _ => ⟨.succ, .succ⟩
  | .zero => ⟨.zero, .zero⟩
  | .ne nf => ⟨.neutral nf.neK, .neutral nf.neM⟩

/-!
## Reducibility of Empty and Unit (logrel-mltt master `Definition/LogicalRelation.agda`)
-/

/-- Reducible empty type (`Γ ⊩Empty A`). -/
abbrev RedEmpty (Γ : Context) (A : Term) : Prop :=
  TypeStarWf Γ A .empty

/-- Reducible empty type equality (`Γ ⊩Empty A ≡ B`). -/
abbrev RedEmptyEq (Γ : Context) (B : Term) : Prop :=
  TypeStar Γ B .empty

/-- Reducible term of the empty type (`Γ ⊩Empty t ∷Empty`). The source's `Empty-prop` has the
single constructor `ne`, so its content is inlined as `RedNeNf`. -/
inductive RedEmptyTerm (eqrel : EqRelSet) (Γ : Context) (t : Term) : Prop where
  | mk (n : Term) (d : StarWf Γ t n .empty) (neqn : eqrel.TermEqRel Γ n n .empty)
      (prop : RedNeNf eqrel Γ n .empty)

/-- Reducible term equality of the empty type (`Γ ⊩Empty t ≡ u ∷Empty`); `[Empty]-prop` is
inlined as `RedNeNfEq`. -/
inductive RedEmptyTermEq (eqrel : EqRelSet) (Γ : Context) (t u : Term) : Prop where
  | mk (k k' : Term) (d : StarWf Γ t k .empty) (d' : StarWf Γ u k' .empty)
      (keqk' : eqrel.TermEqRel Γ k k' .empty) (prop : RedNeNfEq eqrel Γ k k' .empty)

/-- Reducible unit type (`Γ ⊩Unit A`). -/
abbrev RedUnit (Γ : Context) (A : Term) : Prop :=
  TypeStarWf Γ A .unit

/-- Reducible unit type equality (`Γ ⊩Unit A ≡ B`). -/
abbrev RedUnitEq (Γ : Context) (B : Term) : Prop :=
  TypeStar Γ B .unit

/-- Reducible term of the unit type (`Γ ⊩Unit t ∷Unit`). -/
inductive RedUnitTerm (Γ : Context) (t : Term) : Prop where
  | mk (n : Term) (d : StarWf Γ t n .unit) (prop : Whnf n)

/-- Reducible term equality of the unit type (`Γ ⊩Unit t ≡ u ∷Unit`): by η, any two
well-typed terms of the unit type are equal. -/
structure RedUnitTermEq (Γ : Context) (t u : Term) : Prop where
  ht : HasType Γ t .unit
  hu : HasType Γ u .unit

/-!
## Type Levels and Logical Relation Bundle (`Definition/LogicalRelation.agda` lines 130–349)
-/

/-- Universe levels `⁰` and `¹`. -/
inductive TypeLevel where
  | zero
  | one
  deriving DecidableEq, Repr

/-- Strict ordering `⁰ < ¹` on `TypeLevel`. -/
inductive TypeLevelLT : TypeLevel → TypeLevel → Prop where
  | zeroLT : TypeLevelLT .zero .one

/-- Bundle of decoded relations for a reducible type:
type equality (`eqType`), term reducibility (`hasTerm`), and term equality (`eqTerm`). -/
structure RedRel : Type 1 where
  eqType : Term → Prop
  hasTerm : Term → Prop
  eqTerm : Term → Term → Prop

/-- Reducible universe type with explicit lower level `l'` (`Γ ⊩¹U`). -/
structure RedUAt (l' l : TypeLevel) (Γ : Context) : Prop where
  lt : TypeLevelLT l' l
  wf : CtxWf Γ

/-- Reducible universe type (`Γ ⊩¹U`). -/
inductive RedU (l : TypeLevel) (Γ : Context) : Prop where
  | mk (l' : TypeLevel) (lt : TypeLevelLT l' l) (wf : CtxWf Γ)

/-- Reducible term of universe type (`Γ ⊩¹U t ∷U/ l<`). -/
inductive RedUTerm (eqrel : EqRelSet) (rec : Context → Term → RedRel → Prop)
    (Γ : Context) (t : Term) : Prop where
  | mk (A : Term)
      (d : StarWf Γ t A .univ)
      (typeA : SmallTypeView A)
      (AeqA : eqrel.TermEqRel Γ A A .univ)
      (ht : ∃ rel, rec Γ t rel)

/-- Reducible term equality of universe type (`Γ ⊩¹U t ≡ u ∷U/ l<`). -/
inductive RedUTermEq (eqrel : EqRelSet) (rec : Context → Term → RedRel → Prop)
    (Γ : Context) (t u : Term) : Prop where
  | mk (A B : Term)
      (d : StarWf Γ t A .univ)
      (d' : StarWf Γ u B .univ)
      (typeA : SmallTypeView A)
      (typeB : SmallTypeView B)
      (AeqB : eqrel.TermEqRel Γ A B .univ)
      (relt : RedRel)
      (ht : rec Γ t relt)
      (hu : ∃ relu, rec Γ u relu)
      (tequ : relt.eqType u)

/-- Relation bundle for `U`. -/
def RedURel (eqrel : EqRelSet) (rec : Context → Term → RedRel → Prop) (Γ : Context) : RedRel where
  eqType B := B = .univ
  hasTerm t := RedUTerm eqrel rec Γ t
  eqTerm t u := RedUTermEq eqrel rec Γ t u

/-- Relation bundle for `ℕ`. -/
def RedNatRel (eqrel : EqRelSet) (Γ : Context) : RedRel where
  eqType B := RedNatEq Γ B
  hasTerm t := RedNatTerm eqrel Γ t
  eqTerm t u := RedNatTermEq eqrel Γ t u

/-- Relation bundle for neutral types. -/
def RedNeRel (eqrel : EqRelSet) (Γ : Context) (K : Term) : RedRel where
  eqType B := RedNeEq eqrel Γ K B
  hasTerm t := RedNeTerm eqrel Γ K t
  eqTerm t u := RedNeTermEq eqrel Γ K t u

/-- Relation bundle for `Empty`. -/
def RedEmptyRel (eqrel : EqRelSet) (Γ : Context) : RedRel where
  eqType B := RedEmptyEq Γ B
  hasTerm t := RedEmptyTerm eqrel Γ t
  eqTerm t u := RedEmptyTermEq eqrel Γ t u

/-- Relation bundle for `Unit`. -/
def RedUnitRel (Γ : Context) : RedRel where
  eqType B := RedUnitEq Γ B
  hasTerm t := RedUnitTerm Γ t
  eqTerm t u := RedUnitTermEq Γ t u

/-- Helper predicates for domain and codomain relation families in `Π` and `Σ`. -/
abbrev RelFEqType (relF : Wk → Context → RedRel → Prop) (ρ : Wk) (Δ : Context) (B : Term) : Prop :=
  ∃ rel, relF ρ Δ rel ∧ rel.eqType B

abbrev RelFHasTerm (relF : Wk → Context → RedRel → Prop) (ρ : Wk) (Δ : Context) (a : Term) : Prop :=
  ∃ rel, relF ρ Δ rel ∧ rel.hasTerm a

abbrev RelFEqTerm (relF : Wk → Context → RedRel → Prop) (ρ : Wk) (Δ : Context) (a b : Term) : Prop :=
  ∃ rel, relF ρ Δ rel ∧ rel.eqTerm a b

abbrev RelGEqType (relG : Wk → Context → Term → RedRel → Prop)
    (ρ : Wk) (Δ : Context) (a B : Term) : Prop :=
  ∃ rel, relG ρ Δ a rel ∧ rel.eqType B

abbrev RelGHasTerm (relG : Wk → Context → Term → RedRel → Prop)
    (ρ : Wk) (Δ : Context) (a t : Term) : Prop :=
  ∃ rel, relG ρ Δ a rel ∧ rel.hasTerm t

abbrev RelGEqTerm (relG : Wk → Context → Term → RedRel → Prop)
    (ρ : Wk) (Δ : Context) (a t u : Term) : Prop :=
  ∃ rel, relG ρ Δ a rel ∧ rel.eqTerm t u

/-- Reducible `Π`-type equality (`Γ ⊩¹Π A ≡ B / [A]`). -/
inductive RedPiEq (eqrel : EqRelSet) (Γ : Context) (F G : Term)
    (relF : Wk → Context → RedRel → Prop)
    (relG : Wk → Context → Term → RedRel → Prop)
    (B : Term) : Prop where
  | mk (F' G' : Term)
      (D' : TypeStar Γ B (.pi F' G'))
      (AeqB : eqrel.TypeEqRel Γ (.pi F G) (.pi F' G'))
      (FeqF' : ∀ {ρ Δ}, WkCtx ρ Δ Γ → CtxWf Δ → RelFEqType relF ρ Δ (wk ρ F'))
      (GeqG' : ∀ {ρ Δ a}, WkCtx ρ Δ Γ → CtxWf Δ → RelFHasTerm relF ρ Δ a →
        RelGEqType relG ρ Δ a (subst0 (wk (.lift ρ) G') a))

/-- Reducible term of `Π`-type (`Γ ⊩¹Π t ∷ A / [A]`). -/
inductive RedPiTerm (eqrel : EqRelSet) (Γ : Context) (F G : Term)
    (relF : Wk → Context → RedRel → Prop)
    (relG : Wk → Context → Term → RedRel → Prop)
    (t : Term) : Prop where
  | mk (f : Term)
      (d : StarWf Γ t f (.pi F G))
      (funcF : FunctionView f)
      (feqf : eqrel.TermEqRel Γ f f (.pi F G))
      (appEq : ∀ {ρ Δ a b}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a →
        RelFHasTerm relF ρ Δ b →
        RelFEqTerm relF ρ Δ a b →
        RelGEqTerm relG ρ Δ a (.app (wk ρ f) a) (.app (wk ρ f) b))
      (appTerm : ∀ {ρ Δ a}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a →
        RelGHasTerm relG ρ Δ a (.app (wk ρ f) a))

/-- Reducible term equality of `Π`-type (`Γ ⊩¹Π t ≡ u ∷ A / [A]`). -/
inductive RedPiTermEq (eqrel : EqRelSet) (Γ : Context) (F G : Term)
    (relF : Wk → Context → RedRel → Prop)
    (relG : Wk → Context → Term → RedRel → Prop)
    (t u : Term) : Prop where
  | mk (f g : Term)
      (d : StarWf Γ t f (.pi F G))
      (d' : StarWf Γ u g (.pi F G))
      (funcF : FunctionView f)
      (funcG : FunctionView g)
      (feqg : eqrel.TermEqRel Γ f g (.pi F G))
      (ht : RedPiTerm eqrel Γ F G relF relG t)
      (hu : RedPiTerm eqrel Γ F G relF relG u)
      (appEq : ∀ {ρ Δ a}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a →
        RelGEqTerm relG ρ Δ a (.app (wk ρ f) a) (.app (wk ρ g) a))

/-- Relation bundle for `Π`-types. -/
def RedPiRel (eqrel : EqRelSet) (Γ : Context) (F G : Term)
    (relF : Wk → Context → RedRel → Prop)
    (relG : Wk → Context → Term → RedRel → Prop) : RedRel where
  eqType B := RedPiEq eqrel Γ F G relF relG B
  hasTerm t := RedPiTerm eqrel Γ F G relF relG t
  eqTerm t u := RedPiTermEq eqrel Γ F G relF relG t u

/-- Reducible `Σ`-type equality (`Γ ⊩¹Σ A ≡ B / [A]`). -/
inductive RedSigmaEq (eqrel : EqRelSet) (Γ : Context) (F G : Term)
    (relF : Wk → Context → RedRel → Prop)
    (relG : Wk → Context → Term → RedRel → Prop)
    (B : Term) : Prop where
  | mk (F' G' : Term)
      (D' : TypeStar Γ B (.sigma F' G'))
      (AeqB : eqrel.TypeEqRel Γ (.sigma F G) (.sigma F' G'))
      (FeqF' : ∀ {ρ Δ}, WkCtx ρ Δ Γ → CtxWf Δ → RelFEqType relF ρ Δ (wk ρ F'))
      (GeqG' : ∀ {ρ Δ a}, WkCtx ρ Δ Γ → CtxWf Δ → RelFHasTerm relF ρ Δ a →
        RelGEqType relG ρ Δ a (subst0 (wk (.lift ρ) G') a))

/-- Reducible term of `Σ`-type (`Γ ⊩¹Σ t ∷ A / [A]`, logrel-mltt master): the weak-head normal
form `p` is a product (pair or neutral), and its projections are reducible at the identity
weakening. -/
inductive RedSigmaTerm (eqrel : EqRelSet) (Γ : Context) (F G : Term)
    (relF : Wk → Context → RedRel → Prop)
    (relG : Wk → Context → Term → RedRel → Prop)
    (t : Term) : Prop where
  | mk (p : Term)
      (d : StarWf Γ t p (.sigma F G))
      (prodP : ProductView p)
      (peqp : eqrel.TermEqRel Γ p p (.sigma F G))
      (fstTerm : RelFHasTerm relF .id Γ (.fst p))
      (sndTerm : RelGHasTerm relG .id Γ (.fst p) (.snd p))

/-- Reducible term equality of `Σ`-type (`Γ ⊩¹Σ t ≡ u ∷ A / [A]`, logrel-mltt master). -/
inductive RedSigmaTermEq (eqrel : EqRelSet) (Γ : Context) (F G : Term)
    (relF : Wk → Context → RedRel → Prop)
    (relG : Wk → Context → Term → RedRel → Prop)
    (t u : Term) : Prop where
  | mk (p r : Term)
      (d : StarWf Γ t p (.sigma F G))
      (d' : StarWf Γ u r (.sigma F G))
      (prodP : ProductView p)
      (prodR : ProductView r)
      (peqr : eqrel.TermEqRel Γ p r (.sigma F G))
      (ht : RedSigmaTerm eqrel Γ F G relF relG t)
      (hu : RedSigmaTerm eqrel Γ F G relF relG u)
      (fstP : RelFHasTerm relF .id Γ (.fst p))
      (fstR : RelFHasTerm relF .id Γ (.fst r))
      (fstEq : RelFEqTerm relF .id Γ (.fst p) (.fst r))
      (sndEq : RelGEqTerm relG .id Γ (.fst p) (.snd p) (.snd r))

/-- Relation bundle for `Σ`-types. -/
def RedSigmaRel (eqrel : EqRelSet) (Γ : Context) (F G : Term)
    (relF : Wk → Context → RedRel → Prop)
    (relG : Wk → Context → Term → RedRel → Prop) : RedRel where
  eqType B := RedSigmaEq eqrel Γ F G relF relG B
  hasTerm t := RedSigmaTerm eqrel Γ F G relF relG t
  eqTerm t u := RedSigmaTermEq eqrel Γ F G relF relG t u

/-- One level of the logical relation (`LogRel` in `Definition/LogicalRelation.agda`),
parameterized by the lower-level relation `rec`. -/
inductive LogRel (eqrel : EqRelSet) (l : TypeLevel)
    (rec : ∀ (l' : TypeLevel), TypeLevelLT l' l → Context → Term → RedRel → Prop) :
    Context → Term → RedRel → Prop where
  | U {Γ : Context} {l' : TypeLevel} (hU : RedUAt l' l Γ) :
      LogRel eqrel l rec Γ .univ (RedURel eqrel (rec l' hU.lt) Γ)
  | nat {Γ : Context} {A : Term} (D : RedNat Γ A) :
      LogRel eqrel l rec Γ A (RedNatRel eqrel Γ)
  | ne {Γ : Context} {A K : Term} (neA : RedNeAt eqrel Γ A K) :
      LogRel eqrel l rec Γ A (RedNeRel eqrel Γ K)
  | pi {Γ : Context} {A F G : Term}
      (D : TypeStarWf Γ A (.pi F G))
      (hF : TypeWf Γ F)
      (hG : TypeWf (F :: Γ) G)
      (AeqA : eqrel.TypeEqRel Γ (.pi F G) (.pi F G))
      (relF : Wk → Context → RedRel → Prop)
      (relG : Wk → Context → Term → RedRel → Prop)
      (hF_ex : ∀ {ρ Δ}, WkCtx ρ Δ Γ → CtxWf Δ → ∃ rel, relF ρ Δ rel)
      (derivF : ∀ {ρ Δ} (_hρ : WkCtx ρ Δ Γ) (_hΔ : CtxWf Δ) (rel : RedRel),
        relF ρ Δ rel → LogRel eqrel l rec Δ (wk ρ F) rel)
      (hG_ex : ∀ {ρ Δ a}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a → ∃ rel, relG ρ Δ a rel)
      (derivG : ∀ {ρ Δ a} (_hρ : WkCtx ρ Δ Γ) (_hΔ : CtxWf Δ)
        (_ha : RelFHasTerm relF ρ Δ a) (rel : RedRel),
        relG ρ Δ a rel → LogRel eqrel l rec Δ (subst0 (wk (.lift ρ) G) a) rel)
      (Gext : ∀ {ρ Δ a b}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a →
        RelFHasTerm relF ρ Δ b →
        RelFEqTerm relF ρ Δ a b →
        RelGEqType relG ρ Δ a (subst0 (wk (.lift ρ) G) b)) :
      LogRel eqrel l rec Γ A (RedPiRel eqrel Γ F G relF relG)
  | empty {Γ : Context} {A : Term} (D : RedEmpty Γ A) :
      LogRel eqrel l rec Γ A (RedEmptyRel eqrel Γ)
  | unit {Γ : Context} {A : Term} (D : RedUnit Γ A) :
      LogRel eqrel l rec Γ A (RedUnitRel Γ)
  | sigma {Γ : Context} {A F G : Term}
      (D : TypeStarWf Γ A (.sigma F G))
      (hF : TypeWf Γ F)
      (hG : TypeWf (F :: Γ) G)
      (AeqA : eqrel.TypeEqRel Γ (.sigma F G) (.sigma F G))
      (relF : Wk → Context → RedRel → Prop)
      (relG : Wk → Context → Term → RedRel → Prop)
      (hF_ex : ∀ {ρ Δ}, WkCtx ρ Δ Γ → CtxWf Δ → ∃ rel, relF ρ Δ rel)
      (derivF : ∀ {ρ Δ} (_hρ : WkCtx ρ Δ Γ) (_hΔ : CtxWf Δ) (rel : RedRel),
        relF ρ Δ rel → LogRel eqrel l rec Δ (wk ρ F) rel)
      (hG_ex : ∀ {ρ Δ a}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a → ∃ rel, relG ρ Δ a rel)
      (derivG : ∀ {ρ Δ a} (_hρ : WkCtx ρ Δ Γ) (_hΔ : CtxWf Δ)
        (_ha : RelFHasTerm relF ρ Δ a) (rel : RedRel),
        relG ρ Δ a rel → LogRel eqrel l rec Δ (subst0 (wk (.lift ρ) G) a) rel)
      (Gext : ∀ {ρ Δ a b}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a →
        RelFHasTerm relF ρ Δ b →
        RelFEqTerm relF ρ Δ a b →
        RelGEqType relG ρ Δ a (subst0 (wk (.lift ρ) G) b)) :
      LogRel eqrel l rec Γ A (RedSigmaRel eqrel Γ F G relF relG)
  | emb {Γ : Context} {A : Term} {l' : TypeLevel} {rel : RedRel}
      (hlt : TypeLevelLT l' l)
      (hA : rec l' hlt Γ A rel) :
      LogRel eqrel l rec Γ A rel

/-- Empty lower-level relation at level `⁰`. -/
def logRelRecZero : ∀ (l' : TypeLevel), TypeLevelLT l' .zero → Context → Term → RedRel → Prop :=
  fun _ hlt ↦ nomatch hlt

/-- Level recursion for `LogRel` (`logRelRec` in `Definition/LogicalRelation.agda`). -/
def logRelRec (eqrel : EqRelSet) :
    ∀ (l l' : TypeLevel), TypeLevelLT l' l → Context → Term → RedRel → Prop
  | .zero => logRelRecZero
  | .one => fun _ .zeroLT ↦ LogRel eqrel .zero logRelRecZero

/-- The logical relation at level `l` (`kit l`). -/
abbrev LogRelAt (eqrel : EqRelSet) (l : TypeLevel) : Context → Term → RedRel → Prop :=
  LogRel eqrel l (logRelRec eqrel l)

/-- Reducibility of a type at level `l` (`Γ ⊩⟨ l ⟩ A`). -/
def RedType (eqrel : EqRelSet) (l : TypeLevel) (Γ : Context) (A : Term) : Prop :=
  ∃ rel, LogRelAt eqrel l Γ A rel

/-- Reducible type equality (`Γ ⊩⟨ l ⟩ A ≡ B / [A]`). -/
def RedEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (_hA : RedType eqrel l Γ A) (B : Term) : Prop :=
  ∃ rel, LogRelAt eqrel l Γ A rel ∧ rel.eqType B

/-- Reducible term (`Γ ⊩⟨ l ⟩ t ∷ A / [A]`). -/
def RedTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (_hA : RedType eqrel l Γ A) (t : Term) : Prop :=
  ∃ rel, LogRelAt eqrel l Γ A rel ∧ rel.hasTerm t

/-- Reducible term equality (`Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]`). -/
def RedTermEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (_hA : RedType eqrel l Γ A) (t u : Term) : Prop :=
  ∃ rel, LogRelAt eqrel l Γ A rel ∧ rel.eqTerm t u

/-!
## Smart Constructors for `RedType` and `Π`-types
-/

/-- Bundled `Π`-reducibility data with explicit domain `F` and codomain `G` (`Γ ⊩′⟨ l ⟩Π A`). -/
structure RedPiAt (eqrel : EqRelSet) (l : TypeLevel) (Γ : Context) (A F G : Term) : Prop where
  D : TypeStarWf Γ A (.pi F G)
  hF : TypeWf Γ F
  hG : TypeWf (F :: Γ) G
  AeqA : eqrel.TypeEqRel Γ (.pi F G) (.pi F G)
  redF : ∀ {ρ Δ}, WkCtx ρ Δ Γ → CtxWf Δ → RedType eqrel l Δ (wk ρ F)
  redG : ∀ {ρ Δ a} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ),
    RedTerm (redF hρ hΔ) a → RedType eqrel l Δ (subst0 (wk (.lift ρ) G) a)
  Gext : ∀ {ρ Δ a b} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ)
    (ha : RedTerm (redF hρ hΔ) a) (_hb : RedTerm (redF hρ hΔ) b),
    RedTermEq (redF hρ hΔ) a b →
    RedEq (redG hρ hΔ ha) (subst0 (wk (.lift ρ) G) b)

/-- Bundled `Π`-reducibility data (`Γ ⊩′⟨ l ⟩Π A`). -/
inductive RedPi (eqrel : EqRelSet) (l : TypeLevel) (Γ : Context) (A : Term) : Prop where
  | mk (F G : Term)
      (D : TypeStarWf Γ A (.pi F G))
      (hF : TypeWf Γ F)
      (hG : TypeWf (F :: Γ) G)
      (AeqA : eqrel.TypeEqRel Γ (.pi F G) (.pi F G))
      (redF : ∀ {ρ Δ}, WkCtx ρ Δ Γ → CtxWf Δ → RedType eqrel l Δ (wk ρ F))
      (redG : ∀ {ρ Δ a} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ),
        RedTerm (redF hρ hΔ) a → RedType eqrel l Δ (subst0 (wk (.lift ρ) G) a))
      (Gext : ∀ {ρ Δ a b} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ)
        (ha : RedTerm (redF hρ hΔ) a) (_hb : RedTerm (redF hρ hΔ) b),
        RedTermEq (redF hρ hΔ) a b →
        RedEq (redG hρ hΔ ha) (subst0 (wk (.lift ρ) G) b))

/-- Bundled `Σ`-reducibility data with explicit components (`Γ ⊩′⟨ l ⟩B⟨ BΣ ⟩ A`). -/
structure RedSigmaAt (eqrel : EqRelSet) (l : TypeLevel) (Γ : Context) (A F G : Term) : Prop where
  D : TypeStarWf Γ A (.sigma F G)
  hF : TypeWf Γ F
  hG : TypeWf (F :: Γ) G
  AeqA : eqrel.TypeEqRel Γ (.sigma F G) (.sigma F G)
  redF : ∀ {ρ Δ}, WkCtx ρ Δ Γ → CtxWf Δ → RedType eqrel l Δ (wk ρ F)
  redG : ∀ {ρ Δ a} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ),
    RedTerm (redF hρ hΔ) a → RedType eqrel l Δ (subst0 (wk (.lift ρ) G) a)
  Gext : ∀ {ρ Δ a b} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ)
    (ha : RedTerm (redF hρ hΔ) a) (_hb : RedTerm (redF hρ hΔ) b),
    RedTermEq (redF hρ hΔ) a b →
    RedEq (redG hρ hΔ ha) (subst0 (wk (.lift ρ) G) b)

theorem RedType.U {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context}
    (hU : RedU l Γ) : RedType eqrel l Γ .univ := by
  rcases hU with ⟨l', lt, wf⟩
  exact ⟨_, .U ⟨lt, wf⟩⟩

theorem RedType.nat {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (D : RedNat Γ A) : RedType eqrel l Γ A :=
  ⟨_, .nat D⟩

theorem RedType.ne {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (neA : RedNe eqrel Γ A) : RedType eqrel l Γ A := by
  rcases neA with ⟨K, D, neK, KeqK⟩
  exact ⟨_, .ne (K := K) ⟨D, neK, KeqK⟩⟩

theorem RedType.piAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A F G : Term}
    (piA : RedPiAt eqrel l Γ A F G) : RedType eqrel l Γ A :=
  ⟨_, .pi piA.D piA.hF piA.hG piA.AeqA
    (fun ρ Δ rel ↦ LogRelAt eqrel l Δ (wk ρ F) rel)
    (fun ρ Δ a rel ↦ LogRelAt eqrel l Δ (subst0 (wk (.lift ρ) G) a) rel)
    piA.redF
    (fun _ _ _ h ↦ h)
    piA.redG
    (fun _ _ _ _ h ↦ h)
    piA.Gext⟩

theorem RedType.pi {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (piA : RedPi eqrel l Γ A) : RedType eqrel l Γ A := by
  rcases piA with ⟨F, G, D, hF, hG, AeqA, redF, redG, Gext⟩
  exact RedType.piAt ⟨D, hF, hG, AeqA, redF, redG, Gext⟩

theorem RedType.sigmaAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A F G : Term}
    (sigmaA : RedSigmaAt eqrel l Γ A F G) : RedType eqrel l Γ A :=
  ⟨_, .sigma sigmaA.D sigmaA.hF sigmaA.hG sigmaA.AeqA
    (fun ρ Δ rel ↦ LogRelAt eqrel l Δ (wk ρ F) rel)
    (fun ρ Δ a rel ↦ LogRelAt eqrel l Δ (subst0 (wk (.lift ρ) G) a) rel)
    sigmaA.redF
    (fun _ _ _ h ↦ h)
    sigmaA.redG
    (fun _ _ _ _ h ↦ h)
    sigmaA.Gext⟩

theorem RedType.empty {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (D : RedEmpty Γ A) : RedType eqrel l Γ A :=
  ⟨_, .empty D⟩

theorem RedType.unit {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (D : RedUnit Γ A) : RedType eqrel l Γ A :=
  ⟨_, .unit D⟩

theorem RedType.emb {eqrel : EqRelSet} {l' l : TypeLevel} {Γ : Context} {A : Term}
    (hlt : TypeLevelLT l' l) (hA : RedType eqrel l' Γ A) : RedType eqrel l Γ A := by
  rcases hlt with ⟨⟩
  rcases hA with ⟨rel, hrel⟩
  exact ⟨rel, .emb .zeroLT hrel⟩

/-- Any level can be embedded into level `¹` (`maybeEmb`). -/
theorem maybeEmb {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hA : RedType eqrel l Γ A) : RedType eqrel .one Γ A := by
  cases l with
  | zero => exact RedType.emb .zeroLT hA
  | one => exact hA

/-- Level `⁰` can be embedded into any level `l` (`maybeEmb′`). -/
theorem maybeEmb' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hA : RedType eqrel .zero Γ A) : RedType eqrel l Γ A := by
  cases l with
  | zero => exact hA
  | one => exact RedType.emb .zeroLT hA

/-!
## Irrelevance and Uniqueness of Decoded Relations (`Irrelevance.agda` + `ShapeView.agda`)
-/

/-- Non-embedded characterization of a `LogRelAt` derivation: stripping `.emb` preserves `rel`
and yields one of the four canonical type shapes (`.U`, `.nat`, `.ne`, `.pi`). -/
inductive LogRelShape (eqrel : EqRelSet) : Context → Term → RedRel → Prop where
  | U {l' l : TypeLevel} {Γ : Context} (hU : RedUAt l' l Γ) :
      LogRelShape eqrel Γ .univ (RedURel eqrel (logRelRec eqrel l l' hU.lt) Γ)
  | nat {Γ : Context} {A : Term} (D : RedNat Γ A) :
      LogRelShape eqrel Γ A (RedNatRel eqrel Γ)
  | ne {Γ : Context} {A K : Term} (neA : RedNeAt eqrel Γ A K) :
      LogRelShape eqrel Γ A (RedNeRel eqrel Γ K)
  | pi {l : TypeLevel} {Γ : Context} {A F G : Term}
      (D : TypeStarWf Γ A (.pi F G))
      (hF : TypeWf Γ F)
      (hG : TypeWf (F :: Γ) G)
      (AeqA : eqrel.TypeEqRel Γ (.pi F G) (.pi F G))
      (relF : Wk → Context → RedRel → Prop)
      (relG : Wk → Context → Term → RedRel → Prop)
      (hF_ex : ∀ {ρ Δ}, WkCtx ρ Δ Γ → CtxWf Δ → ∃ rel, relF ρ Δ rel)
      (derivF : ∀ {ρ Δ} (_hρ : WkCtx ρ Δ Γ) (_hΔ : CtxWf Δ) (rel : RedRel),
        relF ρ Δ rel → LogRelAt eqrel l Δ (wk ρ F) rel)
      (hG_ex : ∀ {ρ Δ a}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a → ∃ rel, relG ρ Δ a rel)
      (derivG : ∀ {ρ Δ a} (_hρ : WkCtx ρ Δ Γ) (_hΔ : CtxWf Δ)
        (_ha : RelFHasTerm relF ρ Δ a) (rel : RedRel),
        relG ρ Δ a rel → LogRelAt eqrel l Δ (subst0 (wk (.lift ρ) G) a) rel)
      (Gext : ∀ {ρ Δ a b}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a →
        RelFHasTerm relF ρ Δ b →
        RelFEqTerm relF ρ Δ a b →
        RelGEqType relG ρ Δ a (subst0 (wk (.lift ρ) G) b)) :
      LogRelShape eqrel Γ A (RedPiRel eqrel Γ F G relF relG)
  | empty {Γ : Context} {A : Term} (D : RedEmpty Γ A) :
      LogRelShape eqrel Γ A (RedEmptyRel eqrel Γ)
  | unit {Γ : Context} {A : Term} (D : RedUnit Γ A) :
      LogRelShape eqrel Γ A (RedUnitRel Γ)
  | sigma {l : TypeLevel} {Γ : Context} {A F G : Term}
      (D : TypeStarWf Γ A (.sigma F G))
      (hF : TypeWf Γ F)
      (hG : TypeWf (F :: Γ) G)
      (AeqA : eqrel.TypeEqRel Γ (.sigma F G) (.sigma F G))
      (relF : Wk → Context → RedRel → Prop)
      (relG : Wk → Context → Term → RedRel → Prop)
      (hF_ex : ∀ {ρ Δ}, WkCtx ρ Δ Γ → CtxWf Δ → ∃ rel, relF ρ Δ rel)
      (derivF : ∀ {ρ Δ} (_hρ : WkCtx ρ Δ Γ) (_hΔ : CtxWf Δ) (rel : RedRel),
        relF ρ Δ rel → LogRelAt eqrel l Δ (wk ρ F) rel)
      (hG_ex : ∀ {ρ Δ a}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a → ∃ rel, relG ρ Δ a rel)
      (derivG : ∀ {ρ Δ a} (_hρ : WkCtx ρ Δ Γ) (_hΔ : CtxWf Δ)
        (_ha : RelFHasTerm relF ρ Δ a) (rel : RedRel),
        relG ρ Δ a rel → LogRelAt eqrel l Δ (subst0 (wk (.lift ρ) G) a) rel)
      (Gext : ∀ {ρ Δ a b}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a →
        RelFHasTerm relF ρ Δ b →
        RelFEqTerm relF ρ Δ a b →
        RelGEqType relG ρ Δ a (subst0 (wk (.lift ρ) G) b)) :
      LogRelShape eqrel Γ A (RedSigmaRel eqrel Γ F G relF relG)

theorem logRelShape_of_LogRelAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    {rel : RedRel} (h : LogRelAt eqrel l Γ A rel) : LogRelShape eqrel Γ A rel := by
  cases h with
  | U hU => exact .U hU
  | nat D => exact .nat D
  | ne neA => exact .ne neA
  | pi D hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext =>
      exact .pi D hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext
  | emb hlt hA =>
      cases hlt
      cases hA with
      | U hU => exact .U hU
      | nat D => exact .nat D
      | ne neA => exact .ne neA
      | pi D hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext =>
          exact .pi D hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext
      | emb hlt' _ => cases hlt'

/-- Equivalence of two `RedRel` bundles. -/
def RedRelEquiv (rel₁ rel₂ : RedRel) : Prop :=
  (∀ {B}, rel₁.eqType B ↔ rel₂.eqType B) ∧
  (∀ {t}, rel₁.hasTerm t ↔ rel₂.hasTerm t) ∧
  (∀ {t u}, rel₁.eqTerm t u ↔ rel₂.eqTerm t u)

theorem RedRelEquiv.refl (rel : RedRel) : RedRelEquiv rel rel :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem RedRelEquiv.symm {rel₁ rel₂ : RedRel} (h : RedRelEquiv rel₁ rel₂) :
    RedRelEquiv rel₂ rel₁ :=
  ⟨fun {B} ↦ (h.1 (B := B)).symm,
   fun {t} ↦ (h.2.1 (t := t)).symm,
   fun {t u} ↦ (h.2.2 (t := t) (u := u)).symm⟩

theorem RedRelEquiv.trans {rel₁ rel₂ rel₃ : RedRel}
    (h₁₂ : RedRelEquiv rel₁ rel₂) (h₂₃ : RedRelEquiv rel₂ rel₃) :
    RedRelEquiv rel₁ rel₃ :=
  ⟨fun {B} ↦ (h₁₂.1 (B := B)).trans (h₂₃.1 (B := B)),
   fun {t} ↦ (h₁₂.2.1 (t := t)).trans (h₂₃.2.1 (t := t)),
   fun {t u} ↦ (h₁₂.2.2 (t := t) (u := u)).trans (h₂₃.2.2 (t := t) (u := u))⟩

theorem logRelRec_eq {eqrel : EqRelSet} {l₁ l₂ l₁' l₂' : TypeLevel}
    (lt₁ : TypeLevelLT l₁' l₁) (lt₂ : TypeLevelLT l₂' l₂) :
    logRelRec eqrel l₁ l₁' lt₁ = logRelRec eqrel l₂ l₂' lt₂ := by
  cases lt₁
  cases lt₂
  rfl

/-- Core irrelevance theorem for a single level `l`: any two `RedRel`s derived for the same
type `(Γ, A)` (even at different levels) are equivalent (`RedRelEquiv`). -/
theorem irrelLogRel_step {eqrel : EqRelSet} {l : TypeLevel}
    {rec : ∀ (l' : TypeLevel), TypeLevelLT l' l → Context → Term → RedRel → Prop}
    (hRecEq : ∀ {l₁ l₂ l₂'} (lt₁ : TypeLevelLT l₁ l) (lt₂ : TypeLevelLT l₂' l₂),
      rec l₁ lt₁ = logRelRec eqrel l₂ l₂' lt₂)
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A rel₁ rel₂},
      rec l' hlt Γ A rel₁ → LogRelShape eqrel Γ A rel₂ → RedRelEquiv rel₁ rel₂)
    (_hRecShape : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A rel},
      rec l' hlt Γ A rel → LogRelShape eqrel Γ A rel)
    {Γ : Context} {A : Term} {rel₁ : RedRel}
    (h₁ : LogRel eqrel l rec Γ A rel₁) :
    ∀ {A' : Term} {rel₂ : RedRel}, A = A' → LogRelShape eqrel Γ A' rel₂ → RedRelEquiv rel₁ rel₂ := by
  induction h₁ with
  | @U Γ l₁ hU =>
      intro A' rel₂ hAA' h₂
      subst hAA'
      cases h₂ with
      | U hU₂ =>
          rw [hRecEq hU.lt hU₂.lt]
          exact RedRelEquiv.refl _
      | nat D =>
          have h := whnfRedStar D.reduction .univ
          cases h
      | ne neA =>
          have h := whnfRedStar neA.D.reduction .univ
          subst h
          cases neA.neK
      | pi D =>
          have h := whnfRedStar D.reduction .univ
          cases h
  | @nat Γ A D₁ =>
      intro A' rel₂ hAA' h₂
      subst hAA'
      cases h₂ with
      | U _ =>
          have h := whnfRedStar D₁.reduction .univ
          cases h
      | nat _ => exact RedRelEquiv.refl _
      | ne neB =>
          have h := whrDetStar ⟨D₁.reduction, .nat⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | pi D₂ =>
          have h := whrDetStar ⟨D₁.reduction, .nat⟩ ⟨D₂.reduction, .pi⟩
          cases h
  | @ne Γ A K₁ neA =>
      intro A' rel₂ hAA' h₂
      subst hAA'
      cases h₂ with
      | U _ =>
          have h := whnfRedStar neA.D.reduction .univ
          subst h
          cases neA.neK
      | nat D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .nat⟩ ⟨neA.D.reduction, .neutral neA.neK⟩
          subst h
          cases neA.neK
      | @ne _ _ K₂ neB =>
          have hK : K₁ = K₂ :=
            whrDetStar ⟨neA.D.reduction, .neutral neA.neK⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          rw [hK]
          exact RedRelEquiv.refl _
      | pi D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .pi⟩ ⟨neA.D.reduction, .neutral neA.neK⟩
          subst h
          cases neA.neK
  | @pi Γ A F₁ G₁ D₁ _hF₁ _hG₁ _AeqA₁ relF₁ relG₁ hF_ex₁ _derivF₁ hG_ex₁ _derivG₁ _Gext₁ ihF ihG =>
      intro A' rel₂ hAA' h₂
      subst hAA'
      cases h₂ with
      | U _ =>
          have h := whnfRedStar D₁.reduction .univ
          cases h
      | nat D₂ =>
          have h := whrDetStar ⟨D₂.reduction, .nat⟩ ⟨D₁.reduction, .pi⟩
          cases h
      | ne neB =>
          have h := whrDetStar ⟨D₁.reduction, .pi⟩ ⟨neB.D.reduction, .neutral neB.neK⟩
          subst h
          cases neB.neK
      | @pi l₂ _ _ F₂ G₂ D₂ _ _ _ relF₂ relG₂ hF_ex₂ derivF₂ hG_ex₂ derivG₂ _ =>
          have hPi : Term.pi F₁ G₁ = Term.pi F₂ G₂ :=
            whrDetStar ⟨D₁.reduction, .pi⟩ ⟨D₂.reduction, .pi⟩
          injection hPi with hF₁₂ hG₁₂
          subst hF₁₂ hG₁₂
          have hFeqType : ∀ {ρ Δ B} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ),
              RelFEqType relF₁ ρ Δ B ↔ RelFEqType relF₂ ρ Δ B := by
            intro ρ Δ B hρ hΔ
            constructor
            · rintro ⟨r₁, hr₁, hB⟩
              rcases hF_ex₂ hρ hΔ with ⟨r₂, hr₂⟩
              have heq := ihF hρ hΔ r₁ hr₁ rfl (logRelShape_of_LogRelAt (derivF₂ hρ hΔ r₂ hr₂))
              exact ⟨r₂, hr₂, heq.1.mp hB⟩
            · rintro ⟨r₂, hr₂, hB⟩
              rcases hF_ex₁ hρ hΔ with ⟨r₁, hr₁⟩
              have heq := ihF hρ hΔ r₁ hr₁ rfl (logRelShape_of_LogRelAt (derivF₂ hρ hΔ r₂ hr₂))
              exact ⟨r₁, hr₁, heq.1.mpr hB⟩
          have hFhasTerm : ∀ {ρ Δ a} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ),
              RelFHasTerm relF₁ ρ Δ a ↔ RelFHasTerm relF₂ ρ Δ a := by
            intro ρ Δ a hρ hΔ
            constructor
            · rintro ⟨r₁, hr₁, ha⟩
              rcases hF_ex₂ hρ hΔ with ⟨r₂, hr₂⟩
              have heq := ihF hρ hΔ r₁ hr₁ rfl (logRelShape_of_LogRelAt (derivF₂ hρ hΔ r₂ hr₂))
              exact ⟨r₂, hr₂, heq.2.1.mp ha⟩
            · rintro ⟨r₂, hr₂, ha⟩
              rcases hF_ex₁ hρ hΔ with ⟨r₁, hr₁⟩
              have heq := ihF hρ hΔ r₁ hr₁ rfl (logRelShape_of_LogRelAt (derivF₂ hρ hΔ r₂ hr₂))
              exact ⟨r₁, hr₁, heq.2.1.mpr ha⟩
          have hFeqTerm : ∀ {ρ Δ a b} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ),
              RelFEqTerm relF₁ ρ Δ a b ↔ RelFEqTerm relF₂ ρ Δ a b := by
            intro ρ Δ a b hρ hΔ
            constructor
            · rintro ⟨r₁, hr₁, hab⟩
              rcases hF_ex₂ hρ hΔ with ⟨r₂, hr₂⟩
              have heq := ihF hρ hΔ r₁ hr₁ rfl (logRelShape_of_LogRelAt (derivF₂ hρ hΔ r₂ hr₂))
              exact ⟨r₂, hr₂, heq.2.2.mp hab⟩
            · rintro ⟨r₂, hr₂, hab⟩
              rcases hF_ex₁ hρ hΔ with ⟨r₁, hr₁⟩
              have heq := ihF hρ hΔ r₁ hr₁ rfl (logRelShape_of_LogRelAt (derivF₂ hρ hΔ r₂ hr₂))
              exact ⟨r₁, hr₁, heq.2.2.mpr hab⟩
          have hGeqType : ∀ {ρ Δ a B} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ)
              (ha₁ : RelFHasTerm relF₁ ρ Δ a),
              RelGEqType relG₁ ρ Δ a B ↔ RelGEqType relG₂ ρ Δ a B := by
            intro ρ Δ a B hρ hΔ ha₁
            have ha₂ : RelFHasTerm relF₂ ρ Δ a := (hFhasTerm hρ hΔ).mp ha₁
            constructor
            · rintro ⟨s₁, hs₁, hB⟩
              rcases hG_ex₂ hρ hΔ ha₂ with ⟨s₂, hs₂⟩
              have heq := ihG hρ hΔ ha₁ s₁ hs₁ rfl
                (logRelShape_of_LogRelAt (derivG₂ hρ hΔ ha₂ s₂ hs₂))
              exact ⟨s₂, hs₂, heq.1.mp hB⟩
            · rintro ⟨s₂, hs₂, hB⟩
              rcases hG_ex₁ hρ hΔ ha₁ with ⟨s₁, hs₁⟩
              have heq := ihG hρ hΔ ha₁ s₁ hs₁ rfl
                (logRelShape_of_LogRelAt (derivG₂ hρ hΔ ha₂ s₂ hs₂))
              exact ⟨s₁, hs₁, heq.1.mpr hB⟩
          have hGhasTerm : ∀ {ρ Δ a t} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ)
              (ha₁ : RelFHasTerm relF₁ ρ Δ a),
              RelGHasTerm relG₁ ρ Δ a t ↔ RelGHasTerm relG₂ ρ Δ a t := by
            intro ρ Δ a t hρ hΔ ha₁
            have ha₂ : RelFHasTerm relF₂ ρ Δ a := (hFhasTerm hρ hΔ).mp ha₁
            constructor
            · rintro ⟨s₁, hs₁, ht⟩
              rcases hG_ex₂ hρ hΔ ha₂ with ⟨s₂, hs₂⟩
              have heq := ihG hρ hΔ ha₁ s₁ hs₁ rfl
                (logRelShape_of_LogRelAt (derivG₂ hρ hΔ ha₂ s₂ hs₂))
              exact ⟨s₂, hs₂, heq.2.1.mp ht⟩
            · rintro ⟨s₂, hs₂, ht⟩
              rcases hG_ex₁ hρ hΔ ha₁ with ⟨s₁, hs₁⟩
              have heq := ihG hρ hΔ ha₁ s₁ hs₁ rfl
                (logRelShape_of_LogRelAt (derivG₂ hρ hΔ ha₂ s₂ hs₂))
              exact ⟨s₁, hs₁, heq.2.1.mpr ht⟩
          have hGeqTerm : ∀ {ρ Δ a t u} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ)
              (ha₁ : RelFHasTerm relF₁ ρ Δ a),
              RelGEqTerm relG₁ ρ Δ a t u ↔ RelGEqTerm relG₂ ρ Δ a t u := by
            intro ρ Δ a t u hρ hΔ ha₁
            have ha₂ : RelFHasTerm relF₂ ρ Δ a := (hFhasTerm hρ hΔ).mp ha₁
            constructor
            · rintro ⟨s₁, hs₁, htu⟩
              rcases hG_ex₂ hρ hΔ ha₂ with ⟨s₂, hs₂⟩
              have heq := ihG hρ hΔ ha₁ s₁ hs₁ rfl
                (logRelShape_of_LogRelAt (derivG₂ hρ hΔ ha₂ s₂ hs₂))
              exact ⟨s₂, hs₂, heq.2.2.mp htu⟩
            · rintro ⟨s₂, hs₂, htu⟩
              rcases hG_ex₁ hρ hΔ ha₁ with ⟨s₁, hs₁⟩
              have heq := ihG hρ hΔ ha₁ s₁ hs₁ rfl
                (logRelShape_of_LogRelAt (derivG₂ hρ hΔ ha₂ s₂ hs₂))
              exact ⟨s₁, hs₁, heq.2.2.mpr htu⟩
          have hPiTermIff : ∀ {t},
              RedPiTerm eqrel Γ F₁ G₁ relF₁ relG₁ t ↔ RedPiTerm eqrel Γ F₁ G₁ relF₂ relG₂ t := by
            intro t
            constructor
            · rintro ⟨f, d, funcF, feqf, appEq, appTerm⟩
              refine ⟨f, d, funcF, feqf, ?_, ?_⟩
              · intro ρ Δ a b hρ hΔ ha₂ hb₂ hab₂
                have ha₁ := (hFhasTerm hρ hΔ).mpr ha₂
                have hb₁ := (hFhasTerm hρ hΔ).mpr hb₂
                have hab₁ := (hFeqTerm hρ hΔ).mpr hab₂
                exact (hGeqTerm hρ hΔ ha₁).mp (appEq hρ hΔ ha₁ hb₁ hab₁)
              · intro ρ Δ a hρ hΔ ha₂
                have ha₁ := (hFhasTerm hρ hΔ).mpr ha₂
                exact (hGhasTerm hρ hΔ ha₁).mp (appTerm hρ hΔ ha₁)
            · rintro ⟨f, d, funcF, feqf, appEq, appTerm⟩
              refine ⟨f, d, funcF, feqf, ?_, ?_⟩
              · intro ρ Δ a b hρ hΔ ha₁ hb₁ hab₁
                have ha₂ := (hFhasTerm hρ hΔ).mp ha₁
                have hb₂ := (hFhasTerm hρ hΔ).mp hb₁
                have hab₂ := (hFeqTerm hρ hΔ).mp hab₁
                exact (hGeqTerm hρ hΔ ha₁).mpr (appEq hρ hΔ ha₂ hb₂ hab₂)
              · intro ρ Δ a hρ hΔ ha₁
                have ha₂ := (hFhasTerm hρ hΔ).mp ha₁
                exact (hGhasTerm hρ hΔ ha₁).mpr (appTerm hρ hΔ ha₂)
          refine ⟨?_, hPiTermIff, ?_⟩
          · intro B
            constructor
            · rintro ⟨F', G', D', AeqB, FeqF', GeqG'⟩
              refine ⟨F', G', D', AeqB,
                fun hρ hΔ ↦ (hFeqType hρ hΔ).mp (FeqF' hρ hΔ),
                fun hρ hΔ ha₂ ↦ ?_⟩
              have ha₁ := (hFhasTerm hρ hΔ).mpr ha₂
              exact (hGeqType hρ hΔ ha₁).mp (GeqG' hρ hΔ ha₁)
            · rintro ⟨F', G', D', AeqB, FeqF', GeqG'⟩
              refine ⟨F', G', D', AeqB,
                fun hρ hΔ ↦ (hFeqType hρ hΔ).mpr (FeqF' hρ hΔ),
                fun hρ hΔ ha₁ ↦ ?_⟩
              have ha₂ := (hFhasTerm hρ hΔ).mp ha₁
              exact (hGeqType hρ hΔ ha₁).mpr (GeqG' hρ hΔ ha₂)
          · intro t u
            constructor
            · rintro ⟨f, g, d, d', funcF, funcG, feqg, ht, hu, appEq⟩
              refine ⟨f, g, d, d', funcF, funcG, feqg,
                hPiTermIff.mp ht, hPiTermIff.mp hu, fun hρ hΔ ha₂ ↦ ?_⟩
              have ha₁ := (hFhasTerm hρ hΔ).mpr ha₂
              exact (hGeqTerm hρ hΔ ha₁).mp (appEq hρ hΔ ha₁)
            · rintro ⟨f, g, d, d', funcF, funcG, feqg, ht, hu, appEq⟩
              refine ⟨f, g, d, d', funcF, funcG, feqg,
                hPiTermIff.mpr ht, hPiTermIff.mpr hu, fun hρ hΔ ha₁ ↦ ?_⟩
              have ha₂ := (hFhasTerm hρ hΔ).mp ha₁
              exact (hGeqTerm hρ hΔ ha₁).mpr (appEq hρ hΔ ha₂)
  | @emb Γ A l' rel hlt hA =>
      intro A' rel₂ hAA' h₂
      subst hAA'
      exact ihRec l' hlt hA h₂

/-- Full irrelevance theorem across all levels `l₁, l₂`: any two `RedRel`s derived for the same
type `(Γ, A)` are equivalent (`RedRelEquiv`). -/
theorem irrelLogRel {eqrel : EqRelSet} {l₁ l₂ : TypeLevel} {Γ : Context} {A : Term}
    {rel₁ rel₂ : RedRel}
    (h₁ : LogRelAt eqrel l₁ Γ A rel₁)
    (h₂ : LogRelAt eqrel l₂ Γ A rel₂) :
    RedRelEquiv rel₁ rel₂ := by
  have h0 : ∀ {Γ A rel₁ rel₂},
      LogRelAt eqrel .zero Γ A rel₁ → LogRelShape eqrel Γ A rel₂ → RedRelEquiv rel₁ rel₂ :=
    fun h₁ h₂s ↦ irrelLogRel_step (l := .zero) (rec := logRelRec eqrel .zero)
      (fun lt₁ _ ↦ nomatch lt₁)
      (fun _ hlt ↦ nomatch hlt)
      (fun _ hlt ↦ nomatch hlt)
      h₁ rfl h₂s
  cases l₁ with
  | zero => exact h0 h₁ (logRelShape_of_LogRelAt h₂)
  | one =>
      exact irrelLogRel_step (l := .one) (rec := logRelRec eqrel .one)
        (fun lt₁ lt₂ ↦ logRelRec_eq lt₁ lt₂)
        (fun _ hlt _ _ _ _ h₁' h₂s ↦ by cases hlt; exact h0 h₁' h₂s)
        (fun _ hlt _ _ _ h₁' ↦ by cases hlt; exact logRelShape_of_LogRelAt h₁')
        h₁ rfl (logRelShape_of_LogRelAt h₂)

/-!
## Irrelevance Corollaries (`Definition/LogicalRelation/Irrelevance.agda`)
-/

/-- Irrelevance for propositionally equal types (`irrelevance′`). -/
theorem irrelevance' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A A' : Term}
    (h : A = A') (p : RedType eqrel l Γ A) : RedType eqrel l Γ A' :=
  h ▸ p

/-- Irrelevance for propositionally equal contexts and types (`irrelevanceΓ′`). -/
theorem irrelevanceΓ' {eqrel : EqRelSet} {l : TypeLevel} {Γ Γ' : Context} {A A' : Term}
    (hΓ : Γ = Γ') (hA : A = A') (p : RedType eqrel l Γ A) : RedType eqrel l Γ' A' := by
  subst hΓ hA
  exact p

/-- Irrelevance for reducible type equality (`irrelevanceEq`). -/
theorem irrelevanceEq {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A B : Term}
    (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A)
    (hAB : RedEq p B) : RedEq q B := by
  rcases hAB with ⟨rel₁, h₁, hB⟩
  rcases q with ⟨rel₂, h₂⟩
  exact ⟨rel₂, h₂, (irrelLogRel h₁ h₂).1.mp hB⟩

/-- Irrelevance for reducible type equality with equal left types (`irrelevanceEq′`). -/
theorem irrelevanceEq' {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A A' B : Term}
    (hA : A = A') (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A')
    (hAB : RedEq p B) : RedEq q B := by
  subst hA
  exact irrelevanceEq p q hAB

/-- Irrelevance for reducible type equality with equal left and right types (`irrelevanceEq″`). -/
theorem irrelevanceEq'' {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A A' B B' : Term}
    (hA : A = A') (hB : B = B') (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A')
    (hAB : RedEq p B) : RedEq q B' := by
  subst hA hB
  exact irrelevanceEq p q hAB

/-- Irrelevance for reducible type equality with equal right types (`irrelevanceEqR′`). -/
theorem irrelevanceEqR' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B B' : Term}
    (hB : B = B') (p : RedType eqrel l Γ A) (hAB : RedEq p B) : RedEq p B' :=
  hB ▸ hAB

/-- Irrelevance for reducible terms (`irrelevanceTerm`). -/
theorem irrelevanceTerm {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A t : Term}
    (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A)
    (ht : RedTerm p t) : RedTerm q t := by
  rcases ht with ⟨rel₁, h₁, ht⟩
  rcases q with ⟨rel₂, h₂⟩
  exact ⟨rel₂, h₂, (irrelLogRel h₁ h₂).2.1.mp ht⟩

/-- Irrelevance for reducible terms with equal types (`irrelevanceTerm′`). -/
theorem irrelevanceTerm' {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A A' t : Term}
    (hA : A = A') (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A')
    (ht : RedTerm p t) : RedTerm q t := by
  subst hA
  exact irrelevanceTerm p q ht

/-- Irrelevance for reducible terms with equal types and terms (`irrelevanceTerm″`). -/
theorem irrelevanceTerm'' {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A A' t t' : Term}
    (hA : A = A') (htEq : t = t') (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A')
    (ht : RedTerm p t) : RedTerm q t' := by
  subst hA htEq
  exact irrelevanceTerm p q ht

/-- Irrelevance for reducible terms with equal contexts, types, and terms (`irrelevanceTermΓ″`). -/
theorem irrelevanceTermΓ'' {eqrel : EqRelSet} {l l' : TypeLevel} {Γ Γ' : Context} {A A' t t' : Term}
    (hΓ : Γ = Γ') (hA : A = A') (htEq : t = t')
    (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ' A')
    (ht : RedTerm p t) : RedTerm q t' := by
  subst hΓ hA htEq
  exact irrelevanceTerm p q ht

/-- Irrelevance for reducible term equality (`irrelevanceEqTerm`). -/
theorem irrelevanceEqTerm {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A t u : Term}
    (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A)
    (htu : RedTermEq p t u) : RedTermEq q t u := by
  rcases htu with ⟨rel₁, h₁, htu⟩
  rcases q with ⟨rel₂, h₂⟩
  exact ⟨rel₂, h₂, (irrelLogRel h₁ h₂).2.2.mp htu⟩

/-- Irrelevance for reducible term equality with equal types (`irrelevanceEqTerm′`). -/
theorem irrelevanceEqTerm' {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context} {A A' t u : Term}
    (hA : A = A') (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A')
    (htu : RedTermEq p t u) : RedTermEq q t u := by
  subst hA
  exact irrelevanceEqTerm p q htu

/-- Irrelevance for reducible term equality with equal terms and types (`irrelevanceEqTerm″`). -/
theorem irrelevanceEqTerm'' {eqrel : EqRelSet} {l l' : TypeLevel} {Γ : Context}
    {A A' t t' u u' : Term}
    (htEq : t = t') (huEq : u = u') (hA : A = A')
    (p : RedType eqrel l Γ A) (q : RedType eqrel l' Γ A')
    (htu : RedTermEq p t u) : RedTermEq q t' u' := by
  subst htEq huEq hA
  exact irrelevanceEqTerm p q htu

/-!
## Constructor-Specific Characterizations of `RedEq`, `RedTerm`, `RedTermEq`
-/

theorem RedEq_of_LogRelAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B : Term}
    {rel : RedRel} (h : LogRelAt eqrel l Γ A rel) (p : RedType eqrel l Γ A) :
    RedEq p B ↔ rel.eqType B := by
  constructor
  · rintro ⟨rel', h', hB⟩
    exact (irrelLogRel h' h).1.mp hB
  · intro hB
    exact ⟨rel, h, hB⟩

theorem RedTerm_of_LogRelAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t : Term}
    {rel : RedRel} (h : LogRelAt eqrel l Γ A rel) (p : RedType eqrel l Γ A) :
    RedTerm p t ↔ rel.hasTerm t := by
  constructor
  · rintro ⟨rel', h', ht⟩
    exact (irrelLogRel h' h).2.1.mp ht
  · intro ht
    exact ⟨rel, h, ht⟩

theorem RedTermEq_of_LogRelAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u : Term}
    {rel : RedRel} (h : LogRelAt eqrel l Γ A rel) (p : RedType eqrel l Γ A) :
    RedTermEq p t u ↔ rel.eqTerm t u := by
  constructor
  · rintro ⟨rel', h', htu⟩
    exact (irrelLogRel h' h).2.2.mp htu
  · intro htu
    exact ⟨rel, h, htu⟩

/-!
## Escape Lemmas (`Definition/LogicalRelation/Properties/Escape.agda`)
-/

/-- Reducible types are syntactically well-formed (`escape`). -/
theorem escape {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (p : RedType eqrel l Γ A) : TypeWf Γ A := by
  rcases p with ⟨rel, h⟩
  cases logRelShape_of_LogRelAt h with
  | U hU => exact .univ hU.wf
  | nat D => exact D.source
  | ne neA => exact neA.D.source
  | pi D => exact D.source

/-- Reducible type equality implies `eqrel.TypeEqRel` (`escapeEq`). -/
theorem escapeEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A B : Term}
    (p : RedType eqrel l Γ A) (hAB : RedEq p B) : eqrel.TypeEqRel Γ A B := by
  rcases hAB with ⟨rel, h, hB⟩
  cases logRelShape_of_LogRelAt h with
  | U hU =>
      change B = .univ at hB
      subst hB
      exact eqrel.univRefl hU.wf
  | nat D =>
      change TypeStar Γ B .nat at hB
      exact eqrel.redType D.reduction hB .nat .nat (eqrel.natRefl (wfType D.source))
  | ne neA =>
      rcases hB with ⟨M, D', neM, KeqM⟩
      exact eqrel.redType neA.D.reduction D'.reduction (.neutral neA.neK) (.neutral neM)
        (eqrel.neToType KeqM)
  | pi D _ _ _ _ _ _ _ _ _ _ =>
      rcases hB with ⟨F', G', D', AeqB, _, _⟩
      exact eqrel.redType D.reduction D' .pi .pi AeqB

/-- Reducible terms are syntactically well-typed (`escapeTerm`). -/
theorem escapeTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t : Term}
    (p : RedType eqrel l Γ A) (ht : RedTerm p t) : HasType Γ t A := by
  rcases ht with ⟨rel, h, ht⟩
  cases logRelShape_of_LogRelAt h with
  | U _ =>
      rcases ht with ⟨_, d, _, _, _⟩
      exact d.source
  | nat D =>
      rcases ht with ⟨_, _, d, _, _⟩
      exact .conv d.source (.symm (subsetStar D.reduction))
  | ne neA =>
      rcases ht with ⟨_, d, _⟩
      exact .conv d.source (.symm (subsetStar neA.D.reduction))
  | pi D _ _ _ _ _ _ _ _ _ _ =>
      rcases ht with ⟨_, d, _, _, _, _⟩
      exact .conv d.source (.symm (subsetStar D.reduction))

/-- Reducible term equality implies `eqrel.TermEqRel` (`escapeTermEq`). -/
theorem escapeTermEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t u : Term}
    (p : RedType eqrel l Γ A) (htu : RedTermEq p t u) : eqrel.TermEqRel Γ t u A := by
  rcases htu with ⟨rel, h, htu⟩
  cases logRelShape_of_LogRelAt h with
  | U hU =>
      rcases htu with ⟨A₀, B₀, d, d', typeA, typeB, AeqB, _, _, _, _⟩
      exact eqrel.redTerm (.refl (.univ hU.wf)) d.reduction d'.reduction
        .univ typeA.toWhnf typeB.toWhnf AeqB
  | nat D =>
      rcases htu with ⟨_, _, k, k', d, d', keqk', prop⟩
      have ⟨natK, natK'⟩ := split_of_NaturalEqProp prop
      exact eqrel.redTerm D.reduction d.reduction d'.reduction .nat natK.toWhnf natK'.toWhnf keqk'
  | ne neA =>
      rcases htu with ⟨k, m, d, d', nf⟩
      exact eqrel.redTerm neA.D.reduction d.reduction d'.reduction
        (.neutral neA.neK) (.neutral nf.neK) (.neutral nf.neM)
        (eqrel.neToTerm nf.keqm)
  | pi D _ _ _ _ _ _ _ _ _ _ =>
      rcases htu with ⟨f, g, d, d', funcF, funcG, feqg, _, _, _⟩
      exact eqrel.redTerm D.reduction d.reduction d'.reduction
        .pi funcF.toWhnf funcG.toWhnf feqg

/-!
## Shape Elimination Lemmas (`Definition/LogicalRelation/ShapeView.agda` lines 58–108)
-/

/-- Elimination for `U` (`U-elim`). -/
theorem elimU {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context}
    (p : RedType eqrel l Γ .univ) : RedU .one Γ := by
  rcases p with ⟨rel, h⟩
  cases logRelShape_of_LogRelAt h with
  | U hU =>
      cases hU with
      | mk lt wf =>
          cases lt
          exact ⟨.zero, .zeroLT, wf⟩
  | nat D =>
      have h := whnfRedStar D.reduction .univ
      cases h
  | ne neA =>
      have h := whnfRedStar neA.D.reduction .univ
      subst h
      cases neA.neK
  | pi D =>
      have h := whnfRedStar D.reduction .univ
      cases h

/-- Elimination for `ℕ` (`ℕ-elim′`). -/
theorem elimNat' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (D : TypeStar Γ A .nat) (p : RedType eqrel l Γ A) : RedNat Γ A := by
  rcases p with ⟨rel, h⟩
  cases logRelShape_of_LogRelAt h with
  | U _ =>
      have h := whnfRedStar D .univ
      cases h
  | nat D' => exact D'
  | ne neA =>
      have h := whrDetStar ⟨D, .nat⟩ ⟨neA.D.reduction, .neutral neA.neK⟩
      subst h
      cases neA.neK
  | pi D' =>
      have h := whrDetStar ⟨D, .nat⟩ ⟨D'.reduction, .pi⟩
      cases h

theorem elimNat {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context}
    (p : RedType eqrel l Γ .nat) : RedNat Γ .nat :=
  elimNat' (.refl (escape p)) p

/-- Elimination for neutral types with explicit WHNF `K` (`ne-elim′`). -/
theorem elimNeAt' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A K : Term}
    (D : TypeStar Γ A K) (neK : Neutral K) (p : RedType eqrel l Γ A) : RedNeAt eqrel Γ A K := by
  rcases p with ⟨rel, h⟩
  cases logRelShape_of_LogRelAt h with
  | U _ =>
      have h := whnfRedStar D .univ
      subst h
      cases neK
  | nat D' =>
      have h := whrDetStar ⟨D'.reduction, .nat⟩ ⟨D, .neutral neK⟩
      subst h
      cases neK
  | @ne _ _ K₀ neA =>
      have hK : K₀ = K :=
        whrDetStar ⟨neA.D.reduction, .neutral neA.neK⟩ ⟨D, .neutral neK⟩
      subst hK
      exact neA
  | pi D' =>
      have h := whrDetStar ⟨D'.reduction, .pi⟩ ⟨D, .neutral neK⟩
      subst h
      cases neK

/-- Elimination for neutral types (`ne-elim′`). -/
theorem elimNe' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A K : Term}
    (D : TypeStar Γ A K) (neK : Neutral K) (p : RedType eqrel l Γ A) : RedNe eqrel Γ A := by
  have neA := elimNeAt' D neK p
  exact ⟨K, neA.D, neA.neK, neA.KeqK⟩

theorem elimNe {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {K : Term}
    (neK : Neutral K) (p : RedType eqrel l Γ K) : RedNe eqrel Γ K :=
  elimNe' (.refl (escape p)) neK p

/-- Elimination for `Π`-types with explicit domain `F` and codomain `G` (`Π-elim′`). -/
theorem elimPiAt' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A F G : Term}
    (D : TypeStar Γ A (.pi F G)) (p : RedType eqrel l Γ A) :
    ∃ l₀, RedPiAt eqrel l₀ Γ A F G := by
  rcases p with ⟨rel, h⟩
  cases logRelShape_of_LogRelAt h with
  | U _ =>
      have h := whnfRedStar D .univ
      cases h
  | nat D' =>
      have h := whrDetStar ⟨D'.reduction, .nat⟩ ⟨D, .pi⟩
      cases h
  | ne neA =>
      have h := whrDetStar ⟨D, .pi⟩ ⟨neA.D.reduction, .neutral neA.neK⟩
      subst h
      cases neA.neK
  | @pi l₀ _ _ F₀ G₀ D' hF hG AeqA relF relG hF_ex derivF hG_ex derivG Gext =>
      have hPi : Term.pi F₀ G₀ = Term.pi F G :=
        whrDetStar ⟨D'.reduction, .pi⟩ ⟨D, .pi⟩
      injection hPi with hF₀ hG₀
      subst hF₀ hG₀
      refine ⟨l₀, ⟨D', hF, hG, AeqA, ?_, ?_, ?_⟩⟩
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

/-- Elimination for `Π`-types (`Π-elim′`). -/
theorem elimPi' {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A F G : Term}
    (D : TypeStar Γ A (.pi F G)) (p : RedType eqrel l Γ A) :
    ∃ l₀, RedPi eqrel l₀ Γ A := by
  rcases elimPiAt' D p with ⟨l₀, piA⟩
  exact ⟨l₀, ⟨F, G, piA.D, piA.hF, piA.hG, piA.AeqA, piA.redF, piA.redG, piA.Gext⟩⟩

theorem elimPi {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {F G : Term}
    (p : RedType eqrel l Γ (.pi F G)) : ∃ l₀, RedPi eqrel l₀ Γ (.pi F G) :=
  elimPi' (.refl (escape p)) p

/-!
## Reflexivity (`Definition/LogicalRelation/Properties/Reflexivity.agda`)
-/

/-- Reflexivity of `NaturalProp` (`reflNatural-prop`). -/
theorem reflNaturalProp {eqrel : EqRelSet} {Γ : Context} {n : Term}
    (h : NaturalProp eqrel Γ n) : NaturalEqProp eqrel Γ n n :=
  @NaturalProp.rec eqrel Γ
    (fun t _ ↦ RedNatTermEq eqrel Γ t t)
    (fun n _ ↦ NaturalEqProp eqrel Γ n n)
    (fun t n d neqn _ ih ↦ .mk t t n n d d neqn ih)
    (fun _ ih ↦ .suc ih)
    .zero
    (fun nf ↦ .ne ⟨nf.neK, nf.neK, nf.keqk⟩)
    n h

theorem reflLogRel_step {eqrel : EqRelSet} {l : TypeLevel}
    {rec : ∀ (l' : TypeLevel), TypeLevelLT l' l → Context → Term → RedRel → Prop}
    (ihRec : ∀ (l' : TypeLevel) (hlt : TypeLevelLT l' l) {Γ A rel},
      rec l' hlt Γ A rel → rel.eqType A ∧ (∀ {t}, rel.hasTerm t → rel.eqTerm t t))
    {Γ : Context} {A : Term} {rel : RedRel}
    (h : LogRel eqrel l rec Γ A rel) :
    rel.eqType A ∧ (∀ {t}, rel.hasTerm t → rel.eqTerm t t) := by
  induction h with
  | @U _ l' hU =>
      refine ⟨rfl, ?_⟩
      rintro t ⟨A₀, d, typeA, AeqA, relt, ht⟩
      have ⟨hReflEq, _⟩ := ihRec l' hU.lt ht
      exact ⟨A₀, A₀, d, d, typeA, typeA, AeqA, relt, ht, ⟨relt, ht⟩, hReflEq⟩
  | nat D =>
      refine ⟨D.reduction, ?_⟩
      rintro t ⟨_, n, d, neqn, prop⟩
      exact .mk t t n n d d neqn (reflNaturalProp prop)
  | @ne _ _ K neA =>
      refine ⟨⟨K, neA.D, neA.neK, neA.KeqK⟩, ?_⟩
      rintro t ⟨k, d, nf⟩
      exact ⟨k, k, d, d, ⟨nf.neK, nf.neK, nf.keqk⟩⟩
  | @pi Γ A F G D _hF _hG AeqA relF relG hF_ex _derivF hG_ex _derivG _Gext ihF ihG =>
      refine ⟨⟨F, G, D.reduction, AeqA, ?_, ?_⟩, ?_⟩
      · intro ρ Δ hρ hΔ
        rcases hF_ex hρ hΔ with ⟨r, hr⟩
        exact ⟨r, hr, (ihF hρ hΔ r hr).1⟩
      · intro ρ Δ a hρ hΔ ha
        rcases hG_ex hρ hΔ ha with ⟨s, hs⟩
        exact ⟨s, hs, (ihG hρ hΔ ha s hs).1⟩
      · rintro t ht
        rcases ht with ⟨f, d, funcF, feqf, appEq, appTerm⟩
        refine ⟨f, f, d, d, funcF, funcF, feqf,
          ⟨f, d, funcF, feqf, appEq, appTerm⟩,
          ⟨f, d, funcF, feqf, appEq, appTerm⟩, ?_⟩
        intro ρ Δ a hρ hΔ ha
        have haa : RelFEqTerm relF ρ Δ a a := by
          rcases ha with ⟨r, hr, ha'⟩
          exact ⟨r, hr, (ihF hρ hΔ r hr).2 ha'⟩
        exact appEq hρ hΔ ha ha haa
  | @emb _ _ l' _ hlt hA => exact ihRec l' hlt hA

theorem reflLogRelAt {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term} {rel : RedRel}
    (h : LogRelAt eqrel l Γ A rel) :
    rel.eqType A ∧ (∀ {t}, rel.hasTerm t → rel.eqTerm t t) := by
  have h0 : ∀ {Γ A rel},
      LogRelAt eqrel .zero Γ A rel → rel.eqType A ∧ (∀ {t}, rel.hasTerm t → rel.eqTerm t t) :=
    fun h ↦ reflLogRel_step (l := .zero) (rec := logRelRec eqrel .zero) (fun _ hlt ↦ nomatch hlt) h
  cases l with
  | zero => exact h0 h
  | one =>
      exact reflLogRel_step (l := .one) (rec := logRelRec eqrel .one)
        (fun _ hlt _ _ _ h' ↦ by cases hlt; exact h0 h') h

/-- Reflexivity of reducible type equality (`reflEq`). -/
theorem reflEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (p : RedType eqrel l Γ A) : RedEq p A := by
  rcases p with ⟨rel, h⟩
  exact ⟨rel, h, (reflLogRelAt h).1⟩

/-- Reflexivity of reducible term equality (`reflEqTerm`). -/
theorem reflEqTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A t : Term}
    (p : RedType eqrel l Γ A) (ht : RedTerm p t) : RedTermEq p t t := by
  rcases ht with ⟨rel, h, ht⟩
  exact ⟨rel, h, (reflLogRelAt h).2 ht⟩

end LogrelMLTT
