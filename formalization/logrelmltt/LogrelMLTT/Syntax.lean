/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: mr-ohman/logrel-mltt, commit eb2b15ab1c4b45923025834d3bb798943cb44b8e,
Definition/Untyped.agda, extended with the Σ, Unit and Empty formers of
mr-ohman/logrel-mltt master, commit 9d6e290064962a1987c9e1a131c2fb967d6ef928.
These are raw terms; validity is a separate judgment.
-/
import Init

namespace LogrelMLTT

/-- Raw de Bruijn syntax for the source calculus with U, Π, ℕ, Σ (negative, with projections),
Unit (with η) and Empty. -/
inductive Term where
  | univ : Term
  | pi : Term → Term → Term
  | nat : Term
  | var : Nat → Term
  | lam : Term → Term
  | app : Term → Term → Term
  | zero : Term
  | succ : Term → Term
  | natrec : Term → Term → Term → Term → Term
  /-- Dependent sum `Σ A ▹ B`; `B` is a binder. -/
  | sigma : Term → Term → Term
  /-- Pair `prod t u`. -/
  | prod : Term → Term → Term
  | fst : Term → Term
  | snd : Term → Term
  | unit : Term
  | star : Term
  | empty : Term
  /-- `Emptyrec A e`. -/
  | emptyrec : Term → Term → Term
  deriving DecidableEq, Repr

/-- Newest-first representation of the source's snoc contexts: Γ ∙ A becomes A :: Γ. -/
abbrev Context := List Term

def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Renaming lifts under precisely the Pi codomain, lambda body, and recursor motive. -/
def rename (ρ : Nat → Nat) : Term → Term
  | .univ => .univ
  | .pi A B => .pi (rename ρ A) (rename (liftRen ρ) B)
  | .nat => .nat
  | .var x => .var (ρ x)
  | .lam t => .lam (rename (liftRen ρ) t)
  | .app t u => .app (rename ρ t) (rename ρ u)
  | .zero => .zero
  | .succ t => .succ (rename ρ t)
  | .natrec A z s n =>
      .natrec (rename (liftRen ρ) A) (rename ρ z) (rename ρ s) (rename ρ n)
  | .sigma A B => .sigma (rename ρ A) (rename (liftRen ρ) B)
  | .prod t u => .prod (rename ρ t) (rename ρ u)
  | .fst t => .fst (rename ρ t)
  | .snd t => .snd (rename ρ t)
  | .unit => .unit
  | .star => .star
  | .empty => .empty
  | .emptyrec A e => .emptyrec (rename ρ A) (rename ρ e)

/-- Syntactic weakenings from the source, retaining its inductive presentation. -/
inductive Wk where
  | id : Wk
  | step : Wk → Wk
  | lift : Wk → Wk
  deriving DecidableEq, Repr

def wkVar : Wk → Nat → Nat
  | .id, n => n
  | .step ρ, n => wkVar ρ n + 1
  | .lift _, 0 => 0
  | .lift ρ, n + 1 => wkVar ρ n + 1

def wk (ρ : Wk) : Term → Term
  | .univ => .univ
  | .pi A B => .pi (wk ρ A) (wk (.lift ρ) B)
  | .nat => .nat
  | .var x => .var (wkVar ρ x)
  | .lam t => .lam (wk (.lift ρ) t)
  | .app t u => .app (wk ρ t) (wk ρ u)
  | .zero => .zero
  | .succ t => .succ (wk ρ t)
  | .natrec A z s n =>
      .natrec (wk (.lift ρ) A) (wk ρ z) (wk ρ s) (wk ρ n)
  | .sigma A B => .sigma (wk ρ A) (wk (.lift ρ) B)
  | .prod t u => .prod (wk ρ t) (wk ρ u)
  | .fst t => .fst (wk ρ t)
  | .snd t => .snd (wk ρ t)
  | .unit => .unit
  | .star => .star
  | .empty => .empty
  | .emptyrec A e => .emptyrec (wk ρ A) (wk ρ e)

def wk1 : Term → Term := wk (.step .id)

def compWk : Wk → Wk → Wk
  | .id, ρ' => ρ'
  | .step ρ, ρ' => .step (compWk ρ ρ')
  | .lift ρ, .id => .lift ρ
  | .lift ρ, .step ρ' => .step (compWk ρ ρ')
  | .lift ρ, .lift ρ' => .lift (compWk ρ ρ')

abbrev Subst := Nat → Term

def liftSubst (σ : Subst) : Subst
  | 0 => .var 0
  | n + 1 => wk1 (σ n)

def subst (σ : Subst) : Term → Term
  | .univ => .univ
  | .pi A B => .pi (subst σ A) (subst (liftSubst σ) B)
  | .nat => .nat
  | .var x => σ x
  | .lam t => .lam (subst (liftSubst σ) t)
  | .app t u => .app (subst σ t) (subst σ u)
  | .zero => .zero
  | .succ t => .succ (subst σ t)
  | .natrec A z s n =>
      .natrec (subst (liftSubst σ) A) (subst σ z) (subst σ s) (subst σ n)
  | .sigma A B => .sigma (subst σ A) (subst (liftSubst σ) B)
  | .prod t u => .prod (subst σ t) (subst σ u)
  | .fst t => .fst (subst σ t)
  | .snd t => .snd (subst σ t)
  | .unit => .unit
  | .star => .star
  | .empty => .empty
  | .emptyrec A e => .emptyrec (subst σ A) (subst σ e)

def consSubst (σ : Subst) (a : Term) : Subst
  | 0 => a
  | n + 1 => σ n

def idSubst : Subst := Term.var

def sgSubst (a : Term) : Subst := consSubst idSubst a

def toSubst (ρ : Wk) : Subst := fun x ↦ .var (wkVar ρ x)

def headSubst (σ : Subst) : Term := σ 0

def tailSubst (σ : Subst) : Subst := fun n ↦ σ (n + 1)

def wk1Subst (σ : Subst) : Subst := fun n ↦ wk1 (σ n)

def compSubst (σ τ : Subst) : Subst := fun n ↦ subst σ (τ n)

def wkSubst (ρ : Wk) (σ : Subst) : Subst := fun n ↦ wk ρ (σ n)

def substWk (σ : Subst) (ρ : Wk) : Subst := fun n ↦ σ (wkVar ρ n)

/-- Replace index zero and remove its binder, corresponding to source t [ a ]. -/
def subst0 (t a : Term) : Term := subst (consSubst idSubst a) t

/-- Replace index zero while retaining the context, corresponding to source t [ a ]↑. -/
def substKeep (t a : Term) : Term := subst (consSubst (wk1Subst idSubst) a) t

/-- Nondependent arrow: source A ▹▹ B. -/
def arr (A B : Term) : Term := .pi A (wk1 B)

/-- Type of the step argument of natrec, in the context outside its motive binder. -/
def recStepType (F : Term) : Term :=
  .pi .nat (arr F (substKeep F (.succ (.var 0))))

inductive Neutral : Term → Prop where
  | var (n : Nat) : Neutral (.var n)
  | app {k u} : Neutral k → Neutral (.app k u)
  | natrec {C z s k} : Neutral k → Neutral (.natrec C z s k)
  | fst {k} : Neutral k → Neutral (.fst k)
  | snd {k} : Neutral k → Neutral (.snd k)
  | emptyrec {A k} : Neutral k → Neutral (.emptyrec A k)

inductive Whnf : Term → Prop where
  | univ : Whnf .univ
  | pi {A B} : Whnf (.pi A B)
  | nat : Whnf .nat
  | lam {t} : Whnf (.lam t)
  | zero : Whnf .zero
  | succ {t} : Whnf (.succ t)
  | sigma {A B} : Whnf (.sigma A B)
  | unit : Whnf .unit
  | empty : Whnf .empty
  | prod {t u} : Whnf (.prod t u)
  | star : Whnf .star
  | neutral {n} : Neutral n → Whnf n

/-- Source view Natural: the weak-head forms of natural-number terms. -/
inductive NaturalView : Term → Prop where
  | zero : NaturalView .zero
  | succ {t} : NaturalView (.succ t)
  | neutral {n} : Neutral n → NaturalView n

/-- Source view Type: small types in weak-head form; the universe is excluded. -/
inductive SmallTypeView : Term → Prop where
  | pi {A B} : SmallTypeView (.pi A B)
  | nat : SmallTypeView .nat
  | sigma {A B} : SmallTypeView (.sigma A B)
  | unit : SmallTypeView .unit
  | empty : SmallTypeView .empty
  | neutral {n} : Neutral n → SmallTypeView n

/-- Source view Function: weak-head forms of function terms. -/
inductive FunctionView : Term → Prop where
  | lam {t} : FunctionView (.lam t)
  | neutral {n} : Neutral n → FunctionView n

/-- Source view Product (logrel-mltt master): weak-head forms of pair terms. -/
inductive ProductView : Term → Prop where
  | prod {t u} : ProductView (.prod t u)
  | neutral {n} : Neutral n → ProductView n

theorem NaturalView.toWhnf {n : Term} : NaturalView n → Whnf n
  | .zero => .zero
  | .succ => .succ
  | .neutral h => .neutral h

theorem SmallTypeView.toWhnf {A : Term} : SmallTypeView A → Whnf A
  | .pi => .pi
  | .nat => .nat
  | .sigma => .sigma
  | .unit => .unit
  | .empty => .empty
  | .neutral h => .neutral h

theorem FunctionView.toWhnf {f : Term} : FunctionView f → Whnf f
  | .lam => .lam
  | .neutral h => .neutral h

theorem ProductView.toWhnf {p : Term} : ProductView p → Whnf p
  | .prod => .prod
  | .neutral h => .neutral h

theorem Neutral.rename {t : Term} (ρ : Nat → Nat) : Neutral t → Neutral (LogrelMLTT.rename ρ t)
  | .var n => .var (ρ n)
  | .app h => .app (h.rename ρ)
  | .natrec h => .natrec (h.rename ρ)
  | .fst h => .fst (h.rename ρ)
  | .snd h => .snd (h.rename ρ)
  | .emptyrec h => .emptyrec (h.rename ρ)

theorem Neutral.wk {t : Term} (ρ : Wk) : Neutral t → Neutral (LogrelMLTT.wk ρ t)
  | .var n => .var (wkVar ρ n)
  | .app h => .app (h.wk ρ)
  | .natrec h => .natrec (h.wk ρ)
  | .fst h => .fst (h.wk ρ)
  | .snd h => .snd (h.wk ρ)
  | .emptyrec h => .emptyrec (h.wk ρ)

theorem Whnf.wk {t : Term} (ρ : Wk) : Whnf t → Whnf (LogrelMLTT.wk ρ t)
  | .univ => .univ
  | .pi => .pi
  | .nat => .nat
  | .lam => .lam
  | .zero => .zero
  | .succ => .succ
  | .sigma => .sigma
  | .unit => .unit
  | .empty => .empty
  | .prod => .prod
  | .star => .star
  | .neutral h => .neutral (h.wk ρ)

theorem NaturalView.wk {t : Term} (ρ : Wk) : NaturalView t → NaturalView (LogrelMLTT.wk ρ t)
  | .zero => .zero
  | .succ => .succ
  | .neutral h => .neutral (h.wk ρ)

theorem SmallTypeView.wk {t : Term} (ρ : Wk) : SmallTypeView t → SmallTypeView (LogrelMLTT.wk ρ t)
  | .pi => .pi
  | .nat => .nat
  | .sigma => .sigma
  | .unit => .unit
  | .empty => .empty
  | .neutral h => .neutral (h.wk ρ)

theorem FunctionView.wk {t : Term} (ρ : Wk) : FunctionView t → FunctionView (LogrelMLTT.wk ρ t)
  | .lam => .lam
  | .neutral h => .neutral (h.wk ρ)

theorem ProductView.wk {t : Term} (ρ : Wk) : ProductView t → ProductView (LogrelMLTT.wk ρ t)
  | .prod => .prod
  | .neutral h => .neutral (h.wk ρ)

end LogrelMLTT
