/-
  FeasibleUnivalence/BC/StackProg.lean

  Structured stack programs: an *intermediate compilation language* between
  Bellantoni–Cook programs and Turing machines (it is **not** used to define `FP`).

  A program manipulates finitely many stacks of bits (`Stacks := Nat → Word`, the head of
  a word being the top of the stack) with unit-cost `push`/`pop`, a three-way test on the
  top of a stack, sequencing, and a `while`-loop that runs while a stack is nonempty.
  The big-step judgment `Exec P σ c σ'` says that `P` started on `σ` terminates in `σ'`
  with cost `c`.
-/

import FeasibleUnivalence.BC.Poly

namespace FeasibleUnivalence.BC

/-- A finite family of bit stacks (all but finitely many are irrelevant to any program). -/
abbrev Stacks := Nat → Word

/-- Overwrite one stack. -/
def Stacks.set (σ : Stacks) (i : Nat) (w : Word) : Stacks :=
  fun j => if j = i then w else σ j

@[simp] theorem Stacks.set_same (σ : Stacks) (i : Nat) (w : Word) : σ.set i w i = w := by
  simp [Stacks.set]

theorem Stacks.set_other (σ : Stacks) {i j : Nat} (w : Word) (h : j ≠ i) :
    σ.set i w j = σ j := by
  simp [Stacks.set, h]

/-- Initial stacks on input `x`: stack `0` holds `x` (first bit on top), all others empty. -/
def initStacks (x : Word) : Stacks :=
  fun i => if i = 0 then x else []

/-- Structured stack programs. -/
inductive Stmt : Type where
  | skip
  /-- Push bit `b` on stack `i`. -/
  | push (i : Nat) (b : Bool)
  /-- Pop stack `i` (no effect if empty). -/
  | pop (i : Nat)
  | seq (s t : Stmt)
  /-- Branch on the top of stack `i` (empty / `false` / `true`) without popping. -/
  | ifTop (i : Nat) (sE s0 s1 : Stmt)
  /-- `while` stack `i` is nonempty `do body`. -/
  | whileNE (i : Nat) (body : Stmt)
  deriving DecidableEq, Repr

/-- Big-step semantics with cost: `Exec P σ c σ'`. -/
inductive Exec : Stmt → Stacks → Nat → Stacks → Prop where
  | skip (σ : Stacks) : Exec .skip σ 0 σ
  | push (i : Nat) (b : Bool) (σ : Stacks) : Exec (.push i b) σ 1 (σ.set i (b :: σ i))
  | pop (i : Nat) (σ : Stacks) : Exec (.pop i) σ 1 (σ.set i (σ i).tail)
  | seq {s t : Stmt} {σ₁ σ₂ σ₃ : Stacks} {c₁ c₂ : Nat} :
      Exec s σ₁ c₁ σ₂ → Exec t σ₂ c₂ σ₃ → Exec (.seq s t) σ₁ (c₁ + c₂) σ₃
  | ifE {i : Nat} {sE s0 s1 : Stmt} {σ σ' : Stacks} {c : Nat} :
      σ i = [] → Exec sE σ c σ' → Exec (.ifTop i sE s0 s1) σ (c + 1) σ'
  | if0 {i : Nat} {sE s0 s1 : Stmt} {σ σ' : Stacks} {c : Nat} {w : Word} :
      σ i = false :: w → Exec s0 σ c σ' → Exec (.ifTop i sE s0 s1) σ (c + 1) σ'
  | if1 {i : Nat} {sE s0 s1 : Stmt} {σ σ' : Stacks} {c : Nat} {w : Word} :
      σ i = true :: w → Exec s1 σ c σ' → Exec (.ifTop i sE s0 s1) σ (c + 1) σ'
  | whileDone {i : Nat} {body : Stmt} {σ : Stacks} :
      σ i = [] → Exec (.whileNE i body) σ 1 σ
  | whileStep {i : Nat} {body : Stmt} {σ σ' σ'' : Stacks} {c c' : Nat} :
      σ i ≠ [] → Exec body σ c σ' → Exec (.whileNE i body) σ' c' σ'' →
      Exec (.whileNE i body) σ (c + c' + 1) σ''

end FeasibleUnivalence.BC
