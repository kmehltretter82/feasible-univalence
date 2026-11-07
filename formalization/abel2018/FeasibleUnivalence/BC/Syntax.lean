/-
  FeasibleUnivalence/BC/Syntax.lean

  Syntax and denotational semantics of the Bellantoni–Cook function algebra
  (S. Bellantoni and S. Cook, "A new recursion-theoretic characterization of the
  polytime functions", Computational Complexity 2 (1992) 97–110), over binary words.

  A program `f : Fn n m` denotes a function `f(x₁,…,xₙ ; y₁,…,yₘ)` with `n` *normal*
  and `m` *safe* arguments.  The constructors are exactly the BC base functions and the
  two BC schemes:

  * `zero`              : the constant `0` (the empty word `ε`), arity `(0;0)`;
  * `projN i`, `projS j` : the projections `π^{n,m}_j` onto a normal resp. safe argument;
  * `s0`, `s1`          : the successors `s₀(;a) = a0`, `s₁(;a) = a1`, arity `(0;1)`;
  * `pred`              : the predecessor `p(;a)` (drop the last bit), arity `(0;1)`;
  * `cond`              : the conditional `C(;a,b,c,d)`, arity `(0;4)`;
  * `comp h r t`        : safe composition
                          `f(x̄;ȳ) = h(r₁(x̄;),…,r_k(x̄;) ; t₁(x̄;ȳ),…,t_l(x̄;ȳ))`;
  * `srec g h₀ h₁`      : predicative (safe) recursion on notation
                          `f(ε,x̄;ȳ) = g(x̄;ȳ)`,
                          `f(sᵢ(w),x̄;ȳ) = hᵢ(w,x̄; f(w,x̄;ȳ), ȳ)`.

  **Representation conventions** (the only deviations from the 1992 paper, both standard
  for the word presentation of BC, cf. Heraud–Nowak ITP 2011):
  * The carrier is `Word = List Bool` rather than `ℕ` in binary.  The head of the list is
    the *last* (least significant) bit, so `sᵢ` is `cons` and `p` is `tail`.
  * Since words have no "leading zero" identification, the conditional has three
    branches: `C(;ε,b,c,d) = b`, `C(;a0,b,c,d) = c`, `C(;a1,b,c,d) = d`.
  * In `srec`, the recursive value is passed as the *first* safe argument of `hᵢ`.

  Arguments are passed as lists; `Fn n m` guarantees that every projection index is in
  range when the lists have the declared lengths.  The `Fin k → Fn n 0` arguments of
  `comp` are *finite tuples of BC subprograms* (syntax), not semantic functions: no
  constructor of `Fn` takes a Lean function on words.
-/

import FeasibleUnivalence.BC.Poly

namespace FeasibleUnivalence.BC

/-- Bellantoni–Cook programs with `n` normal and `m` safe arguments. -/
inductive Fn : Nat → Nat → Type where
  /-- The constant `0` (empty word). -/
  | zero : Fn 0 0
  /-- Projection onto the `i`-th normal argument. -/
  | projN {n m : Nat} (i : Fin n) : Fn n m
  /-- Projection onto the `j`-th safe argument. -/
  | projS {n m : Nat} (j : Fin m) : Fn n m
  /-- `s₀(;a) = a0` (`false :: a`). -/
  | s0 : Fn 0 1
  /-- `s₁(;a) = a1` (`true :: a`). -/
  | s1 : Fn 0 1
  /-- Predecessor `p(;a)`: drop the last bit (`a.tail`). -/
  | pred : Fn 0 1
  /-- Conditional `C(;a,b,c,d)`: `b` if `a = ε`, `c` if `a` ends in `0`, `d` if `a` ends in `1`. -/
  | cond : Fn 0 4
  /-- Safe composition `h(r̄(x̄;) ; t̄(x̄;ȳ))`. -/
  | comp {n m k l : Nat} (h : Fn k l) (rs : Fin k → Fn n 0) (ts : Fin l → Fn n m) : Fn n m
  /-- Predicative recursion on notation on the first normal argument. -/
  | srec {n m : Nat} (g : Fn n m) (h0 h1 : Fn (n + 1) (m + 1)) : Fn (n + 1) m

/-- Iteration underlying recursion on notation:
    `recIter g h ε = g`, `recIter g h (b :: w) = h b w (recIter g h w)`. -/
def recIter (g : Word) (h : Bool → Word → Word → Word) : Word → Word
  | [] => g
  | b :: w => h b w (recIter g h w)

@[simp] theorem recIter_nil (g : Word) (h : Bool → Word → Word → Word) :
    recIter g h [] = g := rfl
@[simp] theorem recIter_cons (g : Word) (h : Bool → Word → Word → Word) (b : Bool) (w : Word) :
    recIter g h (b :: w) = h b w (recIter g h w) := rfl

/-- The three-way conditional on words. -/
def condW (a b c d : Word) : Word :=
  match a with
  | [] => b
  | false :: _ => c
  | true :: _ => d

namespace Fn

/-- Denotational semantics: `f.eval xs ys = f(xs ; ys)`. -/
def eval : {n m : Nat} → Fn n m → List Word → List Word → Word
  | _, _, .zero, _, _ => []
  | _, _, .projN i, xs, _ => xs.getD i.val []
  | _, _, .projS j, _, ys => ys.getD j.val []
  | _, _, .s0, _, ys => false :: ys.getD 0 []
  | _, _, .s1, _, ys => true :: ys.getD 0 []
  | _, _, .pred, _, ys => (ys.getD 0 []).tail
  | _, _, .cond, _, ys => condW (ys.getD 0 []) (ys.getD 1 []) (ys.getD 2 []) (ys.getD 3 [])
  | _, _, .comp h rs ts, xs, ys =>
      h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)
  | _, _, .srec g h0 h1, xs, ys =>
      recIter (g.eval xs.tail ys)
        (fun b w r => if b then h1.eval (w :: xs.tail) (r :: ys) else h0.eval (w :: xs.tail) (r :: ys))
        (xs.headD [])

@[simp] theorem eval_zero (xs ys : List Word) : Fn.zero.eval xs ys = [] := by
  simp [eval]
@[simp] theorem eval_projN {n m : Nat} (i : Fin n) (xs ys : List Word) :
    (Fn.projN (m := m) i).eval xs ys = xs.getD i.val [] := by simp [eval]
@[simp] theorem eval_projS {n m : Nat} (j : Fin m) (xs ys : List Word) :
    (Fn.projS (n := n) j).eval xs ys = ys.getD j.val [] := by simp [eval]
@[simp] theorem eval_s0 (xs ys : List Word) : Fn.s0.eval xs ys = false :: ys.getD 0 [] := by
  simp [eval]
@[simp] theorem eval_s1 (xs ys : List Word) : Fn.s1.eval xs ys = true :: ys.getD 0 [] := by
  simp [eval]
@[simp] theorem eval_pred (xs ys : List Word) : Fn.pred.eval xs ys = (ys.getD 0 []).tail := by
  simp [eval]
@[simp] theorem eval_cond (xs ys : List Word) :
    Fn.cond.eval xs ys = condW (ys.getD 0 []) (ys.getD 1 []) (ys.getD 2 []) (ys.getD 3 []) := by
  simp [eval]
@[simp] theorem eval_comp {n m k l : Nat} (h : Fn k l) (rs : Fin k → Fn n 0)
    (ts : Fin l → Fn n m) (xs ys : List Word) :
    (Fn.comp h rs ts).eval xs ys =
      h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys) := by
  simp [eval]
theorem eval_srec {n m : Nat} (g : Fn n m) (h0 h1 : Fn (n + 1) (m + 1)) (xs ys : List Word) :
    (Fn.srec g h0 h1).eval xs ys =
      recIter (g.eval xs.tail ys)
        (fun b w r => if b then h1.eval (w :: xs.tail) (r :: ys) else h0.eval (w :: xs.tail) (r :: ys))
        (xs.headD []) := by
  simp [eval]

/-- Unfolding of `rec` on an explicit recursion argument `ε`. -/
@[simp] theorem eval_srec_nil {n m : Nat} (g : Fn n m) (h0 h1 : Fn (n + 1) (m + 1))
    (xs ys : List Word) :
    (Fn.srec g h0 h1).eval ([] :: xs) ys = g.eval xs ys := by
  simp [eval_srec]

/-- Unfolding of `rec` on an explicit recursion argument `s_b(w)`. -/
@[simp] theorem eval_srec_cons {n m : Nat} (g : Fn n m) (h0 h1 : Fn (n + 1) (m + 1))
    (b : Bool) (w : Word) (xs ys : List Word) :
    (Fn.srec g h0 h1).eval ((b :: w) :: xs) ys =
      (if b then h1 else h0).eval (w :: xs) ((Fn.srec g h0 h1).eval (w :: xs) ys :: ys) := by
  cases b <;> simp [eval_srec]

end Fn

/-- A word function is **BC-definable** if it is the denotation of a closed BC program
    with one normal and no safe argument. -/
def BCDefinable (f : Word → Word) : Prop :=
  ∃ prog : Fn 1 0, ∀ x : Word, prog.eval [x] [] = f x

end FeasibleUnivalence.BC
