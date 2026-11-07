/-
  FeasibleUnivalence/BC/Poly.lean

  Syntactic univariate polynomials with natural-number coefficients, used as explicit
  time and size certificates throughout the Bellantoni–Cook library.  Polynomials are
  *syntax*; certificates are computed from program syntax by structural recursion and
  only evaluated afterwards.
-/

namespace FeasibleUnivalence.BC

/-- Binary words `{0,1}*`, represented as `List Bool`.  In Bellantoni–Cook notation the
    head of the list is the *least significant* (last-appended) bit, so `s₀ a = false :: a`,
    `s₁ a = true :: a` and the predecessor `p` is `List.tail`. -/
abbrev Word := List Bool

/-- Syntax of univariate polynomials with natural-number coefficients (`ℕ[X]`),
    equipped with explicit formal composition (`comp`). -/
inductive Poly : Type where
  | const (c : Nat)
  | var
  | add (p q : Poly)
  | mul (p q : Poly)
  | comp (p q : Poly)
  deriving DecidableEq, Repr

namespace Poly

/-- Evaluate a polynomial `p : Poly` at `n : Nat`. -/
def eval : Poly → Nat → Nat
  | .const c, _ => c
  | .var, n => n
  | .add p q, n => p.eval n + q.eval n
  | .mul p q, n => p.eval n * q.eval n
  | .comp p q, n => p.eval (q.eval n)

@[simp] theorem eval_const (c n : Nat) : (Poly.const c).eval n = c := rfl
@[simp] theorem eval_var (n : Nat) : Poly.var.eval n = n := rfl
@[simp] theorem eval_add (p q : Poly) (n : Nat) :
    (Poly.add p q).eval n = p.eval n + q.eval n := rfl
@[simp] theorem eval_mul (p q : Poly) (n : Nat) :
    (Poly.mul p q).eval n = p.eval n * q.eval n := rfl
@[simp] theorem eval_comp (p q : Poly) (n : Nat) :
    (Poly.comp p q).eval n = p.eval (q.eval n) := rfl

/-- Pointwise dominance of polynomials on all natural numbers. -/
def le (p q : Poly) : Prop :=
  ∀ n : Nat, p.eval n ≤ q.eval n

/-- Formal degree upper bound of a polynomial. -/
def degree : Poly → Nat
  | .const _ => 0
  | .var => 1
  | .add p q => max p.degree q.degree
  | .mul p q => p.degree + q.degree
  | .comp p q => p.degree * q.degree

/-- Every `Poly` has natural-number coefficients and is therefore monotone. -/
theorem eval_mono (p : Poly) {n m : Nat} (h : n ≤ m) : p.eval n ≤ p.eval m := by
  induction p generalizing n m with
  | const c => exact Nat.le_refl c
  | var => exact h
  | add p q ihp ihq => exact Nat.add_le_add (ihp h) (ihq h)
  | mul p q ihp ihq => exact Nat.mul_le_mul (ihp h) (ihq h)
  | comp p q ihp ihq => exact ihp (ihq h)

theorem le_refl (p : Poly) : p.le p :=
  fun _ ↦ Nat.le_refl _

theorem le_trans {p q r : Poly} (h₁ : p.le q) (h₂ : q.le r) : p.le r :=
  fun n ↦ Nat.le_trans (h₁ n) (h₂ n)

end Poly

end FeasibleUnivalence.BC
