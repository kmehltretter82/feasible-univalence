import LogrelMLTT.Decidable

/-!
# Fuel-Free Deciders for Judgmental Equality

`theorem_4_12_computational` (in `LogrelMLTT.Decidable`) proves that, on well-formed inputs,
the fuel-bounded checkers `compareTypeUp` and `compareTermUp` succeed at *some* fuel and that
*every* successful run returns the correct answer. This module turns that result into
`Decidable` instances that do not ask the caller for a fuel budget:

* `findNat` — a constructive unbounded search for the least `n` satisfying a decidable
  predicate, given a proof (in `Prop`) that some witness exists. It is defined by
  well-founded recursion on the "not yet found" relation, so it needs neither Mathlib's
  `Nat.find` nor `Classical.choice`.
* `decTypeEq`, `decTermEq` — deciders for `TypeEq` / `TermEq` on well-formed inputs.
* `decideTypeEq`, `decideTermEq` — the corresponding `Bool`-valued functions, with
  correctness theorems `decideTypeEq_iff`, `decideTermEq_iff`.
-/

namespace LogrelMLTT

/-! ## Constructive unbounded search -/

namespace Search

variable {p : Nat → Prop}

/-- Search state: the next candidate `n`, together with the invariant that no smaller number
satisfies `p`. The existence proof `h` is a type index so that the well-founded relation below
can depend on it. -/
structure State (p : Nat → Prop) (_h : ∃ n, p n) where
  n : Nat
  below : ∀ k, k < n → ¬ p k

/-- One search step: `a` is the successor of `b` and `b.n` failed. -/
def Next (p : Nat → Prop) (h : ∃ n, p n) (a b : State p h) : Prop :=
  a.n = b.n + 1 ∧ ¬ p b.n

private theorem acc_of_dist (h : ∃ n, p n) (N : Nat) (hN : p N) :
    ∀ d (s : State p h), N - s.n = d → Acc (Next p h) s := by
  intro d
  induction d with
  | zero =>
    intro s hd
    refine ⟨s, fun a ha => ?_⟩
    exfalso
    rcases Nat.lt_or_ge N s.n with hlt | hge
    · exact s.below N hlt hN
    · have : s.n = N := by omega
      exact ha.2 (this ▸ hN)
  | succ d ih =>
    intro s hd
    refine ⟨s, fun a ha => ih a ?_⟩
    rw [ha.1]
    omega

theorem wf (h : ∃ n, p n) : WellFounded (Next p h) := by
  rcases h with ⟨N, hN⟩
  exact ⟨fun s => acc_of_dist ⟨N, hN⟩ N hN (N - s.n) s rfl⟩

instance (h : ∃ n, p n) : WellFoundedRelation (State p h) := ⟨Next p h, wf h⟩

/-- Search upward from a state for a witness. -/
def go [DecidablePred p] (h : ∃ n, p n) (s : State p h) : { m // p m ∧ ∀ k, k < m → ¬ p k } :=
  if hs : p s.n then
    ⟨s.n, hs, s.below⟩
  else
    go h ⟨s.n + 1, fun k hk => by
      rcases Nat.lt_or_ge k s.n with hlt | hge
      · exact s.below k hlt
      · have : k = s.n := by omega
        exact this ▸ hs⟩
termination_by s
decreasing_by exact ⟨rfl, hs⟩

end Search

/-- The least natural number satisfying a decidable predicate, given a proof that one exists.
Constructive: uses only well-founded recursion. -/
def findNat {p : Nat → Prop} [DecidablePred p] (h : ∃ n, p n) :
    { m // p m ∧ ∀ k, k < m → ¬ p k } :=
  Search.go h ⟨0, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩

/-! ## Deciders for judgmental equality -/

/-- Decide judgmental type equality of well-formed types, without a fuel argument. -/
def decTypeEq {Γ : Context} {A B : Term} (hA : TypeWf Γ A) (hB : TypeWf Γ B) :
    Decidable (TypeEq Γ A B) :=
  have hspec := compareTypeUp_decides_typeEq hA hB
  have hex : ∃ fuel, (compareTypeUp fuel Γ A B).isSome = true := by
    rcases hspec.1 with ⟨fuel, b, hrun⟩
    exact ⟨fuel, by rw [hrun]; rfl⟩
  let fuel := (findNat hex).1
  match hrun : compareTypeUp fuel Γ A B with
  | some true => isTrue ((hspec.2 fuel true hrun).mp rfl)
  | some false => isFalse (fun hEq => Bool.noConfusion ((hspec.2 fuel false hrun).mpr hEq))
  | none => absurd (findNat hex).2.1 (by simp [fuel, hrun])

/-- Decide judgmental term equality of terms of the same type, without a fuel argument. -/
def decTermEq {Γ : Context} {t u A : Term} (ht : HasType Γ t A) (hu : HasType Γ u A) :
    Decidable (TermEq Γ t u A) :=
  have hspec := compareTermUp_decides_termEq ht hu
  have hex : ∃ fuel, (compareTermUp fuel Γ t u A).isSome = true := by
    rcases hspec.1 with ⟨fuel, b, hrun⟩
    exact ⟨fuel, by rw [hrun]; rfl⟩
  let fuel := (findNat hex).1
  match hrun : compareTermUp fuel Γ t u A with
  | some true => isTrue ((hspec.2 fuel true hrun).mp rfl)
  | some false => isFalse (fun hEq => Bool.noConfusion ((hspec.2 fuel false hrun).mpr hEq))
  | none => absurd (findNat hex).2.1 (by simp [fuel, hrun])

/-- Boolean type-equality checker for well-formed types (no fuel argument). -/
def decideTypeEq {Γ : Context} {A B : Term} (hA : TypeWf Γ A) (hB : TypeWf Γ B) : Bool :=
  @decide _ (decTypeEq hA hB)

/-- Boolean term-equality checker for well-typed terms (no fuel argument). -/
def decideTermEq {Γ : Context} {t u A : Term} (ht : HasType Γ t A) (hu : HasType Γ u A) : Bool :=
  @decide _ (decTermEq ht hu)

theorem decideTypeEq_iff {Γ : Context} {A B : Term} (hA : TypeWf Γ A) (hB : TypeWf Γ B) :
    decideTypeEq hA hB = true ↔ TypeEq Γ A B :=
  @decide_eq_true_iff _ (decTypeEq hA hB)

theorem decideTermEq_iff {Γ : Context} {t u A : Term} (ht : HasType Γ t A) (hu : HasType Γ u A) :
    decideTermEq ht hu = true ↔ TermEq Γ t u A :=
  @decide_eq_true_iff _ (decTermEq ht hu)

/-- Fuel-free form of Theorem 4.12: judgmental type and term equality are decidable
(as `Decidable` data, not merely `P ∨ ¬ P`) on well-formed inputs. -/
def theorem_4_12_decidable :
    (∀ (Γ : Context) (A B : Term), TypeWf Γ A → TypeWf Γ B → Decidable (TypeEq Γ A B)) ×
    (∀ (Γ : Context) (t u A : Term), HasType Γ t A → HasType Γ u A →
      Decidable (TermEq Γ t u A)) :=
  ⟨fun _ _ _ hA hB => decTypeEq hA hB, fun _ _ _ _ ht hu => decTermEq ht hu⟩

end LogrelMLTT
