/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean implementation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.
-/
import LogrelMLTT.Syntax

/-!
# Executable bounded conversion for the 2018 lambda-Pi-U-N calculus

This is a candidate computational implementation of the six comparison judgments in
Abel–Öhman–Vezzosi (POPL 2018), Figure 6, and the v2.1 Agda artifact
`Definition.Conversion`. Correctness and sufficient fuel on well-formed inputs
are proof obligations, not assumptions of these definitions.

The fuel bounds recursive call depth, not the number of reduction steps or runtime.
Each function is total and executable. `none` means no answer within this budget;
on malformed raw terms it can also indicate a stuck operation. Source correctness
claims only concern well-formed inputs. `some false` is a negative comparison.

Neutral comparisons use `Option (Option Term)`: outer `none` is lack of an answer,
`some none` is a negative comparison, and `some (some A)` reports an inferred type.
That type is a chosen representative, not every type permitted by conversion in
the relational variable rule. Compare successful neutral outputs up to conversion.
-/

namespace LogrelMLTT

/-- Syntactic neutral-head test, with precisely the source's neutral constructors. -/
def neutralHead : Term → Bool
  | .var _ => true
  | .app k _ => neutralHead k
  | .natrec _ _ _ k => neutralHead k
  | .fst k => neutralHead k
  | .snd k => neutralHead k
  | .emptyrec _ k => neutralHead k
  | .idrec _ _ _ _ _ k => neutralHead k
  | _ => false

/-- Recover a variable's declared type, weakening once for every traversed binder. -/
def lookupType : Context → Nat → Option Term
  | [], _ => none
  | A :: _, 0 => some (wk1 A)
  | _ :: Γ, x + 1 => (lookupType Γ x).map wk1

/-- Bounded head evaluation. No reduction occurs inside lambda bodies, pairs, or successors. -/
def whnfFuel : Nat → Term → Option Term
  | 0, _ => none
  | fuel + 1, .app f a => do
      let f' ← whnfFuel fuel f
      match f' with
      | .lam body => whnfFuel fuel (subst0 body a)
      | _ => if neutralHead f' then some (.app f' a) else none
  | fuel + 1, .natrec A z s n => do
      let n' ← whnfFuel fuel n
      match n' with
      | .zero => whnfFuel fuel z
      | .succ k => whnfFuel fuel (.app (.app s k) (.natrec A z s k))
      | _ => if neutralHead n' then some (.natrec A z s n') else none
  | fuel + 1, .fst p => do
      let p' ← whnfFuel fuel p
      match p' with
      | .prod a _ => whnfFuel fuel a
      | _ => if neutralHead p' then some (.fst p') else none
  | fuel + 1, .snd p => do
      let p' ← whnfFuel fuel p
      match p' with
      | .prod _ b => whnfFuel fuel b
      | _ => if neutralHead p' then some (.snd p') else none
  | fuel + 1, .emptyrec A e => do
      let e' ← whnfFuel fuel e
      if neutralHead e' then some (.emptyrec A e') else none
  | fuel + 1, .idrec A P r t u h => do
      let h' ← whnfFuel fuel h
      match h' with
      | .rfl => whnfFuel fuel r
      | _ => if neutralHead h' then some (.idrec A P r t u h') else none
  | _ + 1, t => some t

mutual
  /-- Compare neutral heads and infer a representative type, before head normalization. -/
  def compareNeutralUp : Nat → Context → Term → Term → Option (Option Term)
    | 0, _, _, _ => none
    | _ + 1, Γ, .var x, .var y =>
        if x == y then some (lookupType Γ x) else some none
    | fuel + 1, Γ, .app k t, .app l v => do
        let inferred ← compareNeutralDown fuel Γ k l
        match inferred with
        | some (.pi F G) =>
            let equal ← compareTermUp fuel Γ t v F
            if equal then some (some (subst0 G t)) else some none
        | _ => some none
    | fuel + 1, Γ, .natrec F a₀ h k, .natrec G b₀ g l => do
        let motives ← compareTypeUp fuel (.nat :: Γ) F G
        if !motives then return none
        let bases ← compareTermUp fuel Γ a₀ b₀ (subst0 F .zero)
        if !bases then return none
        let steps ← compareTermUp fuel Γ h g (recStepType F)
        if !steps then return none
        let inferred ← compareNeutralDown fuel Γ k l
        match inferred with
        | some .nat => some (some (subst0 F k))
        | _ => some none
    | fuel + 1, Γ, .fst p, .fst r => do
        let inferred ← compareNeutralDown fuel Γ p r
        match inferred with
        | some (.sigma F _) => some (some F)
        | _ => some none
    | fuel + 1, Γ, .snd p, .snd r => do
        let inferred ← compareNeutralDown fuel Γ p r
        match inferred with
        | some (.sigma _ G) => some (some (subst0 G (.fst p)))
        | _ => some none
    | fuel + 1, Γ, .emptyrec F k, .emptyrec G l => do
        let motives ← compareTypeUp fuel Γ F G
        if !motives then return none
        let inferred ← compareNeutralDown fuel Γ k l
        match inferred with
        | some .empty => some (some F)
        | _ => some none
    | fuel + 1, Γ, .idrec A P r t u h, .idrec A' P' r' t' u' h' => do
        let types ← compareTypeUp fuel Γ A A'
        if !types then return none
        let lhsEq ← compareTermUp fuel Γ t t' A
        if !lhsEq then return none
        let motives ← compareTypeUp fuel (.id (wk1 A) (wk1 t) (.var 0) :: A :: Γ) P P'
        if !motives then return none
        let branches ← compareTermUp fuel Γ r r' (subst2 P t .rfl)
        if !branches then return none
        let rhsEq ← compareTermUp fuel Γ u u' A
        if !rhsEq then return none
        let inferred ← compareNeutralDown fuel Γ h h'
        match inferred with
        | some (.id _ _ _) => some (some (subst2 P u h))
        | _ => some none
    | _ + 1, _, _, _ => some none

  /-- Compare neutrals and head-normalize the inferred type. -/
  def compareNeutralDown : Nat → Context → Term → Term → Option (Option Term)
    | 0, _, _, _ => none
    | fuel + 1, Γ, k, l => do
        let inferred ← compareNeutralUp fuel Γ k l
        match inferred with
        | none => some none
        | some A => do
            let B ← whnfFuel fuel A
            some (some B)

  /-- Compare arbitrary well-formed types by head evaluation followed by comparison. -/
  def compareTypeUp : Nat → Context → Term → Term → Option Bool
    | 0, _, _, _ => none
    | fuel + 1, Γ, A, B => do
        let A' ← whnfFuel fuel A
        let B' ← whnfFuel fuel B
        compareTypeDown fuel Γ A' B'

  /-- Compare weak-head type forms; well-formedness is a premise of correctness. -/
  def compareTypeDown : Nat → Context → Term → Term → Option Bool
    | 0, _, _, _ => none
    | _ + 1, _, .univ, .univ => some true
    | _ + 1, _, .nat, .nat => some true
    | _ + 1, _, .empty, .empty => some true
    | _ + 1, _, .unit, .unit => some true
    | fuel + 1, Γ, .pi F G, .pi H E => do
        let domains ← compareTypeUp fuel Γ F H
        if !domains then return false
        compareTypeUp fuel (F :: Γ) G E
    | fuel + 1, Γ, .sigma F G, .sigma H E => do
        let domains ← compareTypeUp fuel Γ F H
        if !domains then return false
        compareTypeUp fuel (F :: Γ) G E
    | fuel + 1, Γ, .id A t u, .id A' t' u' => do
        let types ← compareTypeUp fuel Γ A A'
        if !types then return false
        let lhsEq ← compareTermUp fuel Γ t t' A
        if !lhsEq then return false
        compareTermUp fuel Γ u u' A
    | fuel + 1, Γ, K, L =>
        if neutralHead K && neutralHead L then do
          let inferred ← compareNeutralDown fuel Γ K L
          match inferred with
          | some .univ => some true
          | _ => some false
        else some false

  /-- Head-evaluate the expected type and both terms before type-directed comparison. -/
  def compareTermUp : Nat → Context → Term → Term → Term → Option Bool
    | 0, _, _, _, _ => none
    | fuel + 1, Γ, t, u, A => do
        let B ← whnfFuel fuel A
        let t' ← whnfFuel fuel t
        let u' ← whnfFuel fuel u
        compareTermDown fuel Γ t' u' B

  /-- Type-directed comparison, including eta expansion at dependent function, pair, and unit types. -/
  def compareTermDown : Nat → Context → Term → Term → Term → Option Bool
    | 0, _, _, _, _ => none
    | fuel + 1, Γ, t, u, .univ => compareTypeDown fuel Γ t u
    | _ + 1, _, .zero, .zero, .nat => some true
    | fuel + 1, Γ, .succ m, .succ n, .nat => compareTermUp fuel Γ m n .nat
    | fuel + 1, Γ, k, l, .nat =>
        if neutralHead k && neutralHead l then do
          let inferred ← compareNeutralDown fuel Γ k l
          match inferred with
          | some .nat => some true
          | _ => some false
        else some false
    | fuel + 1, Γ, k, l, .empty =>
        if neutralHead k && neutralHead l then do
          let inferred ← compareNeutralDown fuel Γ k l
          match inferred with
          | some .empty => some true
          | _ => some false
        else some false
    | _ + 1, _, _, _, .unit => some true
    | fuel + 1, Γ, f, g, .pi F G =>
        compareTermUp fuel (F :: Γ) (.app (wk1 f) (.var 0))
          (.app (wk1 g) (.var 0)) G
    | fuel + 1, Γ, p, r, .sigma F G => do
        let fstEq ← compareTermUp fuel Γ (.fst p) (.fst r) F
        if !fstEq then return false
        compareTermUp fuel Γ (.snd p) (.snd r) (subst0 G (.fst p))
    | _ + 1, _, .rfl, .rfl, .id _ _ _ => some true
    | fuel + 1, Γ, k, l, .id _ _ _ =>
        if neutralHead k && neutralHead l then do
          let inferred ← compareNeutralDown fuel Γ k l
          some inferred.isSome
        else some false
    | fuel + 1, Γ, k, l, N =>
        if neutralHead N && neutralHead k && neutralHead l then do
          let inferred ← compareNeutralDown fuel Γ k l
          -- Source ne-ins deliberately does not compare the inferred type to N.
          some inferred.isSome
        else some false
end

end LogrelMLTT
