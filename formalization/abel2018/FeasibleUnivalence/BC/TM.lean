/-
  FeasibleUnivalence/BC/TM.lean

  An independent machine model for `FP`: deterministic multi-tape Turing machines over a
  finite tape alphabet, with binary input and output.

  * A machine has `k ≥ 1` tapes (tape `0` is the input/output tape), `Q ≥ 1` states
    (state `0` is initial) and tape alphabet `Fin G` with `G ≥ 3`; symbol `0` is the blank,
    symbols `1` and `2` encode the bits `0` and `1`.
  * The transition function `δ q (a₀,…,a_{k-1})` either halts (`none`) or yields a new
    state, a symbol to write on every tape, and a head move `L`/`R`/`S` for every tape.
    Since its domain `Fin Q × (Fin k → Fin G)` is finite, `δ` is a finite table.
  * Tapes are zippers `⟨left, head, right⟩` (with `left` and `right` listed outwards from
    the head).  Moving keeps the representation canonical: a blank is never stored at the
    outer end of `left`/`right`, so a tape is exactly a finitely supported map `ℤ → Fin G`
    together with a head position.
  * Input convention: tape `0` holds the input bits with the head on the first one (or on
    a blank if the input is empty); all other tapes are blank.
  * Output convention: when `M` halts, the output is the maximal word of bit symbols
    read on tape `0` from the head cell rightwards.
  * Time is the number of transitions taken until `δ` returns `none`.

  `FP f` holds iff some machine computes `f` and halts within `p(|x|)` steps for an
  explicit syntactic polynomial `p : Poly`.
-/

import FeasibleUnivalence.BC.Poly

namespace FeasibleUnivalence.BC

/-- Head moves. -/
inductive Dir : Type where
  | L
  | R
  | S
  deriving DecidableEq, Repr

/-- A Turing machine tape as a zipper: `left` (nearest cell first), `head`, `right`
    (nearest cell first). -/
structure Tape (Γ : Type) where
  left : List Γ
  head : Γ
  right : List Γ
  deriving DecidableEq, Repr

namespace Tape

variable {Γ : Type} [DecidableEq Γ]

/-- Push a cell onto one side of the zipper, dropping it if it would be an outermost
    blank (keeps the representation canonical). -/
def consB (blank a : Γ) : List Γ → List Γ
  | [] => if a = blank then [] else [a]
  | l => a :: l

/-- Overwrite the head cell. -/
def write (t : Tape Γ) (a : Γ) : Tape Γ := { t with head := a }

/-- Move the head. -/
def move (blank : Γ) : Dir → Tape Γ → Tape Γ
  | .L, ⟨[], h, r⟩ => ⟨[], blank, consB blank h r⟩
  | .L, ⟨a :: l, h, r⟩ => ⟨l, a, consB blank h r⟩
  | .R, ⟨l, h, []⟩ => ⟨consB blank h l, blank, []⟩
  | .R, ⟨l, h, a :: r⟩ => ⟨consB blank h l, a, r⟩
  | .S, t => t

end Tape

/-- Deterministic multi-tape Turing machines with tape alphabet `Fin G`. -/
structure TM where
  /-- Number of tapes; tape `0` is the input/output tape. -/
  k : Nat
  /-- Number of states; state `0` is the initial state. -/
  Q : Nat
  /-- Size of the tape alphabet `Fin G`: `0` = blank, `1` = bit `0`, `2` = bit `1`. -/
  G : Nat
  hk : 0 < k
  hQ : 0 < Q
  hG : 2 < G
  /-- Transition table; `none` means *halt*. -/
  δ : Fin Q → (Fin k → Fin G) → Option (Fin Q × (Fin k → Fin G) × (Fin k → Dir))

/-- Machine configurations: control state and all tapes. -/
structure Cfg (k Q G : Nat) where
  state : Fin Q
  tapes : Fin k → Tape (Fin G)

namespace TM

variable (M : TM)

/-- The blank symbol. -/
def blank : Fin M.G := ⟨0, by have := M.hG; omega⟩

/-- The symbol encoding a bit. -/
def bitSym (b : Bool) : Fin M.G := ⟨if b then 2 else 1, by have := M.hG; split <;> omega⟩

/-- Decode a bit symbol. -/
def decodeBit (a : Fin M.G) : Option Bool :=
  if a.val = 1 then some false else if a.val = 2 then some true else none

/-- The maximal prefix of bit symbols, decoded. -/
def readBits : List (Fin M.G) → Word
  | [] => []
  | a :: l =>
    match M.decodeBit a with
    | some b => b :: readBits l
    | none => []

/-- The input tape holding `x`, head on its first symbol. -/
def inputTape : Word → Tape (Fin M.G)
  | [] => ⟨[], M.blank, []⟩
  | b :: w => ⟨[], M.bitSym b, w.map M.bitSym⟩

/-- An empty tape. -/
def blankTape : Tape (Fin M.G) := ⟨[], M.blank, []⟩

/-- Initial configuration on input `x`. -/
def init (x : Word) : Cfg M.k M.Q M.G :=
  ⟨⟨0, M.hQ⟩, fun i => if i.val = 0 then M.inputTape x else M.blankTape⟩

/-- One transition; `none` iff the machine has halted. -/
def step (c : Cfg M.k M.Q M.G) : Option (Cfg M.k M.Q M.G) :=
  match M.δ c.state (fun i => (c.tapes i).head) with
  | none => none
  | some (q, w, d) => some ⟨q, fun i => ((c.tapes i).write (w i)).move M.blank (d i)⟩

/-- Run for at most `n` transitions (stopping early if the machine halts). -/
def run : Nat → Cfg M.k M.Q M.G → Cfg M.k M.Q M.G
  | 0, c => c
  | n + 1, c =>
    match M.step c with
    | none => c
    | some c' => run n c'

/-- The output word of a configuration (read on tape `0` from the head rightwards). -/
def output (c : Cfg M.k M.Q M.G) : Word :=
  M.readBits ((c.tapes ⟨0, M.hk⟩).head :: (c.tapes ⟨0, M.hk⟩).right)

/-- `M` halts on input `x` after at most `t` transitions, with output `y`. -/
def HaltsWithin (x : Word) (t : Nat) (y : Word) : Prop :=
  ∃ s, s ≤ t ∧ M.step (M.run s (M.init x)) = none ∧ M.output (M.run s (M.init x)) = y

/-- `M` computes `f` within time `p(|x|)`. -/
def ComputesInTime (f : Word → Word) (p : Poly) : Prop :=
  ∀ x : Word, M.HaltsWithin x (p.eval x.length) (f x)

end TM

/-- **The class FP** of polynomial-time computable word functions, defined via
    multi-tape Turing machines with an explicit polynomial time bound. -/
def FP (f : Word → Word) : Prop :=
  ∃ (M : TM) (p : Poly), M.ComputesInTime f p

end FeasibleUnivalence.BC
