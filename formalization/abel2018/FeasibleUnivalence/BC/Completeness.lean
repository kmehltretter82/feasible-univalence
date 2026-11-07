/-
  FeasibleUnivalence/BC/Completeness.lean

  Polynomial-time completeness of the Bellantoni–Cook function algebra (`FP f → BCDefinable f`)
  and the headline characterization theorem `defFun_eq_FP`:
  $$(∃ \text{prog} : \text{Fn } 1\ 0,\ \forall x,\ \text{prog.eval } [x]\ [] = f\ x) \iff \text{FP } f.$$

  Architecture:
  1. Basic BC combinators (`prependConst`, `constWord`, `branchPrefix`, `dropConst`, `dropBlock`,
     `polyWord`).
  2. Fixed-width block tables (`concatRev`, `tableOf`, `revBlocks`).
  3. Unary encoding of bounded naturals and TM block data (`BlockData`, `encBlock`, `decBlock`,
     `cfgBlock`, `encCfg`).
  4. Initial TM configuration in BC (`initCfgBC`).
  5. Single-step TM transition (`stepCfgBC`) and polynomial-time iteration (`runCfgBC`).
  6. Output tape decoding (`outputCfgBC`), full TM simulator (`simTM`), `bc_completeness`,
     and `defFun_eq_FP`.
-/

import FeasibleUnivalence.BC.Syntax
import FeasibleUnivalence.BC.Soundness

namespace FeasibleUnivalence.BC

/-! ## 1. Basic BC Combinators and `polyWord` -/

/-- Tuple helpers for `Fin 1 → α`, `Fin 2 → α`, `Fin 3 → α`, `Fin 4 → α`. -/
def vec1 {α : Type _} (a : α) : Fin 1 → α := fun _ => a

def vec2 {α : Type _} (a b : α) : Fin 2 → α
  | ⟨0, _⟩ => a
  | ⟨_ + 1, _⟩ => b

def vec3 {α : Type _} (a b c : α) : Fin 3 → α
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨_ + 2, _⟩ => c

def vec4 {α : Type _} (a b c d : α) : Fin 4 → α
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨_ + 3, _⟩ => d

@[simp] theorem vec1_zero {α : Type _} (a : α) : vec1 a 0 = a := rfl
@[simp] theorem vec2_zero {α : Type _} (a b : α) : vec2 a b 0 = a := rfl
@[simp] theorem vec2_one {α : Type _} (a b : α) (i : Fin 1) : vec2 a b i.succ = b := by
  cases i; rfl
@[simp] theorem vec3_zero {α : Type _} (a b c : α) : vec3 a b c 0 = a := rfl
@[simp] theorem vec3_succ {α : Type _} (a b c : α) (i : Fin 2) : vec3 a b c i.succ = vec2 b c i := by
  rcases i with ⟨_ | _, _⟩ <;> rfl
@[simp] theorem vec4_zero {α : Type _} (a b c d : α) : vec4 a b c d 0 = a := rfl
@[simp] theorem vec4_succ {α : Type _} (a b c d : α) (i : Fin 3) : vec4 a b c d i.succ = vec3 b c d i := by
  rcases i with ⟨_ | _ | _, _⟩ <;> rfl

/-- Constant empty word function of arbitrary arity `(n, m)`. -/
def constZero {n m : Nat} : Fn n m :=
  .comp .zero Fin.elim0 Fin.elim0

@[simp] theorem eval_constZero {n m : Nat} (xs ys : List Word) :
    (constZero (n := n) (m := m)).eval xs ys = [] := by
  simp [constZero, List.ofFn_zero]

/-- Prepend a constant word `u` onto safe argument `j` of `Fn n m`. -/
def prependConstAt {n m : Nat} (j : Fin m) : Word → Fn n m
  | [] => .projS j
  | false :: u => .comp .s0 Fin.elim0 (vec1 (prependConstAt j u))
  | true :: u => .comp .s1 Fin.elim0 (vec1 (prependConstAt j u))

@[simp] theorem eval_prependConstAt {n m : Nat} (j : Fin m) (u : Word) (xs ys : List Word) :
    (prependConstAt (n := n) j u).eval xs ys = u ++ ys.getD j.val [] := by
  induction u with
  | nil => simp [prependConstAt]
  | cons b u ih =>
    cases b <;> simp [prependConstAt, List.ofFn_succ, List.ofFn_zero, ih]

/-- Prepend a constant word `u` onto safe argument `0` of `Fn 0 1`. -/
def prependConst (u : Word) : Fn 0 1 :=
  prependConstAt ⟨0, Nat.zero_lt_one⟩ u

@[simp] theorem eval_prependConst (u : Word) (xs ys : List Word) :
    (prependConst u).eval xs ys = u ++ ys.getD 0 [] :=
  eval_prependConstAt ⟨0, Nat.zero_lt_one⟩ u xs ys

/-- Constant word `u` of arbitrary arity `(n, m)`. -/
def constWord {n m : Nat} (u : Word) : Fn n m :=
  .comp (prependConst u) Fin.elim0 (vec1 constZero)

@[simp] theorem eval_constWord {n m : Nat} (u : Word) (xs ys : List Word) :
    (constWord (n := n) (m := m) u).eval xs ys = u := by
  simp [constWord, List.ofFn_succ, List.ofFn_zero]

/-- Extract a `B`-bit prefix of `y`, padding with `false` if `y` has fewer than `B` bits. -/
def padFalse : Nat → Word → Word
  | 0, _ => []
  | B + 1, [] => false :: padFalse B []
  | B + 1, b :: y => b :: padFalse B y

@[simp] theorem padFalse_zero (y : Word) : padFalse 0 y = [] := rfl
@[simp] theorem padFalse_nil (B : Nat) : padFalse B [] = List.replicate B false := by
  induction B with
  | zero => rfl
  | succ B ih => simp [padFalse, List.replicate_succ, ih]

@[simp] theorem length_padFalse (B : Nat) (y : Word) : (padFalse B y).length = B := by
  induction B generalizing y with
  | zero => rfl
  | succ B ih =>
    cases y with
    | nil => simp [padFalse]
    | cons b y => simp [padFalse, ih]

theorem padFalse_append_exact (u v : Word) :
    padFalse u.length (u ++ v) = u := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [padFalse, ih]

theorem padFalse_eq_of_length {B : Nat} {u v : Word} (h : u.length = B) :
    padFalse B (u ++ v) = u := by
  subst h
  exact padFalse_append_exact u v

theorem padFalse_self {B : Nat} {u : Word} (h : u.length = B) :
    padFalse B u = u := by
  have h1 := padFalse_eq_of_length (v := []) h
  simpa using h1

theorem padFalse_add (A B : Nat) (w : Word) :
    padFalse (A + B) w = padFalse A w ++ padFalse B (w.drop A) := by
  induction A generalizing w with
  | zero => simp
  | succ A ih =>
    rw [Nat.succ_add]
    cases w with
    | nil => simp [padFalse, ih []]
    | cons b w => simp [padFalse, ih w]

/-- Shift the safe arguments of `f : Fn 0 m` by 1 (ignoring safe argument `0`). -/
def shiftSafe {m : Nat} (f : Fn 0 m) : Fn 0 (m + 1) :=
  .comp f Fin.elim0 (fun j => .projS j.succ)

theorem ofFn_getD_eq_self : ∀ {m : Nat} (ys : List Word), ys.length = m →
    (List.ofFn fun j : Fin m => ys.getD j.val []) = ys
  | 0, [], _ => rfl
  | m + 1, y :: ys, h => by
    simp only [List.length_cons] at h
    rw [List.ofFn_succ]
    congr 1
    exact ofFn_getD_eq_self ys (by omega)

theorem ofFn_getD_succ (y : Word) : ∀ {m : Nat} (ys : List Word), ys.length = m →
    (List.ofFn fun j : Fin m => (y :: ys).getD j.succ.val []) = ys
  | 0, [], _ => rfl
  | m + 1, y' :: ys, h => by
    simp only [List.length_cons] at h
    rw [List.ofFn_succ]
    congr 1
    exact ofFn_getD_succ y' ys (by omega)

theorem eval_shiftSafe {m : Nat} (f : Fn 0 m) (y : Word) (ys : List Word) (hys : ys.length = m) :
    (shiftSafe f).eval [] (y :: ys) = f.eval [] ys := by
  simp only [shiftSafe, Fn.eval_comp, List.ofFn_zero, Fn.eval_projS]
  rw [ofFn_getD_succ y ys hys]

/-- Apply `Fn.pred` to safe argument `0` while keeping safe arguments `1 .. m` unchanged,
    then pass the resulting `m + 1` safe arguments to `g : Fn 0 (m + 1)`. -/
def predFirstSafe {m : Nat} (g : Fn 0 (m + 1)) : Fn 0 (m + 1) :=
  .comp g Fin.elim0 (Fin.cases (.comp .pred Fin.elim0 (vec1 (.projS ⟨0, Nat.zero_lt_succ m⟩)))
                               (fun j => .projS j.succ))

theorem eval_predFirstSafe {m : Nat} (g : Fn 0 (m + 1)) (y : Word) (ys : List Word)
    (hys : ys.length = m) :
    (predFirstSafe g).eval [] (y :: ys) = g.eval [] (y.tail :: ys) := by
  simp only [predFirstSafe, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ, Fin.cases_zero,
    Fin.cases_succ, vec1_zero, Fn.eval_pred, Fn.eval_projS, List.getD_cons_zero]
  rw [ofFn_getD_succ y ys hys]

/-- Decision tree of depth `B` inspecting the first `B` bits of safe argument `0` (`padFalse B y`)
    and dispatching to `K (padFalse B y) : Fn 0 m` on the remaining `m` safe arguments `ys`. -/
def branchPrefix : {m : Nat} → (B : Nat) → (Word → Fn 0 m) → Fn 0 (m + 1)
  | _, 0, K => shiftSafe (K [])
  | _, B + 1, K =>
      let bFalse := predFirstSafe (branchPrefix B (fun w => K (false :: w)))
      let bTrue  := predFirstSafe (branchPrefix B (fun w => K (true :: w)))
      .comp .cond Fin.elim0
        (vec4 (.projS ⟨0, Nat.zero_lt_succ _⟩) bFalse bFalse bTrue)

theorem eval_branchPrefix {m : Nat} (B : Nat) (K : Word → Fn 0 m)
    (y : Word) (ys : List Word) (hys : ys.length = m) :
    (branchPrefix B K).eval [] (y :: ys) = (K (padFalse B y)).eval [] ys := by
  induction B generalizing K y with
  | zero =>
    exact eval_shiftSafe (K []) y ys hys
  | succ B ih =>
    simp only [branchPrefix, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
      vec4_zero, vec4_succ, vec3_zero, vec3_succ, vec2_zero, vec2_one,
      Fn.eval_cond, Fn.eval_projS, List.getD_cons_zero, List.getD_cons_succ]
    cases y with
    | nil =>
      simp only [condW, padFalse]
      rw [eval_predFirstSafe _ [] ys hys, List.tail_nil]
      exact ih (fun w => K (false :: w)) []
    | cons b y' =>
      cases b with
      | false =>
        simp only [condW, padFalse]
        rw [eval_predFirstSafe _ (false :: y') ys hys, List.tail_cons]
        exact ih (fun w => K (false :: w)) y'
      | true =>
        simp only [condW, padFalse]
        rw [eval_predFirstSafe _ (true :: y') ys hys, List.tail_cons]
        exact ih (fun w => K (true :: w)) y'

/-- Drop a constant number `D` of bits from safe argument `0`. -/
def dropConst : Nat → Fn 0 1
  | 0 => .projS ⟨0, Nat.zero_lt_one⟩
  | D + 1 => .comp .pred Fin.elim0 (vec1 (dropConst D))

@[simp] theorem eval_dropConst (D : Nat) (xs : List Word) (y : Word) :
    (dropConst D).eval xs [y] = y.drop D := by
  induction D generalizing y with
  | zero => simp [dropConst]
  | succ D ih =>
    simp only [dropConst, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ, vec1_zero,
      Fn.eval_pred, List.getD_cons_zero, ih]
    rw [← List.drop_drop]
    cases List.drop D y <;> rfl

/-- Drop `w.length * D` bits from safe argument `y`, where `w` is normal argument `0`. -/
def dropBlock (D : Nat) : Fn 1 1 :=
  let step : Fn 1 2 := .comp (dropConst D) Fin.elim0 (vec1 (.projS ⟨0, by decide⟩))
  .srec (.projS ⟨0, Nat.zero_lt_one⟩) step step

@[simp] theorem eval_dropBlock (D : Nat) (w y : Word) :
    (dropBlock D).eval [w] [y] = y.drop (w.length * D) := by
  induction w with
  | nil => simp [dropBlock]
  | cons b w ih =>
    have hstep : ((dropBlock D).eval [b :: w] [y]) =
        ((dropBlock D).eval [w] [y]).drop D := by
      cases b <;> simp [dropBlock, Fn.eval_srec_cons, List.ofFn_zero, List.ofFn_succ]
    rw [hstep, ih, List.drop_drop, List.length_cons, Nat.succ_mul]

/-- Construct a BC program `polyWord q : Fn 1 0` whose output on `[x], []` has length `q.eval x.length`. -/
def appendSafe : Fn 1 1 :=
  let s0_rec : Fn 1 2 := .comp .s0 Fin.elim0 (vec1 (.projS ⟨0, by decide⟩))
  .srec (.projS ⟨0, Nat.zero_lt_one⟩) s0_rec s0_rec

theorem length_eval_appendSafe (w y : Word) :
    (appendSafe.eval [w] [y]).length = w.length + y.length := by
  induction w with
  | nil => simp [appendSafe]
  | cons b w ih =>
    have hstep : appendSafe.eval [b :: w] [y] = false :: appendSafe.eval [w] [y] := by
      cases b <;> simp [appendSafe, Fn.eval_srec_cons, List.ofFn_zero, List.ofFn_succ]
    rw [hstep, List.length_cons, ih, List.length_cons, Nat.succ_add]

/-- Multiply lengths: output on `[w₁, w₂], []` has length `w₁.length * w₂.length`. -/
def mulWord : Fn 2 0 :=
  let step : Fn 2 1 :=
    .comp appendSafe (vec1 (.projN ⟨1, by decide⟩)) (vec1 (.projS ⟨0, Nat.zero_lt_one⟩))
  .srec constZero step step

theorem length_eval_mulWord (w₁ w₂ : Word) :
    (mulWord.eval [w₁, w₂] []).length = w₁.length * w₂.length := by
  induction w₁ with
  | nil => simp [mulWord]
  | cons b w₁ ih =>
    have hstep : mulWord.eval [b :: w₁, w₂] [] =
        appendSafe.eval [w₂] [mulWord.eval [w₁, w₂] []] := by
      cases b <;> simp [mulWord, Fn.eval_srec_cons, List.ofFn_zero, List.ofFn_succ]
    rw [hstep, length_eval_appendSafe, ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- For every syntactic polynomial `q : Poly`, `polyWord q : Fn 1 0` produces a word of length
    `q.eval x.length` on input `[x], []`. -/
def polyWord : Poly → Fn 1 0
  | .const c => constWord (List.replicate c false)
  | .var => .projN ⟨0, Nat.zero_lt_one⟩
  | .add p q => .comp appendSafe (vec1 (polyWord p)) (vec1 (polyWord q))
  | .mul p q => .comp mulWord (vec2 (polyWord p) (polyWord q)) Fin.elim0
  | .comp p q => .comp (polyWord p) (vec1 (polyWord q)) Fin.elim0

@[simp] theorem length_eval_polyWord (q : Poly) (x : Word) :
    ((polyWord q).eval [x] []).length = q.eval x.length := by
  induction q generalizing x with
  | const c => simp [polyWord]
  | var => simp [polyWord]
  | add p q ihp ihq =>
    simp [polyWord, List.ofFn_succ, List.ofFn_zero, length_eval_appendSafe, ihp, ihq]
  | mul p q ihp ihq =>
    simp [polyWord, List.ofFn_succ, List.ofFn_zero, length_eval_mulWord, ihp, ihq]
  | comp p q ihp ihq =>
    simp [polyWord, List.ofFn_succ, List.ofFn_zero, ihp, ihq]

/-! ## 2. Fixed-Width Block Tables (`concatRev`, `tableOf`, `revBlocks`) -/

/-- Concatenate `f (n - 1) ++ f (n - 2) ++ ... ++ f 0`. -/
def concatRev (f : Nat → Word) : Nat → Word
  | 0 => []
  | n + 1 => f n ++ concatRev f n

@[simp] theorem concatRev_zero (f : Nat → Word) : concatRev f 0 = [] := rfl
@[simp] theorem concatRev_succ (f : Nat → Word) (n : Nat) :
    concatRev f (n + 1) = f n ++ concatRev f n := rfl

theorem length_concatRev {D : Nat} (f : Nat → Word) (n : Nat)
    (hf : ∀ i : Nat, i < n → (f i).length = D) :
    (concatRev f n).length = n * D := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [concatRev_succ, List.length_append, Nat.succ_mul]
    rw [ih (fun i hi => hf i (by omega)), hf n (Nat.lt_succ_self n), Nat.add_comm]

theorem drop_append_exact (u v : Word) :
    (u ++ v).drop u.length = v := by
  induction u with
  | nil => rfl
  | cons _ u ih => simp [ih]

theorem drop_append_of_length {D : Nat} {u v : Word} (h : u.length = D) :
    (u ++ v).drop D = v := by
  subst h
  exact drop_append_exact u v

theorem replicate_add {α : Type _} (m n : Nat) (a : α) :
    List.replicate (m + n) a = List.replicate m a ++ List.replicate n a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, List.cons_append, ih]

theorem padFalse_drop_concatRev {D : Nat} (f : Nat → Word) (n : Nat)
    (hf : ∀ i : Nat, i < n → (f i).length = D) :
    ∀ k : Nat, k < n → padFalse D ((concatRev f n).drop (k * D)) = f (n - 1 - k) := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    simp only [concatRev_succ]
    have hfn : (f n).length = D := hf n (Nat.lt_succ_self n)
    cases k with
    | zero =>
      simp only [Nat.zero_mul, List.drop_zero, Nat.add_sub_cancel, Nat.sub_zero]
      exact padFalse_eq_of_length hfn
    | succ k' =>
      rw [Nat.succ_mul, Nat.add_comm (k' * D) D, ← List.drop_drop, ← hfn,
          drop_append_exact (f n) (concatRev f n), hfn]
      rw [ih (fun i hi => hf i (by omega)) k' (by omega)]
      congr 1
      omega

/-- Concatenate `f 0 ++ f 1 ++ ... ++ f (N - 1)`, defined via `concatRev`. -/
def tableOf (f : Nat → Word) (N : Nat) : Word :=
  concatRev (fun k => f (N - 1 - k)) N

theorem length_tableOf {D : Nat} (f : Nat → Word) (N : Nat)
    (hf : ∀ j : Nat, j < N → (f j).length = D) :
    (tableOf f N).length = N * D := by
  apply length_concatRev
  intro k hk
  exact hf (N - 1 - k) (by omega)

theorem padFalse_drop_tableOf {D : Nat} (f : Nat → Word) (N : Nat)
    (hf : ∀ j : Nat, j < N → (f j).length = D) {j : Nat} (hj : j < N) :
    padFalse D ((tableOf f N).drop (j * D)) = f j := by
  unfold tableOf
  rw [padFalse_drop_concatRev (fun k => f (N - 1 - k)) N
        (fun k hk => hf (N - 1 - k) (by omega)) j hj]
  congr 1
  omega

/-- Reverse a sequence of `W.length` blocks of width `D`:
    maps `concatRev f W.length` to `tableOf f W.length`. -/
def revBlocks (D : Nat) : Fn 1 1 :=
  let extractAndPrepend : Fn 1 2 :=
    .comp (branchPrefix D prependConst)
      Fin.elim0
      (vec2 (.comp (dropBlock D) (vec1 (.projN ⟨0, Nat.zero_lt_one⟩)) (vec1 (.projS ⟨1, by decide⟩)))
            (.projS ⟨0, by decide⟩))
  .srec constZero extractAndPrepend extractAndPrepend

theorem eval_revBlocks_prefix (D : Nat) (y : Word) (u : Word) :
    (revBlocks D).eval [u] [y] =
      concatRev (fun k => padFalse D (y.drop (k * D))) u.length := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    have hstep : (revBlocks D).eval [b :: u] [y] =
        (branchPrefix D prependConst).eval [] [y.drop (u.length * D), (revBlocks D).eval [u] [y]] := by
      cases b <;> simp [revBlocks, Fn.eval_srec_cons, List.ofFn_zero, List.ofFn_succ]
    rw [hstep, eval_branchPrefix D prependConst (y.drop (u.length * D)) [(revBlocks D).eval [u] [y]] rfl]
    simp [ih]

theorem eval_revBlocks {D : Nat} (f : Nat → Word) (W : Word)
    (hf : ∀ i : Nat, i < W.length → (f i).length = D) :
    (revBlocks D).eval [W] [concatRev f W.length] = tableOf f W.length := by
  rw [eval_revBlocks_prefix]
  unfold tableOf
  have hcongr : ∀ n : Nat, n ≤ W.length →
      concatRev (fun k => padFalse D ((concatRev f W.length).drop (k * D))) n =
      concatRev (fun k => f (W.length - 1 - k)) n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [concatRev_succ]
      rw [padFalse_drop_concatRev f W.length hf n (by omega), ih (by omega)]
  exact hcongr W.length (Nat.le_refl _)

theorem eval_revBlocks_tableOf {D : Nat} (f : Nat → Word) (W : Word)
    (hf : ∀ j : Nat, j < W.length → (f j).length = D) :
    (revBlocks D).eval [W] [tableOf f W.length] = concatRev f W.length := by
  unfold tableOf
  rw [eval_revBlocks (fun k => f (W.length - 1 - k)) W (fun k hk => hf _ (by omega))]
  unfold tableOf
  have hcongr : ∀ n : Nat, n ≤ W.length →
      concatRev (fun k => f (W.length - 1 - (W.length - 1 - k))) n = concatRev f n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [concatRev_succ]
      have hidx : W.length - 1 - (W.length - 1 - n) = n := by omega
      rw [hidx, ih (by omega)]
  exact hcongr W.length (Nat.le_refl _)

/-! ## 3. Unary Encoding of Bounded Naturals and TM Block Data -/

/-- Encode `v : Fin W` as `v` `true` bits followed by `W - v` `false` bits (fixed width `W`). -/
def encFin {W : Nat} (v : Fin W) : Word :=
  List.replicate v.val true ++ List.replicate (W - v.val) false

theorem length_encFin {W : Nat} (v : Fin W) : (encFin v).length = W := by
  simp only [encFin, List.length_append, List.length_replicate]
  have hv : v.val < W := v.isLt
  omega

theorem encFin_zero {W : Nat} (hW : 0 < W) :
    encFin (⟨0, hW⟩ : Fin W) = List.replicate W false := by
  simp [encFin]

/-- Count leading `true` bits of a word. -/
def countTrue : Word → Nat
  | [] => 0
  | false :: _ => 0
  | true :: w => countTrue w + 1

theorem countTrue_replicate_true_cons_false (n : Nat) (w : Word) :
    countTrue (List.replicate n true ++ false :: w) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate_succ, countTrue, ih]

theorem countTrue_encFin {W : Nat} (v : Fin W) :
    countTrue (encFin v) = v.val := by
  unfold encFin
  have hv : v.val < W := v.isLt
  have hsub : W - v.val = (W - 1 - v.val) + 1 := by omega
  rw [hsub, List.replicate_succ]
  exact countTrue_replicate_true_cons_false v.val _

/-- Decode a word into `Fin W` by counting leading `true` bits. -/
def decFin {W : Nat} (hW : 0 < W) (w : Word) : Fin W :=
  if h : countTrue w < W then ⟨countTrue w, h⟩ else ⟨0, hW⟩

theorem decFin_encFin {W : Nat} (hW : 0 < W) (v : Fin W) :
    decFin hW (encFin v) = v := by
  unfold decFin
  rw [countTrue_encFin, dif_pos v.isLt]

/-- Encode a tuple `f : Fin k → α` by concatenating fixed-width encodings. -/
def encTuple {α : Type _} (enc : α → Word) : {k : Nat} → (Fin k → α) → Word
  | 0, _ => []
  | _ + 1, f => enc (f ⟨0, Nat.zero_lt_succ _⟩) ++ encTuple enc (fun i => f i.succ)

/-- Decode a word into `Fin k → α` by slicing into chunks of width `E`. -/
def decTuple {α : Type _} (E : Nat) (dec : Word → α) : (k : Nat) → Word → (Fin k → α)
  | 0, _, i => i.elim0
  | _ + 1, w, ⟨0, _⟩ => dec (padFalse E w)
  | k + 1, w, ⟨i + 1, hi⟩ => decTuple E dec k (w.drop E) ⟨i, Nat.lt_of_succ_lt_succ hi⟩

theorem length_encTuple {α : Type _} {E : Nat} (enc : α → Word)
    (henc : ∀ a : α, (enc a).length = E) :
    ∀ {k : Nat} (f : Fin k → α), (encTuple enc f).length = k * E
  | 0, _ => by simp [encTuple]
  | k + 1, f => by
    simp only [encTuple, List.length_append, henc (f ⟨0, Nat.zero_lt_succ k⟩),
      length_encTuple enc henc (fun i => f i.succ), Nat.succ_mul, Nat.add_comm]

theorem decTuple_encTuple {α : Type _} {E : Nat} (enc : α → Word) (dec : Word → α)
    (henc : ∀ a : α, (enc a).length = E) (hdec : ∀ a : α, dec (enc a) = a) :
    ∀ {k : Nat} (f : Fin k → α), decTuple E dec k (encTuple enc f) = f
  | 0, f => by funext i; exact i.elim0
  | k + 1, f => by
    funext ⟨i, hi⟩
    cases i with
    | zero =>
      simp only [decTuple, encTuple]
      rw [padFalse_eq_of_length (henc _), hdec]
    | succ i' =>
      simp only [decTuple, encTuple]
      rw [drop_append_of_length (henc _)]
      have ih := congrFun (decTuple_encTuple enc dec henc hdec (fun j : Fin k => f j.succ)) ⟨i', Nat.lt_of_succ_lt_succ hi⟩
      exact ih

theorem encTuple_replicate_false {α : Type _} {E : Nat} (enc : α → Word) (a₀ : α)
    (ha₀ : enc a₀ = List.replicate E false) :
    ∀ (k : Nat), encTuple enc (fun _ : Fin k => a₀) = List.replicate (k * E) false
  | 0 => by simp [encTuple]
  | k + 1 => by
    simp only [encTuple, ha₀, encTuple_replicate_false enc a₀ ha₀ k,
      Nat.succ_mul, Nat.add_comm (k * E) E, replicate_add]

/-- Data stored in block `j` of an encoded TM configuration. -/
structure BlockData (M : TM) where
  isZero : Bool
  state : Fin M.Q
  headSym : Fin M.k → Fin M.G
  leftSym : Fin M.k → Fin M.G
  rightSym : Fin M.k → Fin M.G

/-- Fixed bit-width of one block for machine `M`. -/
def blockWidth (M : TM) : Nat :=
  1 + M.Q + (M.k * M.G + (M.k * M.G + M.k * M.G))

theorem blockWidth_pos (M : TM) : 0 < blockWidth M := by
  unfold blockWidth
  omega

/-- The all-blank block (corresponding to an out-of-bounds cell index `j` with `isZero = false`). -/
def blankBlock (M : TM) : BlockData M where
  isZero := false
  state := ⟨0, M.hQ⟩
  headSym := fun _ => M.blank
  leftSym := fun _ => M.blank
  rightSym := fun _ => M.blank

/-- Encode `BlockData M` into a word of length `blockWidth M`. -/
def encBlock (M : TM) (b : BlockData M) : Word :=
  [b.isZero] ++
    (encFin b.state ++
      (encTuple encFin b.headSym ++
        (encTuple encFin b.leftSym ++
          encTuple encFin b.rightSym)))

theorem length_encBlock (M : TM) (b : BlockData M) :
    (encBlock M b).length = blockWidth M := by
  simp only [encBlock, blockWidth, List.length_append, List.length_singleton,
    length_encFin, length_encTuple encFin (fun a => length_encFin a)]
  omega

theorem encBlock_blankBlock (M : TM) :
    encBlock M (blankBlock M) = List.replicate (blockWidth M) false := by
  have hG0 : 0 < M.G := by have := M.hG; omega
  have hblank : encFin M.blank = List.replicate M.G false := encFin_zero hG0
  have htuple : encTuple encFin (fun _ : Fin M.k => M.blank) = List.replicate (M.k * M.G) false :=
    encTuple_replicate_false encFin M.blank hblank M.k
  simp only [encBlock, blankBlock, encFin_zero M.hQ, htuple, blockWidth, Nat.add_assoc, replicate_add]
  rfl

/-- Decode a word of length `blockWidth M` back into `BlockData M`. -/
def decBlock (M : TM) (w : Word) : BlockData M :=
  let hG0 : 0 < M.G := by have := M.hG; omega
  let w1 := w.drop 1
  let w2 := w1.drop M.Q
  let w3 := w2.drop (M.k * M.G)
  let w4 := w3.drop (M.k * M.G)
  { isZero := w.headD false
    state := decFin M.hQ (padFalse M.Q w1)
    headSym := decTuple M.G (decFin hG0) M.k (padFalse (M.k * M.G) w2)
    leftSym := decTuple M.G (decFin hG0) M.k (padFalse (M.k * M.G) w3)
    rightSym := decTuple M.G (decFin hG0) M.k (padFalse (M.k * M.G) w4) }

theorem decBlock_encBlock (M : TM) (b : BlockData M) :
    decBlock M (encBlock M b) = b := by
  have hG0 : 0 < M.G := by have := M.hG; omega
  have hlen_q : (encFin b.state).length = M.Q := length_encFin b.state
  have hlen_h : (encTuple encFin b.headSym).length = M.k * M.G :=
    length_encTuple encFin length_encFin b.headSym
  have hlen_l : (encTuple encFin b.leftSym).length = M.k * M.G :=
    length_encTuple encFin length_encFin b.leftSym
  have hlen_r : (encTuple encFin b.rightSym).length = M.k * M.G :=
    length_encTuple encFin length_encFin b.rightSym
  unfold decBlock encBlock
  dsimp only
  have hd1 : ([b.isZero] ++ (encFin b.state ++ (encTuple encFin b.headSym ++ (encTuple encFin b.leftSym ++ encTuple encFin b.rightSym)))).drop 1 =
      encFin b.state ++ (encTuple encFin b.headSym ++ (encTuple encFin b.leftSym ++ encTuple encFin b.rightSym)) := rfl
  rw [hd1]
  rw [drop_append_of_length hlen_q]
  rw [drop_append_of_length hlen_h]
  rw [drop_append_of_length hlen_l]
  rw [padFalse_eq_of_length hlen_q,
      padFalse_eq_of_length hlen_h,
      padFalse_eq_of_length hlen_l,
      padFalse_self hlen_r,
      decFin_encFin M.hQ b.state,
      decTuple_encTuple encFin (decFin hG0) length_encFin (decFin_encFin hG0) b.headSym,
      decTuple_encTuple encFin (decFin hG0) length_encFin (decFin_encFin hG0) b.leftSym,
      decTuple_encTuple encFin (decFin hG0) length_encFin (decFin_encFin hG0) b.rightSym]
  cases b
  rfl

theorem decBlock_replicate_false (M : TM) :
    decBlock M (List.replicate (blockWidth M) false) = blankBlock M := by
  rw [← encBlock_blankBlock M, decBlock_encBlock M]

/-- Extract the `j`-th `BlockData M` from a configuration `c : Cfg M.k M.Q M.G`. -/
def cfgBlock (M : TM) (c : Cfg M.k M.Q M.G) (j : Nat) : BlockData M :=
  if j = 0 then
    { isZero := true
      state := c.state
      headSym := fun i => (c.tapes i).head
      leftSym := fun i => (c.tapes i).left.getD 0 M.blank
      rightSym := fun i => (c.tapes i).right.getD 0 M.blank }
  else
    { isZero := false
      state := ⟨0, M.hQ⟩
      headSym := fun _ => M.blank
      leftSym := fun i => (c.tapes i).left.getD j M.blank
      rightSym := fun i => (c.tapes i).right.getD j M.blank }

/-- Encode a TM configuration `c` across `N` blocks of width `blockWidth M`. -/
def encCfg (M : TM) (N : Nat) (c : Cfg M.k M.Q M.G) : Word :=
  tableOf (fun j => encBlock M (cfgBlock M c j)) N

theorem length_encCfg (M : TM) (N : Nat) (c : Cfg M.k M.Q M.G) :
    (encCfg M N c).length = N * blockWidth M :=
  length_tableOf _ N (fun j _ => length_encBlock M (cfgBlock M c j))

/-! ## 4. Initial TM Configuration in BC (`initCfgBC`) -/

/-- Branch on `y.head? : Option Bool` of safe argument `0`, dispatching to `K y.head? : Fn 0 m`
    on the remaining `m` safe arguments `ys`. -/
def branchHead {m : Nat} (K : Option Bool → Fn 0 m) : Fn 0 (m + 1) :=
  .comp .cond Fin.elim0
    (vec4 (.projS ⟨0, Nat.zero_lt_succ m⟩)
          (shiftSafe (K none))
          (shiftSafe (K (some false)))
          (shiftSafe (K (some true))))

theorem eval_branchHead {m : Nat} (K : Option Bool → Fn 0 m)
    (y : Word) (ys : List Word) (hys : ys.length = m) :
    (branchHead K).eval [] (y :: ys) = (K y.head?).eval [] ys := by
  simp only [branchHead, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
    vec4_zero, vec4_succ, vec3_zero, vec3_succ, vec2_zero, vec2_one,
    Fn.eval_cond, Fn.eval_projS, List.getD_cons_zero,
    eval_shiftSafe _ y ys hys]
  cases y with
  | nil => rfl
  | cons b y' => cases b <;> rfl

/-- Construct `cfgBlock M (M.init x) j` from `isZero = (j = 0)` and the first two bits
    `(x.drop j).head?` and `(x.drop j).tail.head?`. -/
def initBlockFromDrop (M : TM) (isZero : Bool) (h0 r0 : Option Bool) : BlockData M :=
  let optSym : Option Bool → Fin M.G
    | none => M.blank
    | some b => M.bitSym b
  if isZero then
    { isZero := true
      state := ⟨0, M.hQ⟩
      headSym := fun i => if i.val = 0 then optSym h0 else M.blank
      leftSym := fun _ => M.blank
      rightSym := fun i => if i.val = 0 then optSym r0 else M.blank }
  else
    { isZero := false
      state := ⟨0, M.hQ⟩
      headSym := fun _ => M.blank
      leftSym := fun _ => M.blank
      rightSym := fun i => if i.val = 0 then optSym r0 else M.blank }

theorem map_bitSym_getD (M : TM) (w : Word) (j : Nat) :
    (w.map M.bitSym).getD j M.blank =
      match (w.drop j).head? with
      | none => M.blank
      | some b => M.bitSym b := by
  induction w generalizing j with
  | nil => simp [List.getD]
  | cons b w ih =>
    cases j with
    | zero => rfl
    | succ j' => exact ih j'

theorem inputTape_right_getD (M : TM) (x : Word) (j : Nat) :
    (M.inputTape x).right.getD j M.blank =
      match (x.drop j).tail.head? with
      | none => M.blank
      | some b => M.bitSym b := by
  cases x with
  | nil => simp [TM.inputTape, List.getD]
  | cons b w =>
    simp only [TM.inputTape]
    rw [map_bitSym_getD M w j]
    congr 2
    cases j <;> simp

theorem initBlockFromDrop_eq_cfgBlock (M : TM) (x : Word) (j : Nat) :
    initBlockFromDrop M (decide (j = 0)) (x.drop j).head? (x.drop j).tail.head? =
      cfgBlock M (M.init x) j := by
  by_cases hj : j = 0
  · subst hj
    simp only [initBlockFromDrop, cfgBlock, decide_true, ↓reduceIte, List.drop_zero, TM.init]
    congr 1
    · funext i
      by_cases hi : i.val = 0
      · simp only [hi, ↓reduceIte]
        cases x <;> rfl
      · simp [hi, TM.blankTape]
    · funext i
      by_cases hi : i.val = 0
      · simp only [hi, ↓reduceIte]
        cases x <;> rfl
      · simp [hi, TM.blankTape]
    · funext i
      by_cases hi : i.val = 0
      · simp only [hi, ↓reduceIte]
        exact (inputTape_right_getD M x 0).symm
      · simp [hi, TM.blankTape, List.getD]
  · simp only [initBlockFromDrop, cfgBlock, hj, decide_false, Bool.false_eq_true, ↓reduceIte, TM.init]
    congr 1
    · funext i
      by_cases hi : i.val = 0
      · simp only [hi, ↓reduceIte]
        cases x <;> simp [TM.inputTape, List.getD]
      · simp [hi, TM.blankTape, List.getD]
    · funext i
      by_cases hi : i.val = 0
      · simp only [hi, ↓reduceIte]
        exact (inputTape_right_getD M x j).symm
      · simp [hi, TM.blankTape, List.getD]

/-- Safe function `Fn 0 3` taking `[y, y.tail, r]` and prepending `encBlock M (initBlockFromDrop M isZero y.head? y.tail.head?)` onto `r`. -/
def initBlockBranch (M : TM) (isZero : Bool) : Fn 0 3 :=
  branchHead (fun h0 =>
    branchHead (fun r0 =>
      prependConst (encBlock M (initBlockFromDrop M isZero h0 r0))))

theorem eval_initBlockBranch (M : TM) (isZero : Bool) (y r : Word) :
    (initBlockBranch M isZero).eval [] [y, y.tail, r] =
      encBlock M (initBlockFromDrop M isZero y.head? y.tail.head?) ++ r := by
  unfold initBlockBranch
  rw [eval_branchHead _ y [y.tail, r] rfl,
      eval_branchHead _ y.tail [r] rfl,
      eval_prependConst]
  rfl

/-- Safe step `Fn 1 2` for `initCfgBC`: on normal `[u]` (`|u| = j`) and safe `[r, x]`,
    tests whether `r = []` (`j = 0`) or `r ≠ []` (`j > 0`) and prepends `encBlock M (cfgBlock M (M.init x) j)` onto `r`. -/
def initStepBC (M : TM) : Fn 1 2 :=
  let yDrop : Fn 1 2 :=
    .comp (dropBlock 1) (vec1 (.projN ⟨0, Nat.zero_lt_one⟩)) (vec1 (.projS ⟨1, by decide⟩))
  let yTail : Fn 1 2 :=
    .comp .pred Fin.elim0 (vec1 yDrop)
  let branchTrue : Fn 1 2 :=
    .comp (initBlockBranch M true) Fin.elim0 (vec3 yDrop yTail (.projS ⟨0, by decide⟩))
  let branchFalse : Fn 1 2 :=
    .comp (initBlockBranch M false) Fin.elim0 (vec3 yDrop yTail (.projS ⟨0, by decide⟩))
  .comp .cond Fin.elim0 (vec4 (.projS ⟨0, by decide⟩) branchTrue branchFalse branchFalse)

theorem eval_initStepBC (M : TM) (u r x : Word) (hr : r = [] ↔ u.length = 0) :
    (initStepBC M).eval [u] [r, x] =
      encBlock M (cfgBlock M (M.init x) u.length) ++ r := by
  have hy : (dropBlock 1).eval [u] [x] = x.drop u.length := by
    simp [eval_dropBlock]
  simp only [initStepBC, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
    vec4_zero, vec4_succ, vec3_zero, vec3_succ, vec2_zero, vec2_one, vec1_zero,
    Fn.eval_cond, Fn.eval_projN, Fn.eval_projS, Fn.eval_pred, List.getD_cons_zero, List.getD_cons_succ, hy]
  rw [eval_initBlockBranch M true (x.drop u.length) r,
      eval_initBlockBranch M false (x.drop u.length) r]
  cases r with
  | nil =>
    have hu0 : u.length = 0 := hr.mp rfl
    simp only [condW, hu0, List.drop_zero]
    rw [← initBlockFromDrop_eq_cfgBlock M x 0]
    rfl
  | cons b r' =>
    have hne : u.length ≠ 0 := fun h0 => List.cons_ne_nil b r' (hr.mpr h0)
    have hdec : decide (u.length = 0) = false := decide_eq_false hne
    cases b <;> {
      simp only [condW]
      rw [← initBlockFromDrop_eq_cfgBlock M x u.length, hdec]
    }

/-- BC program `initCfgBC M : Fn 1 1` computing `encCfg M W.length (M.init x)`
    on normal clock `[W]` and safe input `[x]`. -/
def initCfgBC (M : TM) : Fn 1 1 :=
  let buildRev : Fn 1 1 := .srec constZero (initStepBC M) (initStepBC M)
  .comp (revBlocks (blockWidth M))
    (vec1 (.projN ⟨0, Nat.zero_lt_one⟩))
    (vec1 buildRev)

theorem eval_initCfgBC_buildRev (M : TM) (x u : Word) :
    (Fn.srec constZero (initStepBC M) (initStepBC M)).eval [u] [x] =
      concatRev (fun j => encBlock M (cfgBlock M (M.init x) j)) u.length := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    have hstep : (Fn.srec constZero (initStepBC M) (initStepBC M)).eval [b :: u] [x] =
        (initStepBC M).eval [u]
          [(Fn.srec constZero (initStepBC M) (initStepBC M)).eval [u] [x], x] := by
      cases b <;> simp [Fn.eval_srec_cons]
    have hr : (Fn.srec constZero (initStepBC M) (initStepBC M)).eval [u] [x] = [] ↔ u.length = 0 := by
      rw [ih]
      have hlen := length_concatRev (fun j => encBlock M (cfgBlock M (M.init x) j)) u.length
        (fun j _ => length_encBlock M _)
      have hbw : 0 < blockWidth M := blockWidth_pos M
      constructor
      · intro hnil
        rw [hnil, List.length_nil] at hlen
        cases u with
        | nil => rfl
        | cons _ u' =>
          simp only [List.length_cons, Nat.succ_mul] at hlen
          omega
      · intro h0
        have hu : u = [] := List.eq_nil_of_length_eq_zero h0
        subst hu
        rfl
    rw [hstep, eval_initStepBC M u _ x hr, ih]
    rfl

theorem eval_initCfgBC (M : TM) (W x : Word) :
    (initCfgBC M).eval [W] [x] = encCfg M W.length (M.init x) := by
  simp only [initCfgBC, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
    vec1_zero, Fn.eval_projN, List.getD_cons_zero]
  rw [eval_initCfgBC_buildRev M x W]
  exact eval_revBlocks (fun j => encBlock M (cfgBlock M (M.init x) j)) W
    (fun j _ => length_encBlock M _)

/-! ## 5. Single-Step TM Transition (`stepCfgBC`) and Multi-Step Iteration (`runCfgBC`) -/

/-- One transition of `M`, returning `c` unchanged if `M` has already halted (`M.step c = none`). -/
def TM.stepOrSelf (M : TM) (c : Cfg M.k M.Q M.G) : Cfg M.k M.Q M.G :=
  match M.step c with
  | none => c
  | some c' => c'

theorem TM.run_succ_eq_stepOrSelf (M : TM) (t : Nat) (c : Cfg M.k M.Q M.G) :
    M.run (t + 1) c = M.stepOrSelf (M.run t c) := by
  induction t generalizing c with
  | zero =>
    simp only [TM.run, TM.stepOrSelf]
    cases M.step c <;> rfl
  | succ t ih =>
    simp only [TM.run]
    cases h : M.step c with
    | none =>
      simp [TM.stepOrSelf, h]
    | some c' =>
      exact ih c'

theorem Tape.consB_getD {Γ : Type} [DecidableEq Γ] (blank a : Γ) (l : List Γ) (k : Nat) :
    (Tape.consB blank a l).getD k blank = (a :: l).getD k blank := by
  cases l with
  | nil =>
    simp only [Tape.consB]
    by_cases h : a = blank
    · subst h
      simp only [↓reduceIte]
      cases k <;> rfl
    · simp [h]
  | cons b l' => rfl

theorem Tape.consB_length_le {Γ : Type} [DecidableEq Γ] (blank a : Γ) (l : List Γ) :
    (Tape.consB blank a l).length ≤ l.length + 1 := by
  cases l with
  | nil =>
    simp only [Tape.consB]
    by_cases h : a = blank <;> simp [h]
  | cons b l' =>
    simp [Tape.consB]

theorem Tape.move_left_length_le {Γ : Type} [DecidableEq Γ] (blank : Γ) (d : Dir) (t : Tape Γ) :
    (t.move blank d).left.length ≤ t.left.length + 1 := by
  rcases t with ⟨l, h, r⟩
  cases d with
  | L =>
    cases l <;> simp [Tape.move] <;> omega
  | R =>
    cases r <;> simp only [Tape.move] <;> exact Tape.consB_length_le blank h l
  | S =>
    simp [Tape.move]

theorem Tape.move_right_length_le {Γ : Type} [DecidableEq Γ] (blank : Γ) (d : Dir) (t : Tape Γ) :
    (t.move blank d).right.length ≤ t.right.length + 1 := by
  rcases t with ⟨l, h, r⟩
  cases d with
  | L =>
    cases l <;> simp only [Tape.move] <;> exact Tape.consB_length_le blank h r
  | R =>
    cases r <;> simp [Tape.move] <;> omega
  | S =>
    simp [Tape.move]

/-- Tape-length bound: every tape in `c` has `left.length ≤ L` and `right.length ≤ L`. -/
def TM.TapeBounded (M : TM) (L : Nat) (c : Cfg M.k M.Q M.G) : Prop :=
  ∀ i : Fin M.k, (c.tapes i).left.length ≤ L ∧ (c.tapes i).right.length ≤ L

theorem TM.tapeBounded_init (M : TM) (x : Word) :
    M.TapeBounded x.length (M.init x) := by
  intro i
  simp only [TM.init]
  by_cases hi : i.val = 0
  · simp only [hi, ↓reduceIte]
    cases x <;> simp [TM.inputTape]
  · simp [hi, TM.blankTape]

theorem TM.tapeBounded_stepOrSelf (M : TM) {L : Nat} {c : Cfg M.k M.Q M.G}
    (h : M.TapeBounded L c) :
    M.TapeBounded (L + 1) (M.stepOrSelf c) := by
  intro i
  unfold TM.stepOrSelf TM.step
  rcases h i with ⟨hl, hr⟩
  cases hδ : M.δ c.state (fun i => (c.tapes i).head) with
  | none =>
    simp only
    exact ⟨by omega, by omega⟩
  | some qwd =>
    rcases qwd with ⟨q', w, d⟩
    simp only
    have h1 := Tape.move_left_length_le M.blank (d i) ((c.tapes i).write (w i))
    have h2 := Tape.move_right_length_le M.blank (d i) ((c.tapes i).write (w i))
    have hw_l : ((c.tapes i).write (w i)).left.length = (c.tapes i).left.length := rfl
    have hw_r : ((c.tapes i).write (w i)).right.length = (c.tapes i).right.length := rfl
    rw [hw_l] at h1
    rw [hw_r] at h2
    exact ⟨by omega, by omega⟩

theorem TM.tapeBounded_run (M : TM) (x : Word) (t : Nat) :
    M.TapeBounded (x.length + t) (M.run t (M.init x)) := by
  induction t with
  | zero =>
    simp only [TM.run, Nat.add_zero]
    exact M.tapeBounded_init x
  | succ t ih =>
    rw [M.run_succ_eq_stepOrSelf]
    exact M.tapeBounded_stepOrSelf ih

theorem getD_eq_default_of_le_length {α : Type _} (l : List α) (d : α) (j : Nat)
    (hj : l.length ≤ j) :
    l.getD j d = d := by
  induction l generalizing j with
  | nil => simp [List.getD]
  | cons a l ih =>
    cases j with
    | zero => simp at hj
    | succ j' =>
      simp only [List.length_cons] at hj
      exact ih j' (by omega)

theorem cfgBlock_eq_blankBlock_of_tapeBounded (M : TM) {L : Nat} {c : Cfg M.k M.Q M.G}
    (h : M.TapeBounded L c) (j : Nat) (hj0 : 0 < j) (hjL : L ≤ j) :
    cfgBlock M c j = blankBlock M := by
  have hj_ne : j ≠ 0 := by omega
  simp only [cfgBlock, hj_ne, ↓reduceIte, blankBlock]
  congr 1
  · funext i
    exact getD_eq_default_of_le_length (c.tapes i).left M.blank j (Nat.le_trans (h i).1 hjL)
  · funext i
    exact getD_eq_default_of_le_length (c.tapes i).right M.blank j (Nat.le_trans (h i).2 hjL)

/-- Compute the new `BlockData M` at index `j` from:
    - `b0`: block `0` of `c` (providing `c.state` and `(c.tapes i).head`)
    - `bPrev`: block `j - 1` of `c` (or `blankBlock M` if `j = 0`)
    - `bCur`: block `j` of `c`
    - `bNext`: block `j + 1` of `c` -/
def nextBlockData (M : TM) (b0 bPrev bCur bNext : BlockData M) : BlockData M :=
  match M.δ b0.state b0.headSym with
  | none => bCur
  | some (q', w, d) =>
    if bCur.isZero then
      { isZero := true
        state := q'
        headSym := fun i =>
          match d i with
          | .L => bCur.leftSym i
          | .R => bCur.rightSym i
          | .S => w i
        leftSym := fun i =>
          match d i with
          | .L => bNext.leftSym i
          | .R => w i
          | .S => bCur.leftSym i
        rightSym := fun i =>
          match d i with
          | .L => w i
          | .R => bNext.rightSym i
          | .S => bCur.rightSym i }
    else
      { isZero := false
        state := ⟨0, M.hQ⟩
        headSym := fun _ => M.blank
        leftSym := fun i =>
          match d i with
          | .L => bNext.leftSym i
          | .R => bPrev.leftSym i
          | .S => bCur.leftSym i
        rightSym := fun i =>
          match d i with
          | .L => bPrev.rightSym i
          | .R => bNext.rightSym i
          | .S => bCur.rightSym i }

theorem move_head_eq (M : TM) (t : Tape (Fin M.G)) (w : Fin M.G) (d : Dir) :
    ((t.write w).move M.blank d).head =
      match d with
      | .L => t.left.getD 0 M.blank
      | .R => t.right.getD 0 M.blank
      | .S => w := by
  rcases t with ⟨l, h, r⟩
  cases d with
  | L => cases l <;> rfl
  | R => cases r <;> rfl
  | S => rfl

theorem move_left_zero_eq (M : TM) (t : Tape (Fin M.G)) (w : Fin M.G) (d : Dir) :
    ((t.write w).move M.blank d).left.getD 0 M.blank =
      match d with
      | .L => t.left.getD 1 M.blank
      | .R => w
      | .S => t.left.getD 0 M.blank := by
  rcases t with ⟨l, h, r⟩
  cases d with
  | L =>
    cases l with
    | nil => rfl
    | cons a l' => rfl
  | R =>
    cases r <;> {
      simp only [Tape.write, Tape.move]
      rw [Tape.consB_getD M.blank w l 0]
      rfl
    }
  | S => rfl

theorem move_right_zero_eq (M : TM) (t : Tape (Fin M.G)) (w : Fin M.G) (d : Dir) :
    ((t.write w).move M.blank d).right.getD 0 M.blank =
      match d with
      | .L => w
      | .R => t.right.getD 1 M.blank
      | .S => t.right.getD 0 M.blank := by
  rcases t with ⟨l, h, r⟩
  cases d with
  | L =>
    cases l <;> {
      simp only [Tape.write, Tape.move]
      rw [Tape.consB_getD M.blank w r 0]
      rfl
    }
  | R =>
    cases r with
    | nil => rfl
    | cons a r' => rfl
  | S => rfl

theorem move_left_succ_eq (M : TM) (t : Tape (Fin M.G)) (w : Fin M.G) (d : Dir) (j : Nat) :
    ((t.write w).move M.blank d).left.getD (j + 1) M.blank =
      match d with
      | .L => t.left.getD (j + 2) M.blank
      | .R => t.left.getD j M.blank
      | .S => t.left.getD (j + 1) M.blank := by
  rcases t with ⟨l, h, r⟩
  cases d with
  | L =>
    cases l with
    | nil => rfl
    | cons a l' => rfl
  | R =>
    cases r <;> {
      simp only [Tape.write, Tape.move]
      rw [Tape.consB_getD M.blank w l (j + 1)]
      rfl
    }
  | S => rfl

theorem move_right_succ_eq (M : TM) (t : Tape (Fin M.G)) (w : Fin M.G) (d : Dir) (j : Nat) :
    ((t.write w).move M.blank d).right.getD (j + 1) M.blank =
      match d with
      | .L => t.right.getD j M.blank
      | .R => t.right.getD (j + 2) M.blank
      | .S => t.right.getD (j + 1) M.blank := by
  rcases t with ⟨l, h, r⟩
  cases d with
  | L =>
    cases l <;> {
      simp only [Tape.write, Tape.move]
      rw [Tape.consB_getD M.blank w r (j + 1)]
      rfl
    }
  | R =>
    cases r with
    | nil => rfl
    | cons a r' => rfl
  | S => rfl

theorem nextBlockData_correct (M : TM) (c : Cfg M.k M.Q M.G) (j : Nat) :
    nextBlockData M
      (cfgBlock M c 0)
      (if j = 0 then blankBlock M else cfgBlock M c (j - 1))
      (cfgBlock M c j)
      (cfgBlock M c (j + 1)) =
    cfgBlock M (M.stepOrSelf c) j := by
  have hb0_state : (cfgBlock M c 0).state = c.state := rfl
  have hb0_head : (cfgBlock M c 0).headSym = fun i => (c.tapes i).head := rfl
  unfold nextBlockData TM.stepOrSelf TM.step
  rw [hb0_state, hb0_head]
  cases hδ : M.δ c.state (fun i => (c.tapes i).head) with
  | none => rfl
  | some qwd =>
    rcases qwd with ⟨q', w, d⟩
    cases j with
    | zero =>
      simp only [cfgBlock, ↓reduceIte, Nat.zero_add, Nat.add_one_ne_zero]
      congr 1
      · funext i; exact (move_head_eq M (c.tapes i) (w i) (d i)).symm
      · funext i; exact (move_left_zero_eq M (c.tapes i) (w i) (d i)).symm
      · funext i; exact (move_right_zero_eq M (c.tapes i) (w i) (d i)).symm
    | succ j' =>
      have hj_ne1 : j' + 1 ≠ 0 := by omega
      have hj_ne2 : j' + 1 + 1 ≠ 0 := by omega
      simp only [cfgBlock, hj_ne1, hj_ne2, Nat.add_sub_cancel, Bool.false_eq_true, ↓reduceIte]
      congr 1
      · funext i
        rw [move_left_succ_eq M (c.tapes i) (w i) (d i) j']
        cases d i <;> cases j' <;> rfl
      · funext i
        rw [move_right_succ_eq M (c.tapes i) (w i) (d i) j']
        cases d i <;> cases j' <;> rfl

/-- Decode `w0` (length `D`) and `wWin` (length `3 * D`) into `(b0, bPrev, bCur, bNext)`
    and encode `nextBlockData M b0 bPrev bCur bNext`. -/
def stepBlockWord (M : TM) (w0 wWin : Word) : Word :=
  let D := blockWidth M
  let b0 := decBlock M (padFalse D w0)
  let bPrev := decBlock M (padFalse D wWin)
  let bCur := decBlock M (padFalse D (wWin.drop D))
  let bNext := decBlock M (padFalse D ((wWin.drop D).drop D))
  encBlock M (nextBlockData M b0 bPrev bCur bNext)

theorem padFalse_drop_tableOf_ge {D : Nat} (f : Nat → Word) (N : Nat)
    (hf : ∀ j : Nat, j < N → (f j).length = D) {j : Nat} (hj : N ≤ j) :
    padFalse D ((tableOf f N).drop (j * D)) = List.replicate D false := by
  have hlen : (tableOf f N).length ≤ j * D := by
    rw [length_tableOf f N hf]
    exact Nat.mul_le_mul_right D hj
  rw [List.drop_eq_nil_of_le hlen, padFalse_nil]

theorem stepBlockWord_on_encCfg (M : TM) {N : Nat} {c : Cfg M.k M.Q M.G}
    (hbnd : M.TapeBounded N c) {j : Nat} (hj : j < N) :
    stepBlockWord M
      (padFalse (blockWidth M) (encCfg M N c))
      (padFalse (blockWidth M + (blockWidth M + blockWidth M))
        ((List.replicate (blockWidth M) false ++ encCfg M N c).drop (j * blockWidth M))) =
    encBlock M (cfgBlock M (M.stepOrSelf c) j) := by
  let D := blockWidth M
  let f := fun k => encBlock M (cfgBlock M c k)
  have hf : ∀ k : Nat, k < N → (f k).length = D := fun k _ => length_encBlock M _
  have h0N : 0 < N := by omega
  have hw0 : padFalse D (padFalse D (encCfg M N c)) = encBlock M (cfgBlock M c 0) := by
    rw [padFalse_self (length_padFalse D _)]
    have h0 := padFalse_drop_tableOf f N hf h0N
    simpa [encCfg, f, D] using h0
  let wShift := (List.replicate D false ++ encCfg M N c).drop (j * D)
  have hwin_split :
      padFalse (D + (D + D)) wShift =
        padFalse D wShift ++ (padFalse D (wShift.drop D) ++ padFalse D ((wShift.drop D).drop D)) := by
    rw [padFalse_add D (D + D) wShift, padFalse_add D D (wShift.drop D)]
  have hprev : decBlock M (padFalse D (padFalse (D + (D + D)) wShift)) =
      (if j = 0 then blankBlock M else cfgBlock M c (j - 1)) := by
    rw [hwin_split, padFalse_eq_of_length (length_padFalse D wShift)]
    cases j with
    | zero =>
      dsimp only [wShift]
      simp only [Nat.zero_mul, List.drop_zero, ↓reduceIte]
      rw [padFalse_eq_of_length (@List.length_replicate _ D false), decBlock_replicate_false M]
    | succ j' =>
      have hj1 : j' + 1 ≠ 0 := by omega
      simp only [hj1, ↓reduceIte, Nat.add_sub_cancel]
      dsimp only [wShift, encCfg]
      rw [Nat.succ_mul, Nat.add_comm (j' * D) D, ← List.drop_drop,
          drop_append_of_length (@List.length_replicate _ D false)]
      rw [padFalse_drop_tableOf f N hf (by omega), decBlock_encBlock M]
  have hcur : decBlock M (padFalse D ((padFalse (D + (D + D)) wShift).drop D)) =
      cfgBlock M c j := by
    rw [hwin_split, drop_append_of_length (length_padFalse D wShift),
        padFalse_eq_of_length (length_padFalse D (wShift.drop D))]
    dsimp only [wShift, encCfg]
    rw [List.drop_drop, Nat.add_comm (j * D) D, ← List.drop_drop,
        drop_append_of_length (@List.length_replicate _ D false)]
    rw [padFalse_drop_tableOf f N hf hj, decBlock_encBlock M]
  have hnext : decBlock M (padFalse D (((padFalse (D + (D + D)) wShift).drop D).drop D)) =
      cfgBlock M c (j + 1) := by
    rw [hwin_split, drop_append_of_length (length_padFalse D wShift),
        drop_append_of_length (length_padFalse D (wShift.drop D)),
        padFalse_self (length_padFalse D ((wShift.drop D).drop D))]
    dsimp only [wShift, encCfg]
    rw [List.drop_drop, List.drop_drop,
        show j * D + (D + D) = D + (j + 1) * D by rw [Nat.succ_mul]; omega,
        ← List.drop_drop,
        drop_append_of_length (@List.length_replicate _ D false)]
    by_cases hj1 : j + 1 < N
    · rw [padFalse_drop_tableOf f N hf hj1, decBlock_encBlock M]
    · have hj_eq : j + 1 = N := by omega
      rw [padFalse_drop_tableOf_ge f N hf (j := j + 1) (by omega), decBlock_replicate_false M, hj_eq]
      exact (cfgBlock_eq_blankBlock_of_tapeBounded M hbnd N h0N (Nat.le_refl N)).symm
  unfold stepBlockWord
  dsimp only
  change encBlock M (nextBlockData M
    (decBlock M (padFalse D (padFalse D (encCfg M N c))))
    (decBlock M (padFalse D (padFalse (D + (D + D)) wShift)))
    (decBlock M (padFalse D ((padFalse (D + (D + D)) wShift).drop D)))
    (decBlock M (padFalse D (((padFalse (D + (D + D)) wShift).drop D).drop D)))) = _
  rw [hw0, decBlock_encBlock M, hprev, hcur, hnext, nextBlockData_correct M c j]

/-- Safe function `Fn 0 3` taking `[y, wShift, r]` and prepending the updated block onto `r`. -/
def stepBlockBranch (M : TM) : Fn 0 3 :=
  let D := blockWidth M
  branchPrefix D (fun w0 =>
    branchPrefix (D + (D + D)) (fun wWin =>
      prependConst (stepBlockWord M w0 wWin)))

theorem eval_stepBlockBranch (M : TM) (y wShift r : Word) :
    (stepBlockBranch M).eval [] [y, wShift, r] =
      stepBlockWord M (padFalse (blockWidth M) y)
        (padFalse (blockWidth M + (blockWidth M + blockWidth M)) wShift) ++ r := by
  unfold stepBlockBranch
  rw [eval_branchPrefix (blockWidth M) _ y [wShift, r] rfl,
      eval_branchPrefix (blockWidth M + (blockWidth M + blockWidth M)) _ wShift [r] rfl,
      eval_prependConst]
  rfl

/-- Safe step `Fn 1 2` for `stepCfgBC`: on normal `[u]` (`|u| = j`) and safe `[r, y]`,
    prepends block `j` of `M.stepOrSelf c` onto `r`. -/
def stepCfgStepBC (M : TM) : Fn 1 2 :=
  let D := blockWidth M
  let padY : Fn 1 2 :=
    .comp (prependConst (List.replicate D false)) Fin.elim0 (vec1 (.projS ⟨1, by decide⟩))
  let wShift : Fn 1 2 :=
    .comp (dropBlock D) (vec1 (.projN ⟨0, Nat.zero_lt_one⟩)) (vec1 padY)
  .comp (stepBlockBranch M) Fin.elim0
    (vec3 (.projS ⟨1, by decide⟩) wShift (.projS ⟨0, by decide⟩))

theorem eval_stepCfgStepBC (M : TM) (u r y : Word) :
    (stepCfgStepBC M).eval [u] [r, y] =
      stepBlockWord M (padFalse (blockWidth M) y)
        (padFalse (blockWidth M + (blockWidth M + blockWidth M))
          ((List.replicate (blockWidth M) false ++ y).drop (u.length * blockWidth M))) ++ r := by
  simp only [stepCfgStepBC, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
    vec3_zero, vec3_succ, vec2_zero, vec2_one, vec1_zero,
    Fn.eval_projN, Fn.eval_projS, eval_prependConst, eval_dropBlock,
    List.getD_cons_zero, List.getD_cons_succ]
  exact eval_stepBlockBranch M y _ r

/-- BC program `stepCfgBC M : Fn 1 1` computing `encCfg M W.length (M.stepOrSelf c)`
    on normal clock `[W]` and safe input `[encCfg M W.length c]`. -/
def stepCfgBC (M : TM) : Fn 1 1 :=
  let buildRev : Fn 1 1 := .srec constZero (stepCfgStepBC M) (stepCfgStepBC M)
  .comp (revBlocks (blockWidth M))
    (vec1 (.projN ⟨0, Nat.zero_lt_one⟩))
    (vec1 buildRev)

theorem eval_stepCfgBC_buildRev (M : TM) {N : Nat} {c : Cfg M.k M.Q M.G}
    (hbnd : M.TapeBounded N c) (u : Word) (hu : u.length ≤ N) :
    (Fn.srec constZero (stepCfgStepBC M) (stepCfgStepBC M)).eval [u] [encCfg M N c] =
      concatRev (fun j => encBlock M (cfgBlock M (M.stepOrSelf c) j)) u.length := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    simp only [List.length_cons] at hu
    have hstep : (Fn.srec constZero (stepCfgStepBC M) (stepCfgStepBC M)).eval [b :: u] [encCfg M N c] =
        (stepCfgStepBC M).eval [u]
          [(Fn.srec constZero (stepCfgStepBC M) (stepCfgStepBC M)).eval [u] [encCfg M N c], encCfg M N c] := by
      cases b <;> simp [Fn.eval_srec_cons]
    rw [hstep, eval_stepCfgStepBC, stepBlockWord_on_encCfg M hbnd (by omega), ih (by omega)]
    rfl

theorem eval_stepCfgBC (M : TM) (W : Word) {c : Cfg M.k M.Q M.G}
    (hbnd : M.TapeBounded W.length c) :
    (stepCfgBC M).eval [W] [encCfg M W.length c] =
      encCfg M W.length (M.stepOrSelf c) := by
  simp only [stepCfgBC, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
    vec1_zero, Fn.eval_projN, List.getD_cons_zero]
  rw [eval_stepCfgBC_buildRev M hbnd W (Nat.le_refl W.length)]
  exact eval_revBlocks (fun j => encBlock M (cfgBlock M (M.stepOrSelf c) j)) W
    (fun j _ => length_encBlock M _)

/-- Iterate `stepCfgBC M` for `T.length` transitions using normal clock `W`:
    `runCfgBC M : Fn 2 1` takes normal `[T, W]` and safe `[y]`. -/
def runCfgBC (M : TM) : Fn 2 1 :=
  let step : Fn 2 2 :=
    .comp (stepCfgBC M) (vec1 (.projN ⟨1, by decide⟩)) (vec1 (.projS ⟨0, by decide⟩))
  .srec (.projS ⟨0, Nat.zero_lt_one⟩) step step

theorem eval_runCfgBC (M : TM) (T W x : Word) (hW : x.length + T.length ≤ W.length) :
    (runCfgBC M).eval [T, W] [encCfg M W.length (M.init x)] =
      encCfg M W.length (M.run T.length (M.init x)) := by
  induction T with
  | nil => rfl
  | cons b T ih =>
    simp only [List.length_cons] at hW ⊢
    have hstep : (runCfgBC M).eval [b :: T, W] [encCfg M W.length (M.init x)] =
        (stepCfgBC M).eval [W] [(runCfgBC M).eval [T, W] [encCfg M W.length (M.init x)]] := by
      cases b <;> simp [runCfgBC, Fn.eval_srec_cons, List.ofFn_zero, List.ofFn_succ]
    have hbnd_T : M.TapeBounded W.length (M.run T.length (M.init x)) := by
      intro i
      rcases M.tapeBounded_run x T.length i with ⟨hl, hr⟩
      exact ⟨by omega, by omega⟩
    rw [hstep, ih (by omega), eval_stepCfgBC M W hbnd_T, ← M.run_succ_eq_stepOrSelf]

/-! ## 6. Output Decoding (`outputCfgBC`) and Main Completeness Theorem (`defFun_eq_FP`) -/

/-- Pure specification of one step of output extraction from block `b` onto accumulator `r`. -/
def outStepWord (M : TM) (b : BlockData M) (r : Word) : Word :=
  let r1 :=
    match M.decodeBit (b.rightSym ⟨0, M.hk⟩) with
    | some bit => bit :: r
    | none => []
  if b.isZero then
    match M.decodeBit (b.headSym ⟨0, M.hk⟩) with
    | some bit0 => bit0 :: r1
    | none => []
  else
    r1

/-- BC program `Fn 0 1` implementing `outStepWord M (decBlock M w)` on safe argument `[r]`. -/
def outBlockFn (M : TM) (w : Word) : Fn 0 1 :=
  let b := decBlock M w
  if b.isZero then
    match M.decodeBit (b.headSym ⟨0, M.hk⟩), M.decodeBit (b.rightSym ⟨0, M.hk⟩) with
    | none, _ => constZero
    | some bit0, none => constWord [bit0]
    | some bit0, some bit1 => prependConst [bit0, bit1]
  else
    match M.decodeBit (b.rightSym ⟨0, M.hk⟩) with
    | none => constZero
    | some bit => prependConst [bit]

theorem eval_outBlockFn (M : TM) (w r : Word) :
    (outBlockFn M w).eval [] [r] = outStepWord M (decBlock M w) r := by
  unfold outBlockFn outStepWord
  dsimp only
  cases (decBlock M w).isZero with
  | false =>
    cases M.decodeBit ((decBlock M w).rightSym ⟨0, M.hk⟩) <;> simp
  | true =>
    cases M.decodeBit ((decBlock M w).headSym ⟨0, M.hk⟩) with
    | none =>
      cases M.decodeBit ((decBlock M w).rightSym ⟨0, M.hk⟩) <;> simp
    | some bit0 =>
      cases M.decodeBit ((decBlock M w).rightSym ⟨0, M.hk⟩) <;> simp

/-- Safe step `Fn 1 2` for `outputCfgBC`: on normal `[u]` (`|u| = k`) and safe `[r, yRev]`,
    extracts block `k` from `yRev` (`= encBlock M (cfgBlock M c (N - 1 - k))`) and applies `outBlockFn M`. -/
def outCfgStepBC (M : TM) : Fn 1 2 :=
  let D := blockWidth M
  let wBlock : Fn 1 2 :=
    .comp (dropBlock D) (vec1 (.projN ⟨0, Nat.zero_lt_one⟩)) (vec1 (.projS ⟨1, by decide⟩))
  .comp (branchPrefix D (outBlockFn M)) Fin.elim0
    (vec2 wBlock (.projS ⟨0, by decide⟩))

theorem eval_outCfgStepBC (M : TM) (u r yRev : Word) :
    (outCfgStepBC M).eval [u] [r, yRev] =
      outStepWord M (decBlock M (padFalse (blockWidth M) (yRev.drop (u.length * blockWidth M)))) r := by
  simp only [outCfgStepBC, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
    vec2_zero, vec2_one, vec1_zero, Fn.eval_projN, Fn.eval_projS, eval_dropBlock,
    List.getD_cons_zero, List.getD_cons_succ]
  rw [eval_branchPrefix (blockWidth M) (outBlockFn M) _ [r] rfl, eval_outBlockFn]

theorem decodeBit_blank (M : TM) : M.decodeBit M.blank = none := by
  rfl

theorem readBits_drop_step (M : TM) (right : List (Fin M.G)) (j : Nat) :
    (match M.decodeBit (right.getD j M.blank) with
     | some bit => bit :: M.readBits (right.drop (j + 1))
     | none => []) = M.readBits (right.drop j) := by
  induction right generalizing j with
  | nil =>
    simp [List.getD, TM.readBits]
  | cons a l ih =>
    cases j with
    | zero =>
      rfl
    | succ j' =>
      simpa [List.getD] using ih j'

theorem eval_outExtract_lt (M : TM) {N : Nat} {c : Cfg M.k M.Q M.G}
    (hbnd : (c.tapes ⟨0, M.hk⟩).right.length < N) :
    ∀ (u : Word), u.length < N →
      (Fn.srec constZero (outCfgStepBC M) (outCfgStepBC M)).eval [u]
        [concatRev (fun j => encBlock M (cfgBlock M c j)) N] =
      M.readBits (((c.tapes ⟨0, M.hk⟩).right).drop (N - u.length))
  | [], _ => by
    simp only [List.length_nil, Nat.sub_zero, Fn.eval_srec_nil, eval_constZero]
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | b :: u, hu => by
    simp only [List.length_cons] at hu ⊢
    have hstep : (Fn.srec constZero (outCfgStepBC M) (outCfgStepBC M)).eval [b :: u]
        [concatRev (fun j => encBlock M (cfgBlock M c j)) N] =
      (outCfgStepBC M).eval [u]
        [(Fn.srec constZero (outCfgStepBC M) (outCfgStepBC M)).eval [u]
          [concatRev (fun j => encBlock M (cfgBlock M c j)) N],
         concatRev (fun j => encBlock M (cfgBlock M c j)) N] := by
      cases b <;> simp [Fn.eval_srec_cons]
    rw [hstep, eval_outCfgStepBC,
        padFalse_drop_concatRev (fun j => encBlock M (cfgBlock M c j)) N
          (fun j _ => length_encBlock M _) u.length (by omega),
        decBlock_encBlock M,
        eval_outExtract_lt M hbnd u (by omega)]
    have hj_pos : N - 1 - u.length ≠ 0 := by omega
    have hj_add : (N - 1 - u.length) + 1 = N - u.length := by omega
    have hj_sub : N - (u.length + 1) = N - 1 - u.length := by omega
    simp only [outStepWord, cfgBlock, hj_pos, Bool.false_eq_true, ↓reduceIte,
      ← hj_add, hj_sub]
    exact readBits_drop_step M (c.tapes ⟨0, M.hk⟩).right (N - 1 - u.length)

/-- BC program `outputCfgBC M : Fn 1 1` extracting `M.output c` from `encCfg M W.length c`
    using normal clock `[W]`. -/
def outputCfgBC (M : TM) : Fn 1 1 :=
  let yRev : Fn 1 1 :=
    .comp (revBlocks (blockWidth M))
      (vec1 (.projN ⟨0, Nat.zero_lt_one⟩))
      (vec1 (.projS ⟨0, Nat.zero_lt_one⟩))
  let extract : Fn 1 1 := .srec constZero (outCfgStepBC M) (outCfgStepBC M)
  .comp extract (vec1 (.projN ⟨0, Nat.zero_lt_one⟩)) (vec1 yRev)

theorem eval_outputCfgBC (M : TM) (W : Word) {c : Cfg M.k M.Q M.G}
    (hbnd : (c.tapes ⟨0, M.hk⟩).right.length < W.length) :
    (outputCfgBC M).eval [W] [encCfg M W.length c] = M.output c := by
  simp only [outputCfgBC, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
    vec1_zero, Fn.eval_projN, Fn.eval_projS, List.getD_cons_zero]
  have hrev : (revBlocks (blockWidth M)).eval [W] [encCfg M W.length c] =
      concatRev (fun j => encBlock M (cfgBlock M c j)) W.length :=
    eval_revBlocks_tableOf (fun j => encBlock M (cfgBlock M c j)) W (fun j _ => length_encBlock M _)
  rw [hrev]
  cases W with
  | nil =>
    simp at hbnd
  | cons b u =>
    have hstep : (Fn.srec constZero (outCfgStepBC M) (outCfgStepBC M)).eval [b :: u]
        [concatRev (fun j => encBlock M (cfgBlock M c j)) (b :: u).length] =
      (outCfgStepBC M).eval [u]
        [(Fn.srec constZero (outCfgStepBC M) (outCfgStepBC M)).eval [u]
          [concatRev (fun j => encBlock M (cfgBlock M c j)) (b :: u).length],
         concatRev (fun j => encBlock M (cfgBlock M c j)) (b :: u).length] := by
      cases b <;> simp [Fn.eval_srec_cons]
    have hu_lt : u.length < (b :: u).length := by simp
    rw [hstep, eval_outCfgStepBC,
        padFalse_drop_concatRev (fun j => encBlock M (cfgBlock M c j)) (b :: u).length
          (fun j _ => length_encBlock M _) u.length hu_lt,
        decBlock_encBlock M,
        eval_outExtract_lt M hbnd u hu_lt]
    have h0 : (b :: u).length - 1 - u.length = 0 := by simp
    have h1 : (b :: u).length - u.length = 1 := by simp
    rw [h0, h1]
    simp only [outStepWord, cfgBlock, ↓reduceIte]
    have hr0 := readBits_drop_step M (c.tapes ⟨0, M.hk⟩).right 0
    simp only [Nat.zero_add, List.drop_zero] at hr0
    rw [hr0]
    rfl

/-- If `M.HaltsWithin x T y`, then running `M` for `T` steps yields a configuration whose
    output is `y`. -/
theorem TM.output_run_of_haltsWithin (M : TM) {x : Word} {T : Nat} {y : Word}
    (h : M.HaltsWithin x T y) :
    M.output (M.run T (M.init x)) = y := by
  rcases h with ⟨s, hs, hstep, hout⟩
  have hadd : T = s + (T - s) := by omega
  rw [hadd, M.run_add s (T - s) (M.init x),
      M.run_of_step_none hstep (T - s), hout]

/-- Full BC program `simTM M p : Fn 1 0` simulating `M : TM` for `p(|x|)` transitions
    on input `[x], []`. -/
def simTM (M : TM) (p : Poly) : Fn 1 0 :=
  let clockPoly : Poly := .add (.add .var p) (.const 1)
  let wClock : Fn 1 0 := polyWord clockPoly
  let tSteps : Fn 1 0 := polyWord p
  let initCfg : Fn 1 0 := .comp (initCfgBC M) (vec1 wClock) (vec1 (.projN ⟨0, Nat.zero_lt_one⟩))
  let finalCfg : Fn 1 0 := .comp (runCfgBC M) (vec2 tSteps wClock) (vec1 initCfg)
  .comp (outputCfgBC M) (vec1 wClock) (vec1 finalCfg)

theorem eval_simTM (M : TM) (p : Poly) (x : Word) :
    (simTM M p).eval [x] [] = M.output (M.run (p.eval x.length) (M.init x)) := by
  let W := (polyWord (.add (.add .var p) (.const 1))).eval [x] []
  let T := (polyWord p).eval [x] []
  have hW_len : W.length = x.length + p.eval x.length + 1 := by
    simp [W]
  have hT_len : T.length = p.eval x.length := by
    simp [T]
  simp only [simTM, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
    vec2_zero, vec2_one, vec1_zero, Fn.eval_projN, List.getD_cons_zero]
  change (outputCfgBC M).eval [W] [(runCfgBC M).eval [T, W] [(initCfgBC M).eval [W] [x]]] = _
  rw [eval_initCfgBC M W x,
      eval_runCfgBC M T W x (by omega),
      hT_len]
  apply eval_outputCfgBC M W
  have hbnd := (M.tapeBounded_run x (p.eval x.length) ⟨0, M.hk⟩).2
  omega

/-- **Bellantoni–Cook Polynomial-Time Completeness (`FP f → BCDefinable f`)**:
    Every word function computable in polynomial time by a multi-tape Turing machine
    is definable in the Bellantoni–Cook safe recursion algebra. -/
theorem bc_completeness (f : Word → Word) (h : FP f) : BCDefinable f := by
  rcases h with ⟨M, p, hM⟩
  refine ⟨simTM M p, fun x => ?_⟩
  rw [eval_simTM M p x]
  exact M.output_run_of_haltsWithin (hM x)

/-- **Bellantoni–Cook Theorem (1992) (`defFun_eq_FP`)**:
    A unary word function `f : Word → Word` is definable by a closed Bellantoni–Cook
    program `prog : Fn 1 0` if and only if `f ∈ FP`. -/
theorem defFun_eq_FP (f : Word → Word) :
    (∃ prog : Fn 1 0, ∀ x : Word, prog.eval [x] [] = f x) ↔ FP f :=
  ⟨bc_soundness f, bc_completeness f⟩

/-- Equivalent formulation of `defFun_eq_FP` using `BCDefinable`. -/
theorem bcDefinable_iff_FP (f : Word → Word) :
    BCDefinable f ↔ FP f :=
  defFun_eq_FP f

end FeasibleUnivalence.BC
