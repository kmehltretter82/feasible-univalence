/-
  FeasibleUnivalence/BC/Soundness.lean

  Polynomial-time soundness of the Bellantoni–Cook function algebra (`BCDefinable f → FP f`):
  1. Compiles every BC program `f : Fn n m` into a structured stack program `compileBC base f : Stmt`
     and synthesizes an explicit polynomial time bound `f.timePoly : Poly` purely from the
     syntax of `f`.
  2. Proves that `compileBC base f` evaluates `f.eval xs ys` into stack `base` within
     `f.timePoly.eval K` steps whenever all input words in `xs` and `ys` have length `≤ K`.
  3. Combines with `stmtToTM_haltsWithin` from `CompileStmt.lean` to obtain a multi-tape
     Turing machine `M : TM` and polynomial `p : Poly` witnessing `FP f`.
-/

import FeasibleUnivalence.BC.Syntax
import FeasibleUnivalence.BC.CompileStmt

namespace FeasibleUnivalence.BC

/-! ## 1. Extensionality & Frame Helpers on `Stacks` -/

theorem Stacks.set_set_same (σ : Stacks) (i : Nat) (w₁ w₂ : Word) :
    (σ.set i w₁).set i w₂ = σ.set i w₂ := by
  funext j
  simp only [Stacks.set]
  by_cases h : j = i <;> simp [h]

theorem Stacks.set_set_comm (σ : Stacks) {i j : Nat} (w₁ w₂ : Word) (hne : i ≠ j) :
    (σ.set i w₁).set j w₂ = (σ.set j w₂).set i w₁ := by
  funext k
  simp only [Stacks.set]
  by_cases hki : k = i
  · subst hki
    have hkj : k ≠ j := hne
    simp [hkj]
  · by_cases hkj : k = j
    · subst hkj; simp [hki]
    · simp [hki, hkj]

theorem Stacks.set_eq_self {σ : Stacks} {i : Nat} {w : Word} (h : σ i = w) :
    σ.set i w = σ := by
  funext j
  simp only [Stacks.set]
  by_cases hj : j = i
  · subst hj; simp [h]
  · simp [hj]

/-- Place a list of words `ws` into contiguous stacks `start, start + 1, ..., start + ws.length - 1`. -/
def setFrame (σ : Stacks) (start : Nat) : List Word → Stacks
  | [] => σ
  | w :: ws => (setFrame σ (start + 1) ws).set start w

@[simp] theorem setFrame_nil (σ : Stacks) (start : Nat) :
    setFrame σ start [] = σ := rfl

@[simp] theorem setFrame_cons (σ : Stacks) (start : Nat) (w : Word) (ws : List Word) :
    setFrame σ start (w :: ws) = (setFrame σ (start + 1) ws).set start w := rfl

theorem setFrame_outside (σ : Stacks) (start : Nat) (ws : List Word) (r : Nat)
    (hr : r < start ∨ start + ws.length ≤ r) :
    setFrame σ start ws r = σ r := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [setFrame_cons, List.length_cons] at hr ⊢
    have hne : r ≠ start := by omega
    rw [Stacks.set_other _ _ hne]
    exact ih (start + 1) (by omega)

theorem setFrame_get (σ : Stacks) (start : Nat) (ws : List Word) (i : Nat) (hi : i < ws.length) :
    setFrame σ start ws (start + i) = ws.getD i [] := by
  induction ws generalizing start i with
  | nil => contradiction
  | cons w ws ih =>
    simp only [setFrame_cons, List.length_cons] at hi ⊢
    cases i with
    | zero =>
      simp [List.getD]
    | succ i' =>
      have hne : start + (i' + 1) ≠ start := by omega
      rw [Stacks.set_other _ _ hne]
      have heq : start + (i' + 1) = (start + 1) + i' := by omega
      rw [heq, ih (start + 1) i' (by omega)]
      rfl

theorem setFrame_append (σ : Stacks) (start : Nat) (ws₁ ws₂ : List Word) :
    setFrame (setFrame σ (start + ws₁.length) ws₂) start ws₁ =
      setFrame σ start (ws₁ ++ ws₂) := by
  induction ws₁ generalizing start with
  | nil => simp
  | cons w ws₁ ih =>
    simp only [List.length_cons, List.cons_append, setFrame_cons]
    have hadd : start + (ws₁.length + 1) = (start + 1) + ws₁.length := by omega
    rw [hadd, ih (start + 1)]

theorem setFrame_set_below (σ : Stacks) (start : Nat) (ws : List Word)
    {i : Nat} (w : Word) (hi : i < start) :
    setFrame (σ.set i w) start ws = (setFrame σ start ws).set i w := by
  induction ws generalizing start with
  | nil => rfl
  | cons u ws ih =>
    simp only [setFrame_cons]
    rw [ih (start + 1) (by omega), Stacks.set_set_comm _ _ _ (by omega)]

/-! ## 2. Basic Stack Manipulation Macros in `Stmt` -/

/-- Empty stack `dst`. -/
def clearStack (dst : Nat) : Stmt :=
  .whileNE dst (.pop dst)

theorem exec_clearStack_aux (dst : Nat) :
    ∀ (w : Word) (σ : Stacks), σ dst = w →
      Exec (clearStack dst) σ (2 * w.length + 1) (σ.set dst [])
  | [], σ, hw => by
    have hdone := Exec.whileDone (body := .pop dst) hw
    rw [Stacks.set_eq_self hw]
    exact hdone
  | b :: w, σ, hw => by
    have hne : σ dst ≠ [] := by rw [hw]; exact List.cons_ne_nil b w
    have hpop : Exec (.pop dst) σ 1 (σ.set dst w) := by
      have hp := Exec.pop dst σ
      rw [hw] at hp
      exact hp
    have ih := exec_clearStack_aux dst w (σ.set dst w) (Stacks.set_same σ dst w)
    rw [Stacks.set_set_same] at ih
    have hstep := Exec.whileStep hne hpop ih
    have hcost : 1 + (2 * w.length + 1) + 1 = 2 * (b :: w).length + 1 := by
      simp [List.length_cons]; omega
    rw [hcost] at hstep
    exact hstep

theorem exec_clearStack (dst : Nat) (σ : Stacks) :
    Exec (clearStack dst) σ (2 * (σ dst).length + 1) (σ.set dst []) :=
  exec_clearStack_aux dst (σ dst) σ rfl

/-- Pop all bits from `src` and push them onto `dst` (reversing `src` onto `dst`). -/
def moveRev (src dst : Nat) : Stmt :=
  .whileNE src
    (.ifTop src .skip
      (.seq (.pop src) (.push dst false))
      (.seq (.pop src) (.push dst true)))

theorem exec_moveRev_aux {src dst : Nat} (hne : src ≠ dst) :
    ∀ (w : Word) (σ : Stacks), σ src = w →
      Exec (moveRev src dst) σ (4 * w.length + 1)
        ((σ.set src []).set dst (w.reverse ++ σ dst))
  | [], σ, hw => by
    have hdone := Exec.whileDone (i := src)
      (body := .ifTop src .skip (.seq (.pop src) (.push dst false)) (.seq (.pop src) (.push dst true))) hw
    have hst : ((σ.set src []).set dst ([].reverse ++ σ dst)) = σ := by
      simp only [List.reverse_nil, List.nil_append]
      rw [Stacks.set_eq_self hw, Stacks.set_eq_self rfl]
    rw [hst]
    exact hdone
  | b :: w, σ, hw => by
    have hne_nil : σ src ≠ [] := by rw [hw]; exact List.cons_ne_nil b w
    let body := Stmt.ifTop src .skip
      (.seq (.pop src) (.push dst false))
      (.seq (.pop src) (.push dst true))
    have hbody : Exec body σ 3 ((σ.set src w).set dst (b :: σ dst)) := by
      have hpop : Exec (.pop src) σ 1 (σ.set src w) := by
        have hp := Exec.pop src σ
        rw [hw] at hp
        exact hp
      have hpush : Exec (.push dst b) (σ.set src w) 1 ((σ.set src w).set dst (b :: σ dst)) := by
        have hpu := Exec.push dst b (σ.set src w)
        rw [Stacks.set_other σ w hne.symm] at hpu
        exact hpu
      have hseq := Exec.seq hpop hpush
      cases b
      · exact Exec.if0 hw hseq
      · exact Exec.if1 hw hseq
    let σ' := (σ.set src w).set dst (b :: σ dst)
    have hσ'_src : σ' src = w := by
      simp [σ', Stacks.set_other _ _ hne]
    have ih := exec_moveRev_aux hne w σ' hσ'_src
    have hst : (σ'.set src []).set dst (w.reverse ++ σ' dst) =
        (σ.set src []).set dst ((b :: w).reverse ++ σ dst) := by
      simp only [σ', Stacks.set_same]
      rw [Stacks.set_set_comm (σ.set src w) (b :: σ dst) [] hne.symm,
          Stacks.set_set_same,
          Stacks.set_set_same,
          List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [hst] at ih
    have hstep := Exec.whileStep hne_nil hbody ih
    have hcost : 3 + (4 * w.length + 1) + 1 = 4 * (b :: w).length + 1 := by
      simp [List.length_cons]; omega
    rw [hcost] at hstep
    exact hstep

theorem exec_moveRev {src dst : Nat} (hne : src ≠ dst) (σ : Stacks) :
    Exec (moveRev src dst) σ (4 * (σ src).length + 1)
      ((σ.set src []).set dst ((σ src).reverse ++ σ dst)) :=
  exec_moveRev_aux hne (σ src) σ rfl

/-- Pop all bits from `tmp` and push each bit onto both `src` and `dst`. -/
def dupRev (tmp src dst : Nat) : Stmt :=
  .whileNE tmp
    (.ifTop tmp .skip
      (.seq (.pop tmp) (.seq (.push src false) (.push dst false)))
      (.seq (.pop tmp) (.seq (.push src true) (.push dst true))))

theorem exec_dupRev_aux {tmp src dst : Nat}
    (hts : tmp ≠ src) (htd : tmp ≠ dst) (hsd : src ≠ dst) :
    ∀ (u : Word) (σ : Stacks), σ tmp = u →
      Exec (dupRev tmp src dst) σ (5 * u.length + 1)
        (((σ.set tmp []).set src (u.reverse ++ σ src)).set dst (u.reverse ++ σ dst))
  | [], σ, hu => by
    have hdone := Exec.whileDone (i := tmp)
      (body := .ifTop tmp .skip
        (.seq (.pop tmp) (.seq (.push src false) (.push dst false)))
        (.seq (.pop tmp) (.seq (.push src true) (.push dst true)))) hu
    have hst : (((σ.set tmp []).set src ([].reverse ++ σ src)).set dst ([].reverse ++ σ dst)) = σ := by
      simp only [List.reverse_nil, List.nil_append]
      rw [Stacks.set_eq_self hu, Stacks.set_eq_self rfl, Stacks.set_eq_self rfl]
    rw [hst]
    exact hdone
  | b :: u, σ, hu => by
    have hne_nil : σ tmp ≠ [] := by rw [hu]; exact List.cons_ne_nil b u
    let body := Stmt.ifTop tmp .skip
      (.seq (.pop tmp) (.seq (.push src false) (.push dst false)))
      (.seq (.pop tmp) (.seq (.push src true) (.push dst true)))
    let σ' := ((σ.set tmp u).set src (b :: σ src)).set dst (b :: σ dst)
    have hbody : Exec body σ 4 σ' := by
      have hpop : Exec (.pop tmp) σ 1 (σ.set tmp u) := by
        have hp := Exec.pop tmp σ
        rw [hu] at hp
        exact hp
      have hpush1 : Exec (.push src b) (σ.set tmp u) 1 ((σ.set tmp u).set src (b :: σ src)) := by
        have hp1 := Exec.push src b (σ.set tmp u)
        rw [Stacks.set_other σ u hts.symm] at hp1
        exact hp1
      have hpush2 : Exec (.push dst b) ((σ.set tmp u).set src (b :: σ src)) 1 σ' := by
        have hp2 := Exec.push dst b ((σ.set tmp u).set src (b :: σ src))
        rw [Stacks.set_other _ _ hsd.symm, Stacks.set_other σ u htd.symm] at hp2
        exact hp2
      have hseq := Exec.seq hpop (Exec.seq hpush1 hpush2)
      cases b
      · exact Exec.if0 hu hseq
      · exact Exec.if1 hu hseq
    have hσ'_tmp : σ' tmp = u := by
      simp [σ', Stacks.set_other _ _ htd, Stacks.set_other _ _ hts]
    have ih := exec_dupRev_aux hts htd hsd u σ' hσ'_tmp
    have hst : ((σ'.set tmp []).set src (u.reverse ++ σ' src)).set dst (u.reverse ++ σ' dst) =
        (((σ.set tmp []).set src ((b :: u).reverse ++ σ src)).set dst ((b :: u).reverse ++ σ dst)) := by
      funext k
      simp only [σ', Stacks.set]
      by_cases hkd : k = dst
      · simp [hkd, List.reverse_cons, List.append_assoc]
      · by_cases hks : k = src
        · subst hks
          simp [hkd, List.reverse_cons, List.append_assoc]
        · by_cases hkt : k = tmp
          · subst hkt; simp [hkd, hks]
          · simp [hkd, hks, hkt]
    rw [hst] at ih
    have hstep := Exec.whileStep hne_nil hbody ih
    have hcost : 4 + (5 * u.length + 1) + 1 = 5 * (b :: u).length + 1 := by
      simp [List.length_cons]; omega
    rw [hcost] at hstep
    exact hstep

theorem exec_dupRev {tmp src dst : Nat}
    (hts : tmp ≠ src) (htd : tmp ≠ dst) (hsd : src ≠ dst) (σ : Stacks) :
    Exec (dupRev tmp src dst) σ (5 * (σ tmp).length + 1)
      (((σ.set tmp []).set src ((σ tmp).reverse ++ σ src)).set dst ((σ tmp).reverse ++ σ dst)) :=
  exec_dupRev_aux hts htd hsd (σ tmp) σ rfl

/-- Copy stack `src` into an initially empty stack `dst`, using an initially empty temporary
    stack `tmp`, restoring `src` and `tmp`. -/
def copyToEmpty (src dst tmp : Nat) : Stmt :=
  .seq (moveRev src tmp) (dupRev tmp src dst)

theorem exec_copyToEmpty {src dst tmp : Nat}
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (σ : Stacks) (hdst : σ dst = []) (htmp : σ tmp = []) :
    Exec (copyToEmpty src dst tmp) σ (9 * (σ src).length + 2) (σ.set dst (σ src)) := by
  have h1 := exec_moveRev hst σ
  rw [htmp, List.append_nil] at h1
  let σ₁ := (σ.set src []).set tmp (σ src).reverse
  have h2 := exec_dupRev hst.symm hdt.symm hsd σ₁
  have hσ₁_tmp : σ₁ tmp = (σ src).reverse := Stacks.set_same _ _ _
  have hσ₁_src : σ₁ src = [] := by simp [σ₁, Stacks.set_other _ _ hst]
  have hσ₁_dst : σ₁ dst = [] := by simp [σ₁, Stacks.set_other _ _ hdt, Stacks.set_other _ _ hsd.symm, hdst]
  rw [hσ₁_tmp, hσ₁_src, hσ₁_dst, List.length_reverse, List.reverse_reverse,
      List.append_nil] at h2
  have hst_final : (((σ₁.set tmp []).set src (σ src)).set dst (σ src)) = σ.set dst (σ src) := by
    funext k
    simp only [σ₁, Stacks.set]
    by_cases hkd : k = dst
    · simp [hkd]
    · by_cases hks : k = src
      · subst hks; simp [hkd]
      · by_cases hkt : k = tmp
        · subst hkt; simp [hkd, hks, htmp.symm]
        · simp [hkd, hks, hkt]
  rw [hst_final] at h2
  have hseq := Exec.seq h1 h2
  have hcost : (4 * (σ src).length + 1) + (5 * (σ src).length + 1) = 9 * (σ src).length + 2 := by omega
  rw [hcost] at hseq
  exact hseq

/-- Move stack `src` into an initially empty stack `dst` (leaving `src = []`), using an
    initially empty temporary stack `tmp`. -/
def moveStack (src dst tmp : Nat) : Stmt :=
  .seq (moveRev src tmp) (moveRev tmp dst)

theorem exec_moveStack {src dst tmp : Nat}
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (σ : Stacks) (hdst : σ dst = []) (htmp : σ tmp = []) :
    Exec (moveStack src dst tmp) σ (8 * (σ src).length + 2) ((σ.set src []).set dst (σ src)) := by
  have h1 := exec_moveRev hst σ
  rw [htmp, List.append_nil] at h1
  let σ₁ := (σ.set src []).set tmp (σ src).reverse
  have h2 := exec_moveRev hdt.symm σ₁
  have hσ₁_tmp : σ₁ tmp = (σ src).reverse := Stacks.set_same _ _ _
  have hσ₁_dst : σ₁ dst = [] := by simp [σ₁, Stacks.set_other _ _ hdt, Stacks.set_other _ _ hsd.symm, hdst]
  rw [hσ₁_tmp, hσ₁_dst, List.length_reverse, List.reverse_reverse, List.append_nil] at h2
  have hst_final : ((σ₁.set tmp []).set dst (σ src)) = (σ.set src []).set dst (σ src) := by
    funext k
    simp only [σ₁, Stacks.set]
    by_cases hkd : k = dst
    · simp [hkd]
    · by_cases hkt : k = tmp
      · subst hkt; simp [hkd, hst.symm, htmp.symm]
      · simp [hkd, hkt]
  rw [hst_final] at h2
  have hseq := Exec.seq h1 h2
  have hcost : (4 * (σ src).length + 1) + (4 * (σ src).length + 1) = 8 * (σ src).length + 2 := by omega
  rw [hcost] at hseq
  exact hseq

/-! ## 3. Range Copy & Range Clear Macros -/

/-- Copy `count` contiguous stacks `src .. src + count - 1` into initially empty stacks
    `dst .. dst + count - 1` using empty temporary stack `tmp`. -/
def copyRange (src dst : Nat) : Nat → Nat → Stmt
  | 0, _ => .skip
  | count + 1, tmp =>
      .seq (copyRange (src + 1) (dst + 1) count tmp)
           (copyToEmpty src dst tmp)

theorem exec_copyRange (src dst : Nat) (ws : List Word) (tmp : Nat) (σ : Stacks) {K : Nat}
    (hdisj : src + ws.length ≤ dst)
    (htmp_ge : dst + ws.length ≤ tmp)
    (hsrc : ∀ i : Nat, i < ws.length → σ (src + i) = ws.getD i [])
    (hdst : ∀ r : Nat, dst ≤ r → r < dst + ws.length → σ r = [])
    (htmp : σ tmp = [])
    (hlen : ∀ w ∈ ws, w.length ≤ K) :
    ∃ c : Nat,
      c ≤ ws.length * (9 * K + 2) ∧
      Exec (copyRange src dst ws.length tmp) σ c (setFrame σ dst ws) := by
  induction ws generalizing src dst σ with
  | nil =>
    exact ⟨0, Nat.zero_le _, Exec.skip σ⟩
  | cons w ws ih =>
    simp only [List.length_cons, copyRange, setFrame_cons] at hdisj htmp_ge hsrc hdst ⊢
    have hsrc' : ∀ i : Nat, i < ws.length → σ ((src + 1) + i) = ws.getD i [] := by
      intro i hi
      have h1 := hsrc (i + 1) (by omega)
      have heq : src + (i + 1) = (src + 1) + i := by omega
      rw [← heq, h1]
      rfl
    have hdst' : ∀ r : Nat, dst + 1 ≤ r → r < (dst + 1) + ws.length → σ r = [] :=
      fun r hr1 hr2 => hdst r (by omega) (by omega)
    have hlen' : ∀ u ∈ ws, u.length ≤ K :=
      fun u hu => hlen u (.tail w hu)
    rcases ih (src + 1) (dst + 1) σ (by omega) (by omega) hsrc' hdst' htmp hlen' with
      ⟨c₁, hc₁, hexec₁⟩
    let σ₁ := setFrame σ (dst + 1) ws
    have hσ₁_src : σ₁ src = w := by
      dsimp only [σ₁]
      rw [setFrame_outside σ (dst + 1) ws src (by omega)]
      have h0 := hsrc 0 (by omega)
      simpa using h0
    have hσ₁_dst : σ₁ dst = [] := by
      dsimp only [σ₁]
      rw [setFrame_outside σ (dst + 1) ws dst (by omega)]
      exact hdst dst (Nat.le_refl dst) (by omega)
    have hσ₁_tmp : σ₁ tmp = [] := by
      dsimp only [σ₁]
      rw [setFrame_outside σ (dst + 1) ws tmp (by omega)]
      exact htmp
    have hcopy := exec_copyToEmpty (src := src) (dst := dst) (tmp := tmp)
      (by omega) (by omega) (by omega) σ₁ hσ₁_dst hσ₁_tmp
    rw [hσ₁_src] at hcopy
    have hw_le : w.length ≤ K := hlen w (.head ws)
    have hmul : (ws.length + 1) * (9 * K + 2) = ws.length * (9 * K + 2) + (9 * K + 2) :=
      Nat.succ_mul ws.length (9 * K + 2)
    exact ⟨c₁ + (9 * w.length + 2), by omega, Exec.seq hexec₁ hcopy⟩

/-- Clear `count` contiguous stacks `dst .. dst + count - 1`. -/
def clearRange (dst : Nat) : Nat → Stmt
  | 0 => .skip
  | count + 1 => .seq (clearStack dst) (clearRange (dst + 1) count)

theorem exec_clearRange (dst : Nat) (ws : List Word) (σ : Stacks) {K : Nat}
    (hempty : ∀ r : Nat, dst ≤ r → σ r = [])
    (hlen : ∀ w ∈ ws, w.length ≤ K) :
    ∃ c : Nat,
      c ≤ ws.length * (2 * K + 1) ∧
      Exec (clearRange dst ws.length) (setFrame σ dst ws) c σ := by
  induction ws generalizing dst with
  | nil =>
    exact ⟨0, Nat.zero_le _, Exec.skip σ⟩
  | cons w ws ih =>
    simp only [List.length_cons, clearRange, setFrame_cons]
    have h1 := exec_clearStack dst ((setFrame σ (dst + 1) ws).set dst w)
    rw [Stacks.set_same, Stacks.set_set_same] at h1
    have hset_nil : (setFrame σ (dst + 1) ws).set dst [] = setFrame σ (dst + 1) ws := by
      apply Stacks.set_eq_self
      rw [setFrame_outside σ (dst + 1) ws dst (by omega)]
      exact hempty dst (Nat.le_refl dst)
    rw [hset_nil] at h1
    rcases ih (dst + 1) (fun r hr => hempty r (by omega)) (fun u hu => hlen u (.tail w hu)) with
      ⟨c₂, hc₂, hexec₂⟩
    have hw_le : w.length ≤ K := hlen w (.head ws)
    have hmul : (ws.length + 1) * (2 * K + 1) = ws.length * (2 * K + 1) + (2 * K + 1) :=
      Nat.succ_mul ws.length (2 * K + 1)
    exact ⟨(2 * w.length + 1) + c₂, by omega, Exec.seq h1 hexec₂⟩

/-! ## 4. List & Subprogram Evaluation Combinators -/

theorem getD_append_left (xs ys : List Word) (i : Nat) (hi : i < xs.length) :
    (xs ++ ys).getD i [] = xs.getD i [] := by
  induction xs generalizing i with
  | nil => contradiction
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      simp only [List.length_cons] at hi
      exact ih i' (by omega)

theorem getD_append_right (xs ys : List Word) (j : Nat) :
    (xs ++ ys).getD (xs.length + j) [] = ys.getD j [] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.cons_append]
    have hadd : (xs.length + 1) + j = (xs.length + j) + 1 := by omega
    rw [hadd]
    exact ih

theorem getD_length_le (ws : List Word) (i : Nat) {K : Nat} (h : ∀ w ∈ ws, w.length ≤ K) :
    (ws.getD i []).length ≤ K :=
  Nat.le_trans (Fn.length_getD_le_maxLen ws i) (Fn.maxLen_le_of_forall h)

/-- Copy `count` arguments starting at `src` into a fresh frame at `workBase + 1`,
    execute `sub` (which writes its result to `workBase`), clear the argument frame
    `workBase + 1 .. workBase + count`, and move the result from `workBase` to `dst`. -/
def evalSubTo (src count dst workBase : Nat) (sub : Stmt) : Stmt :=
  .seq (copyRange src (workBase + 1) count (workBase + 1 + count))
    (.seq sub
      (.seq (clearRange (workBase + 1) count)
            (moveStack workBase dst (workBase + 1))))

theorem exec_evalSubTo (src : Nat) (args : List Word) (dst workBase : Nat)
    (sub : Stmt) (σ : Stacks) (val : Word) {K K_out c_sub : Nat}
    (hsrc_wb : src + args.length ≤ workBase + 1)
    (hdst_wb : dst < workBase)
    (hsrc : ∀ i : Nat, i < args.length → σ (src + i) = args.getD i [])
    (hdst : σ dst = [])
    (hwb : ∀ r : Nat, workBase ≤ r → σ r = [])
    (hlen : ∀ w ∈ args, w.length ≤ K)
    (hval : val.length ≤ K_out)
    (hsub : Exec sub (setFrame σ (workBase + 1) args) c_sub
              ((setFrame σ (workBase + 1) args).set workBase val)) :
    ∃ c : Nat,
      c ≤ c_sub + args.length * (11 * K + 3) + (8 * K_out + 2) ∧
      Exec (evalSubTo src args.length dst workBase sub) σ c (σ.set dst val) := by
  rcases exec_copyRange src (workBase + 1) args (workBase + 1 + args.length) σ
      hsrc_wb (Nat.le_refl _) hsrc
      (fun r hr _ => hwb r (by omega))
      (hwb _ (by omega))
      hlen with
    ⟨c₁, hc₁, hexec₁⟩
  have hframe_eq : (setFrame σ (workBase + 1) args).set workBase val =
      setFrame (σ.set workBase val) (workBase + 1) args :=
    (setFrame_set_below σ (workBase + 1) args val (by omega)).symm
  rw [hframe_eq] at hsub
  rcases exec_clearRange (workBase + 1) args (σ.set workBase val)
      (fun r hr => by rw [Stacks.set_other _ _ (by omega)]; exact hwb r (by omega)) hlen with
    ⟨c₂, hc₂, hexec₂⟩
  have hmove := exec_moveStack (src := workBase) (dst := dst) (tmp := workBase + 1)
    (by omega) (by omega) (by omega) (σ.set workBase val)
    (by rw [Stacks.set_other _ _ (by omega)]; exact hdst)
    (by rw [Stacks.set_other _ _ (by omega)]; exact hwb (workBase + 1) (by omega))
  rw [Stacks.set_same, Stacks.set_set_same, Stacks.set_eq_self (hwb workBase (Nat.le_refl _))] at hmove
  have hmul : args.length * (11 * K + 3) = args.length * (9 * K + 2) + args.length * (2 * K + 1) := by
    rw [← Nat.mul_add]
    have h1 : 9 * K + 2 + (2 * K + 1) = 11 * K + 3 := by omega
    rw [h1]
  exact ⟨c₁ + (c_sub + (c₂ + (8 * val.length + 2))),
    by omega,
    Exec.seq hexec₁ (Exec.seq hsub (Exec.seq hexec₂ hmove))⟩

/-- Evaluate a tuple of `k` subprograms `subs : Fin k → Stmt` using argument frame `src .. src + count - 1`
    and scratch frame `workBase`, storing their outputs into `dst .. dst + k - 1`. -/
def evalTuple (src count dst workBase : Nat) : {k : Nat} → (Fin k → Stmt) → Stmt
  | 0, _ => .skip
  | _ + 1, subs =>
      .seq (evalTuple src count (dst + 1) workBase (fun i => subs i.succ))
           (evalSubTo src count dst workBase (subs ⟨0, Nat.zero_lt_succ _⟩))

theorem exec_evalTuple (src : Nat) (args : List Word) (dst workBase : Nat) :
    ∀ {k : Nat} (subs : Fin k → Stmt) (vals : Fin k → Word) (ps : Fin k → Poly)
      (σ : Stacks) {K K_out : Nat},
      src + args.length ≤ dst →
      dst + k ≤ workBase →
      (∀ i : Nat, i < args.length → σ (src + i) = args.getD i []) →
      (∀ r : Nat, dst ≤ r → r < dst + k → σ r = []) →
      (∀ r : Nat, workBase ≤ r → σ r = []) →
      (∀ w ∈ args, w.length ≤ K) →
      (∀ i : Fin k, (vals i).length ≤ K_out) →
      (∀ (i : Fin k) (σ' : Stacks), (∀ r : Nat, workBase ≤ r → σ' r = []) →
        ∃ c : Nat, c ≤ (ps i).eval K ∧
          Exec (subs i) (setFrame σ' (workBase + 1) args) c
            ((setFrame σ' (workBase + 1) args).set workBase (vals i))) →
      ∃ c : Nat,
        c ≤ (Poly.sumFin ps).eval K + k * (args.length * (11 * K + 3) + (8 * K_out + 2)) ∧
        Exec (evalTuple src args.length dst workBase subs) σ c
          (setFrame σ dst (List.ofFn vals))
  | 0, subs, vals, ps, σ, K, K_out, _, _, _, _, _, _, _, _ => by
    simp only [evalTuple, Poly.sumFin, Poly.eval_const, Nat.zero_mul, Nat.add_zero,
      List.ofFn_zero, setFrame_nil]
    exact ⟨0, Nat.le_refl 0, Exec.skip σ⟩
  | k + 1, subs, vals, ps, σ, K, K_out, hsrc_dst, hdst_wb, hsrc, hdst, hwb, hlen, hvals, hsubs => by
    simp only [evalTuple, Poly.sumFin, Poly.eval_add, List.ofFn_succ, setFrame_cons]
    rcases exec_evalTuple src args (dst + 1) workBase
        (fun i => subs i.succ) (fun i => vals i.succ) (fun i => ps i.succ) σ
        (by omega) (by omega) hsrc
        (fun r hr1 hr2 => hdst r (by omega) (by omega))
        hwb hlen
        (fun i => hvals i.succ)
        (fun i σ' hσ' => hsubs i.succ σ' hσ') with
      ⟨c₁, hc₁, hexec₁⟩
    let σ₁ := setFrame σ (dst + 1) (List.ofFn (fun i : Fin k => vals i.succ))
    have hσ₁_wb : ∀ r : Nat, workBase ≤ r → σ₁ r = [] := by
      intro r hr
      dsimp only [σ₁]
      rw [setFrame_outside σ (dst + 1) _ r (by simp [List.length_ofFn]; omega)]
      exact hwb r hr
    have hσ₁_src : ∀ i : Nat, i < args.length → σ₁ (src + i) = args.getD i [] := by
      intro i hi
      dsimp only [σ₁]
      rw [setFrame_outside σ (dst + 1) _ (src + i) (by omega)]
      exact hsrc i hi
    have hσ₁_dst : σ₁ dst = [] := by
      dsimp only [σ₁]
      rw [setFrame_outside σ (dst + 1) _ dst (by omega)]
      exact hdst dst (Nat.le_refl dst) (by omega)
    rcases hsubs ⟨0, Nat.zero_lt_succ k⟩ σ₁ hσ₁_wb with ⟨c_sub, hc_sub, hexec_sub⟩
    rcases exec_evalSubTo src args dst workBase (subs ⟨0, Nat.zero_lt_succ k⟩) σ₁ (vals ⟨0, Nat.zero_lt_succ k⟩)
        (by omega) (by omega) hσ₁_src hσ₁_dst hσ₁_wb hlen (hvals ⟨0, Nat.zero_lt_succ k⟩) hexec_sub with
      ⟨c₂, hc₂, hexec₂⟩
    have hmul : (k + 1) * (args.length * (11 * K + 3) + (8 * K_out + 2)) =
        k * (args.length * (11 * K + 3) + (8 * K_out + 2)) +
          (args.length * (11 * K + 3) + (8 * K_out + 2)) :=
      Nat.succ_mul k _
    exact ⟨c₁ + c₂, by omega, Exec.seq hexec₁ hexec₂⟩

/-! ## 5. Safe Recursion (`srec`) Loop Combinators -/

/-- One iteration step of safe recursion on notation for bit `b`:
    - Copies `ys` (from `base + 2 + n`), `acc` (from `base`), and `u :: xs_tail` (from `base + 1`)
      into `workBase + 1 .. workBase + (n + 1) + (m + 1)`.
    - Runs `sub` (which evaluates `h_b` into `workBase`).
    - Clears the argument frame at `workBase + 1`, replaces `base` with `workBase`,
      pops `revW`, and pushes `b` onto `base + 1`. -/
def evalRecStep (base n m : Nat) (b : Bool) (sub : Stmt) : Stmt :=
  let revW := base + 2 + n + m
  let workBase := base + 3 + n + m
  let tmp := workBase + 1 + (n + 1) + (m + 1)
  .seq (copyRange (base + 2 + n) (workBase + 1 + (n + 1) + 1) m tmp)
    (.seq (copyToEmpty base (workBase + 1 + (n + 1)) tmp)
      (.seq (copyRange (base + 1) (workBase + 1) (n + 1) tmp)
        (.seq sub
          (.seq (clearRange (workBase + 1) ((n + 1) + (m + 1)))
            (.seq (clearStack base)
              (.seq (moveStack workBase base (workBase + 1))
                (.seq (.pop revW) (.push (base + 1) b))))))))

/-- The `whileNE` loop for safe recursion on notation. -/
def recLoop (base n m : Nat) (sub0 sub1 : Stmt) : Stmt :=
  let revW := base + 2 + n + m
  .whileNE revW
    (.ifTop revW .skip
      (evalRecStep base n m false sub0)
      (evalRecStep base n m true sub1))

theorem exec_evalRecStep (base n m : Nat) (b : Bool) (sub : Stmt)
    (σ_loop : Stacks) (u v' : Word) (xs_tail ys : List Word) (acc newAcc : Word)
    {K_rec c_sub : Nat}
    (hxs_len : xs_tail.length = n) (hys_len : ys.length = m)
    (hacc : σ_loop base = acc)
    (hu : σ_loop (base + 1) = u)
    (hxs : ∀ i : Nat, i < n → σ_loop (base + 2 + i) = xs_tail.getD i [])
    (hys : ∀ j : Nat, j < m → σ_loop (base + 2 + n + j) = ys.getD j [])
    (hrev : σ_loop (base + 2 + n + m) = b :: v')
    (hwb : ∀ r : Nat, base + 3 + n + m ≤ r → σ_loop r = [])
    (hu_le : u.length ≤ K_rec)
    (hxs_le : ∀ x ∈ xs_tail, x.length ≤ K_rec)
    (hys_le : ∀ y ∈ ys, y.length ≤ K_rec)
    (hacc_le : acc.length ≤ K_rec)
    (hnew_le : newAcc.length ≤ K_rec)
    (hsub : Exec sub
      (setFrame σ_loop ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys)))
      c_sub
      ((setFrame σ_loop ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))).set
        (base + 3 + n + m) newAcc)) :
    ∃ c : Nat,
      c ≤ c_sub + ((n + 1) + (m + 1)) * (11 * K_rec + 3) + (10 * K_rec + 5) ∧
      Exec (evalRecStep base n m b sub) σ_loop c
        (((σ_loop.set base newAcc).set (base + 2 + n + m) v').set (base + 1) (b :: u)) := by
  let revW := base + 2 + n + m
  let workBase := base + 3 + n + m
  let tmp := workBase + 1 + (n + 1) + (m + 1)
  have hys_copy : ∃ c₁, c₁ ≤ m * (9 * K_rec + 2) ∧
      Exec (copyRange (base + 2 + n) (workBase + 1 + (n + 1) + 1) m tmp) σ_loop c₁
        (setFrame σ_loop (workBase + 1 + (n + 1) + 1) ys) := by
    rw [← hys_len]
    exact exec_copyRange (base + 2 + n) (workBase + 1 + (n + 1) + 1) ys tmp σ_loop
      (by omega) (by omega)
      (fun j hj => hys j (by omega))
      (fun r hr _ => hwb r (by omega))
      (hwb _ (by omega))
      hys_le
  rcases hys_copy with ⟨c₁, hc₁, hexec₁⟩
  let σ₁ := setFrame σ_loop (workBase + 1 + (n + 1) + 1) ys
  have hacc_copy : Exec (copyToEmpty base (workBase + 1 + (n + 1)) tmp) σ₁ (9 * acc.length + 2)
      (setFrame σ_loop (workBase + 1 + (n + 1)) (acc :: ys)) := by
    have hcp := exec_copyToEmpty (src := base) (dst := workBase + 1 + (n + 1)) (tmp := tmp)
      (by omega) (by omega) (by omega) σ₁
      (by dsimp only [σ₁]; rw [setFrame_outside _ _ _ _ (by omega)]; exact hwb _ (by omega))
      (by dsimp only [σ₁]; rw [setFrame_outside _ _ _ _ (by omega)]; exact hwb _ (by omega))
    have hσ₁_base : σ₁ base = acc := by
      dsimp only [σ₁]
      rw [setFrame_outside _ _ _ _ (by omega)]
      exact hacc
    rw [hσ₁_base] at hcp
    exact hcp
  let σ₂ := setFrame σ_loop (workBase + 1 + (n + 1)) (acc :: ys)
  have huxs_len : (u :: xs_tail).length = n + 1 := by simp [hxs_len]
  have huxs_le : ∀ x ∈ (u :: xs_tail), x.length ≤ K_rec := by
    intro x hx
    cases hx with
    | head => exact hu_le
    | tail _ hm => exact hxs_le x hm
  have huxs_src : ∀ i : Nat, i < (u :: xs_tail).length → σ₂ (base + 1 + i) = (u :: xs_tail).getD i [] := by
    intro i hi
    dsimp only [σ₂]
    rw [setFrame_outside _ _ _ _ (by omega)]
    cases i with
    | zero => simpa using hu
    | succ i' =>
      have heq : base + 1 + (i' + 1) = base + 2 + i' := by omega
      rw [heq]
      exact hxs i' (by omega)
  have huxs_copy : ∃ c₃, c₃ ≤ (n + 1) * (9 * K_rec + 2) ∧
      Exec (copyRange (base + 1) (workBase + 1) (n + 1) tmp) σ₂ c₃
        (setFrame σ_loop (workBase + 1) ((u :: xs_tail) ++ (acc :: ys))) := by
    rcases exec_copyRange (base + 1) (workBase + 1) (u :: xs_tail) tmp σ₂
        (by simp [hxs_len]; omega) (by simp [hxs_len]; omega) huxs_src
        (fun r hr1 hr2 => by
          dsimp only [σ₂]
          rw [setFrame_outside _ _ _ _ (by simp [hxs_len] at hr2; omega)]
          exact hwb r (by omega))
        (by
          dsimp only [σ₂, tmp]
          rw [setFrame_outside _ _ _ _ (by simp [hys_len])]
          exact hwb _ (by omega))
        huxs_le with
      ⟨c₃, hc₃, hexec₃⟩
    have happ : setFrame σ₂ (workBase + 1) (u :: xs_tail) =
        setFrame σ_loop (workBase + 1) ((u :: xs_tail) ++ (acc :: ys)) := by
      dsimp only [σ₂]
      rw [← huxs_len]
      exact setFrame_append σ_loop (workBase + 1) (u :: xs_tail) (acc :: ys)
    rw [happ] at hexec₃
    rw [huxs_len] at hc₃ hexec₃
    exact ⟨c₃, hc₃, hexec₃⟩
  rcases huxs_copy with ⟨c₃, hc₃, hexec₃⟩
  have hframe_eq : (setFrame σ_loop (workBase + 1) ((u :: xs_tail) ++ (acc :: ys))).set workBase newAcc =
      setFrame (σ_loop.set workBase newAcc) (workBase + 1) ((u :: xs_tail) ++ (acc :: ys)) :=
    (setFrame_set_below σ_loop (workBase + 1) ((u :: xs_tail) ++ (acc :: ys)) newAcc (by omega)).symm
  rw [hframe_eq] at hsub
  have hall_len : ((u :: xs_tail) ++ (acc :: ys)).length = (n + 1) + (m + 1) := by
    simp [hxs_len, hys_len]; omega
  have hall_le : ∀ w ∈ ((u :: xs_tail) ++ (acc :: ys)), w.length ≤ K_rec := by
    intro w hw
    rcases List.mem_append.mp hw with h1 | h2
    · exact huxs_le w h1
    · cases h2 with
      | head => exact hacc_le
      | tail _ hm => exact hys_le w hm
  have hclear_args : ∃ c₅, c₅ ≤ ((n + 1) + (m + 1)) * (2 * K_rec + 1) ∧
      Exec (clearRange (workBase + 1) ((n + 1) + (m + 1)))
        (setFrame (σ_loop.set workBase newAcc) (workBase + 1) ((u :: xs_tail) ++ (acc :: ys)))
        c₅ (σ_loop.set workBase newAcc) := by
    rw [← hall_len]
    exact exec_clearRange (workBase + 1) ((u :: xs_tail) ++ (acc :: ys)) (σ_loop.set workBase newAcc)
      (fun r hr => by rw [Stacks.set_other _ _ (by omega)]; exact hwb r (by omega))
      hall_le
  rcases hclear_args with ⟨c₅, hc₅, hexec₅⟩
  have hclear_base : Exec (clearStack base) (σ_loop.set workBase newAcc) (2 * acc.length + 1)
      ((σ_loop.set workBase newAcc).set base []) := by
    have hcl := exec_clearStack base (σ_loop.set workBase newAcc)
    rw [Stacks.set_other _ _ (by omega), hacc] at hcl
    exact hcl
  have hmove_base : Exec (moveStack workBase base (workBase + 1))
      ((σ_loop.set workBase newAcc).set base []) (8 * newAcc.length + 2)
      (σ_loop.set base newAcc) := by
    have hmv := exec_moveStack (src := workBase) (dst := base) (tmp := workBase + 1)
      (by omega) (by omega) (by omega) ((σ_loop.set workBase newAcc).set base [])
      (Stacks.set_same _ _ _)
      (by
        rw [Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega)]
        exact hwb (workBase + 1) (by omega))
    have hwb_val : ((σ_loop.set workBase newAcc).set base []) workBase = newAcc := by
      rw [Stacks.set_other _ _ (by omega), Stacks.set_same]
    rw [hwb_val] at hmv
    have hst : ((((σ_loop.set workBase newAcc).set base []).set workBase []).set base newAcc) =
        σ_loop.set base newAcc := by
      rw [Stacks.set_set_comm (σ_loop.set workBase newAcc) [] [] (by omega),
          Stacks.set_set_same,
          Stacks.set_set_same,
          Stacks.set_eq_self (hwb workBase (Nat.le_refl _))]
    rw [hst] at hmv
    exact hmv
  have hpop_rev : Exec (.pop revW) (σ_loop.set base newAcc) 1
      ((σ_loop.set base newAcc).set revW v') := by
    have hp := Exec.pop revW (σ_loop.set base newAcc)
    have hrev_val : (σ_loop.set base newAcc) revW = b :: v' := by
      rw [Stacks.set_other _ _ (by omega)]
      exact hrev
    rw [hrev_val] at hp
    exact hp
  have hpush_u : Exec (.push (base + 1) b) ((σ_loop.set base newAcc).set revW v') 1
      (((σ_loop.set base newAcc).set revW v').set (base + 1) (b :: u)) := by
    have hpu := Exec.push (base + 1) b ((σ_loop.set base newAcc).set revW v')
    have hu_val : ((σ_loop.set base newAcc).set revW v') (base + 1) = u := by
      rw [Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega)]
      exact hu
    rw [hu_val] at hpu
    exact hpu
  have hcost_arith :
      c₁ + ((9 * acc.length + 2) + (c₃ + (c_sub + (c₅ + ((2 * acc.length + 1) + ((8 * newAcc.length + 2) + (1 + 1))))))) ≤
      c_sub + ((n + 1) + (m + 1)) * (11 * K_rec + 3) + (10 * K_rec + 5) := by
    have h1 : ((n + 1) + (m + 1)) * (11 * K_rec + 3) =
        m * (9 * K_rec + 2) + (9 * K_rec + 2) + (n + 1) * (9 * K_rec + 2) +
          ((n + 1) + (m + 1)) * (2 * K_rec + 1) := by
      have ha : (n + 1) + (m + 1) = m + 1 + (n + 1) := by omega
      have hb : 11 * K_rec + 3 = (9 * K_rec + 2) + (2 * K_rec + 1) := by omega
      rw [hb, Nat.mul_add, ha, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    omega
  exact ⟨_, hcost_arith,
    Exec.seq hexec₁ (Exec.seq hacc_copy (Exec.seq hexec₃ (Exec.seq hsub
      (Exec.seq hexec₅ (Exec.seq hclear_base (Exec.seq hmove_base (Exec.seq hpop_rev hpush_u)))))))⟩

/-- Loop invariant state for `recLoop`:
    - `base` holds `recIter gVal stepFn u`
    - `base + 2 + n + m` (`revW`) holds `v`
    - `base + 1` holds `u` -/
def recLoopState (σ₀ : Stacks) (base n m : Nat) (gVal : Word)
    (stepFn : Bool → Word → Word → Word) (u v : Word) : Stacks :=
  (((σ₀.set base (recIter gVal stepFn u)).set (base + 2 + n + m) v).set (base + 1) u)

theorem recLoopState_update (σ₀ : Stacks) (base n m : Nat) (gVal : Word)
    (stepFn : Bool → Word → Word → Word) (u v v' : Word) (b : Bool) :
    ((((recLoopState σ₀ base n m gVal stepFn u v).set base (recIter gVal stepFn (b :: u))).set
        (base + 2 + n + m) v').set (base + 1) (b :: u)) =
      recLoopState σ₀ base n m gVal stepFn (b :: u) v' := by
  simp only [recLoopState]
  rw [Stacks.set_set_comm _ u (recIter gVal stepFn (b :: u)) (by omega),
      Stacks.set_set_comm _ u v' (by omega),
      Stacks.set_set_same,
      Stacks.set_set_comm (σ₀.set base (recIter gVal stepFn u)) v (recIter gVal stepFn (b :: u)) (by omega),
      Stacks.set_set_same,
      Stacks.set_set_same]

theorem exec_recLoop (base n m : Nat) (sub0 sub1 : Stmt)
    (σ₀ : Stacks) (xs_tail ys : List Word) (gVal : Word)
    (stepFn : Bool → Word → Word → Word) {K K_rec C_step : Nat}
    (hK_le : K ≤ K_rec)
    (hxs_len : xs_tail.length = n) (hys_len : ys.length = m)
    (hxs : ∀ i : Nat, i < n → σ₀ (base + 2 + i) = xs_tail.getD i [])
    (hys : ∀ j : Nat, j < m → σ₀ (base + 2 + n + j) = ys.getD j [])
    (hwb : ∀ r : Nat, base + 3 + n + m ≤ r → σ₀ r = [])
    (hxs_le : ∀ x ∈ xs_tail, x.length ≤ K_rec)
    (hys_le : ∀ y ∈ ys, y.length ≤ K_rec)
    (hrec_le : ∀ u : Word, u.length ≤ K → (recIter gVal stepFn u).length ≤ K_rec)
    (hstep0 : ∀ (u acc : Word) (σ' : Stacks),
      u.length ≤ K_rec → acc.length ≤ K_rec →
      (∀ r : Nat, base + 3 + n + m ≤ r → σ' r = []) →
      ∃ c : Nat, c ≤ C_step ∧
        Exec sub0 (setFrame σ' ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))) c
          ((setFrame σ' ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))).set
            (base + 3 + n + m) (stepFn false u acc)))
    (hstep1 : ∀ (u acc : Word) (σ' : Stacks),
      u.length ≤ K_rec → acc.length ≤ K_rec →
      (∀ r : Nat, base + 3 + n + m ≤ r → σ' r = []) →
      ∃ c : Nat, c ≤ C_step ∧
        Exec sub1 (setFrame σ' ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))) c
          ((setFrame σ' ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))).set
            (base + 3 + n + m) (stepFn true u acc))) :
    ∀ (v u : Word), v.length + u.length ≤ K →
      ∃ c : Nat,
        c ≤ v.length * (C_step + ((n + 1) + (m + 1)) * (11 * K_rec + 3) + (10 * K_rec + 7)) + 1 ∧
        Exec (recLoop base n m sub0 sub1)
          (recLoopState σ₀ base n m gVal stepFn u v)
          c
          (recLoopState σ₀ base n m gVal stepFn (v.reverse ++ u) [])
  | [], u, _ => by
    have hrev : recLoopState σ₀ base n m gVal stepFn u [] (base + 2 + n + m) = [] := by
      simp only [recLoopState]
      rw [Stacks.set_other _ _ (by omega), Stacks.set_same]
    have hdone := Exec.whileDone (i := base + 2 + n + m)
      (body := .ifTop (base + 2 + n + m) .skip (evalRecStep base n m false sub0) (evalRecStep base n m true sub1))
      hrev
    simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.zero_mul, Nat.zero_add]
    exact ⟨1, Nat.le_refl 1, hdone⟩
  | b :: v', u, hvu => by
    simp only [List.length_cons] at hvu
    let σ_loop := recLoopState σ₀ base n m gVal stepFn u (b :: v')
    have hrev : σ_loop (base + 2 + n + m) = b :: v' := by
      dsimp only [σ_loop, recLoopState]
      rw [Stacks.set_other _ _ (by omega), Stacks.set_same]
    have hne : σ_loop (base + 2 + n + m) ≠ [] := by
      rw [hrev]; exact List.cons_ne_nil b v'
    have hloop_base : σ_loop base = recIter gVal stepFn u := by
      dsimp only [σ_loop, recLoopState]
      rw [Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega), Stacks.set_same]
    have hloop_u : σ_loop (base + 1) = u := by
      dsimp only [σ_loop, recLoopState]
      exact Stacks.set_same _ _ _
    have hloop_xs : ∀ i : Nat, i < n → σ_loop (base + 2 + i) = xs_tail.getD i [] := by
      intro i hi
      dsimp only [σ_loop, recLoopState]
      rw [Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega)]
      exact hxs i hi
    have hloop_ys : ∀ j : Nat, j < m → σ_loop (base + 2 + n + j) = ys.getD j [] := by
      intro j hj
      dsimp only [σ_loop, recLoopState]
      rw [Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega)]
      exact hys j hj
    have hloop_wb : ∀ r : Nat, base + 3 + n + m ≤ r → σ_loop r = [] := by
      intro r hr
      dsimp only [σ_loop, recLoopState]
      rw [Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega)]
      exact hwb r hr
    have hu_le_K : u.length ≤ K := by omega
    have hbu_le_K : (b :: u).length ≤ K := by simp [List.length_cons]; omega
    have hu_le : u.length ≤ K_rec := by omega
    have hacc_le : (recIter gVal stepFn u).length ≤ K_rec := hrec_le u hu_le_K
    have hnew_le : (recIter gVal stepFn (b :: u)).length ≤ K_rec := hrec_le (b :: u) hbu_le_K
    have hbody : ∃ c_b : Nat,
        c_b ≤ C_step + ((n + 1) + (m + 1)) * (11 * K_rec + 3) + (10 * K_rec + 6) ∧
        Exec (.ifTop (base + 2 + n + m) .skip (evalRecStep base n m false sub0) (evalRecStep base n m true sub1))
          σ_loop c_b (recLoopState σ₀ base n m gVal stepFn (b :: u) v') := by
      cases b with
      | false =>
        rcases hstep0 u (recIter gVal stepFn u) σ_loop hu_le hacc_le hloop_wb with
          ⟨c_sub, hc_sub, hexec_sub⟩
        rcases exec_evalRecStep base n m false sub0 σ_loop u v' xs_tail ys
            (recIter gVal stepFn u) (recIter gVal stepFn (false :: u))
            hxs_len hys_len hloop_base hloop_u hloop_xs hloop_ys hrev hloop_wb
            hu_le hxs_le hys_le hacc_le hnew_le hexec_sub with
          ⟨c_step, hc_step, hexec_step⟩
        rw [recLoopState_update] at hexec_step
        exact ⟨c_step + 1, by omega, Exec.if0 hrev hexec_step⟩
      | true =>
        rcases hstep1 u (recIter gVal stepFn u) σ_loop hu_le hacc_le hloop_wb with
          ⟨c_sub, hc_sub, hexec_sub⟩
        rcases exec_evalRecStep base n m true sub1 σ_loop u v' xs_tail ys
            (recIter gVal stepFn u) (recIter gVal stepFn (true :: u))
            hxs_len hys_len hloop_base hloop_u hloop_xs hloop_ys hrev hloop_wb
            hu_le hxs_le hys_le hacc_le hnew_le hexec_sub with
          ⟨c_step, hc_step, hexec_step⟩
        rw [recLoopState_update] at hexec_step
        exact ⟨c_step + 1, by omega, Exec.if1 hrev hexec_step⟩
    rcases hbody with ⟨c_b, hc_b, hexec_b⟩
    rcases exec_recLoop base n m sub0 sub1 σ₀ xs_tail ys gVal stepFn
        hK_le hxs_len hys_len hxs hys hwb hxs_le hys_le hrec_le hstep0 hstep1
        v' (b :: u) (by simp [List.length_cons]; omega) with
      ⟨c_rest, hc_rest, hexec_rest⟩
    have hrev_app : v'.reverse ++ (b :: u) = (b :: v').reverse ++ u := by
      simp [List.reverse_cons, List.append_assoc]
    rw [hrev_app] at hexec_rest
    have hmul : (v'.length + 1) * (C_step + ((n + 1) + (m + 1)) * (11 * K_rec + 3) + (10 * K_rec + 7)) =
        v'.length * (C_step + ((n + 1) + (m + 1)) * (11 * K_rec + 3) + (10 * K_rec + 7)) +
          (C_step + ((n + 1) + (m + 1)) * (11 * K_rec + 3) + (10 * K_rec + 7)) :=
      Nat.succ_mul v'.length _
    simp only [List.length_cons]
    exact ⟨c_b + c_rest + 1, by omega, Exec.whileStep hne hexec_b hexec_rest⟩

/-! ## 6. Compiler from `BC.Fn` to `StackProg.Stmt` and Polynomial-Time Soundness -/

/-- Linear polynomial `a * X + b`. -/
def Poly.linear (a b : Nat) : Poly :=
  .add (.mul (.const a) .var) (.const b)

@[simp] theorem Poly.eval_linear (a b n : Nat) :
    (Poly.linear a b).eval n = a * n + b := rfl

/-- Compile a BC function `f : Fn n m` into a stack statement `Stmt` operating on the frame
    starting at `base`:
    - `base`: output stack (initially empty)
    - `base + 1 .. base + n`: normal arguments `xs`
    - `base + 1 + n .. base + n + m`: safe arguments `ys`
    - `≥ base + 1 + n + m`: scratch space (initially empty, restored to empty on exit). -/
def compileBC (base : Nat) : {n m : Nat} → Fn n m → Stmt
  | _, _, .zero => .skip
  | n, m, .projN i => copyToEmpty (base + 1 + i.val) base (base + 1 + n + m)
  | n, m, .projS j => copyToEmpty (base + 1 + n + j.val) base (base + 1 + n + m)
  | _, _, .s0 => .seq (copyToEmpty (base + 1) base (base + 2)) (.push base false)
  | _, _, .s1 => .seq (copyToEmpty (base + 1) base (base + 2)) (.push base true)
  | _, _, .pred => .seq (copyToEmpty (base + 1) base (base + 2)) (.pop base)
  | _, _, .cond =>
      .ifTop (base + 1)
        (copyToEmpty (base + 2) base (base + 5))
        (copyToEmpty (base + 3) base (base + 5))
        (copyToEmpty (base + 4) base (base + 5))
  | n, m, .comp (k := k) (l := l) h rs ts =>
      .seq (evalTuple (base + 1) (n + m) (base + 1 + n + m + 1 + k) (base + 1 + n + m + 1 + k + l)
              (fun j => compileBC (base + 1 + n + m + 1 + k + l) (ts j)))
        (.seq (evalTuple (base + 1) n (base + 1 + n + m + 1) (base + 1 + n + m + 1 + k + l)
                (fun i => compileBC (base + 1 + n + m + 1 + k + l) (rs i)))
          (.seq (compileBC (base + 1 + n + m) h)
            (.seq (clearRange (base + 1 + n + m + 1) (k + l))
                  (moveStack (base + 1 + n + m) base (base + 1 + n + m + 1)))))
  | n + 1, m, .srec g h0 h1 =>
      .seq (moveRev (base + 1) (base + 2 + n + m))
        (.seq (evalSubTo (base + 2) (n + m) base (base + 3 + n + m) (compileBC (base + 3 + n + m) g))
              (recLoop base n m (compileBC (base + 3 + n + m) h0) (compileBC (base + 3 + n + m) h1)))

/-- Syntactic polynomial time bound for `compileBC base f` when all normal and safe arguments
    have bit-length at most `K`. -/
def Fn.timePoly : {n m : Nat} → Fn n m → Poly
  | _, _, .zero => .const 1
  | _, _, .projN _ => .linear 9 2
  | _, _, .projS _ => .linear 9 2
  | _, _, .s0 => .linear 9 3
  | _, _, .s1 => .linear 9 3
  | _, _, .pred => .linear 9 3
  | _, _, .cond => .linear 9 3
  | n, m, .comp (k := k) (l := l) h rs ts =>
      .add
        (.add
          (.add
            (.add
              (.add (Poly.sumFin fun j => (ts j).timePoly)
                    (.mul (.const l)
                      (.add (.mul (.const (n + m)) (.linear 11 3))
                            ((Poly.linear 8 2).comp
                              (.add (Poly.sumFin fun i => (rs i).fullSizePoly)
                                    (Poly.sumFin fun j => (ts j).fullSizePoly))))))
              (.add (Poly.sumFin fun i => (rs i).timePoly)
                    (.mul (.const k)
                      (.add (.mul (.const n) (.linear 11 3))
                            ((Poly.linear 8 2).comp
                              (.add (Poly.sumFin fun i => (rs i).fullSizePoly)
                                    (Poly.sumFin fun j => (ts j).fullSizePoly)))))))
            (h.timePoly.comp
              (.add (Poly.sumFin fun i => (rs i).fullSizePoly)
                    (Poly.sumFin fun j => (ts j).fullSizePoly))))
          (.mul (.const (k + l))
            ((Poly.linear 2 1).comp
              (.add (Poly.sumFin fun i => (rs i).fullSizePoly)
                    (Poly.sumFin fun j => (ts j).fullSizePoly)))))
        ((Poly.linear 8 2).comp
          (h.fullSizePoly.comp
            (.add (Poly.sumFin fun i => (rs i).fullSizePoly)
                  (Poly.sumFin fun j => (ts j).fullSizePoly))))
  | n + 1, m, .srec g h0 h1 =>
      .add
        (.add (.linear 4 1)
          (.add (.add g.timePoly (.mul (.const (n + m)) (.linear 11 3)))
                ((Poly.linear 8 2).comp (Fn.srec g h0 h1).fullSizePoly)))
        (.add
          (.mul .var
            (.add
              (.add
                ((Poly.add h0.timePoly h1.timePoly).comp (Fn.srec g h0 h1).fullSizePoly)
                (.mul (.const ((n + 1) + (m + 1)))
                  ((Poly.linear 11 3).comp (Fn.srec g h0 h1).fullSizePoly)))
              ((Poly.linear 10 7).comp (Fn.srec g h0 h1).fullSizePoly)))
          (.const 1))

/-- **Big-step correctness and polynomial time bound for `compileBC`**:
    For every BC program `f : Fn n m`, frame base `base`, normal inputs `xs` (`xs.length = n`),
    and safe inputs `ys` (`ys.length = m`) with all input lengths `≤ K`,
    `compileBC base f` evaluates `f.eval xs ys` into stack `base` within `f.timePoly.eval K` steps,
    preserving all argument stacks and restoring all scratch stacks above the frame to `[]`. -/
theorem exec_compileBC {n m : Nat} (f : Fn n m) (base : Nat) (σ : Stacks)
    (xs ys : List Word) (K : Nat)
    (hxs : xs.length = n) (hys : ys.length = m)
    (hempty : ∀ r : Nat, base ≤ r → σ r = [])
    (hlenX : ∀ x ∈ xs, x.length ≤ K)
    (hlenY : ∀ y ∈ ys, y.length ≤ K) :
    ∃ c : Nat,
      c ≤ f.timePoly.eval K ∧
      Exec (compileBC base f)
        (setFrame σ (base + 1) (xs ++ ys))
        c
        ((setFrame σ (base + 1) (xs ++ ys)).set base (f.eval xs ys)) := by
  induction f generalizing base σ xs ys K with
  | zero =>
    simp only [compileBC, Fn.timePoly, Poly.eval_const, Fn.eval_zero]
    have hbase : setFrame σ (base + 1) (xs ++ ys) base = [] := by
      rw [setFrame_outside _ _ _ _ (by omega)]
      exact hempty base (Nat.le_refl base)
    rw [Stacks.set_eq_self hbase]
    exact ⟨0, by omega, Exec.skip _⟩
  | @projN n m i =>
    simp only [compileBC, Fn.timePoly, Poly.eval_linear, Fn.eval_projN]
    have hi : i.val < n := i.isLt
    have hbase : setFrame σ (base + 1) (xs ++ ys) base = [] := by
      rw [setFrame_outside _ _ _ _ (by omega)]
      exact hempty base (Nat.le_refl base)
    have htmp : setFrame σ (base + 1) (xs ++ ys) (base + 1 + n + m) = [] := by
      rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
      exact hempty _ (by omega)
    have hsrc : setFrame σ (base + 1) (xs ++ ys) (base + 1 + i.val) = xs.getD i.val [] := by
      rw [setFrame_get _ _ _ i.val (by simp [hxs, hys]; omega)]
      exact getD_append_left xs ys i.val (by omega)
    have hcp := exec_copyToEmpty (src := base + 1 + i.val) (dst := base) (tmp := base + 1 + n + m)
      (by omega) (by omega) (by omega) (setFrame σ (base + 1) (xs ++ ys)) hbase htmp
    rw [hsrc] at hcp
    have hlen_i : (xs.getD i.val []).length ≤ K := getD_length_le xs i.val hlenX
    exact ⟨9 * (xs.getD i.val []).length + 2, by omega, hcp⟩
  | @projS n m j =>
    simp only [compileBC, Fn.timePoly, Poly.eval_linear, Fn.eval_projS]
    have hj : j.val < m := j.isLt
    have hbase : setFrame σ (base + 1) (xs ++ ys) base = [] := by
      rw [setFrame_outside _ _ _ _ (by omega)]
      exact hempty base (Nat.le_refl base)
    have htmp : setFrame σ (base + 1) (xs ++ ys) (base + 1 + n + m) = [] := by
      rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
      exact hempty _ (by omega)
    have hsrc : setFrame σ (base + 1) (xs ++ ys) (base + 1 + n + j.val) = ys.getD j.val [] := by
      have heq : base + 1 + n + j.val = (base + 1) + (xs.length + j.val) := by omega
      rw [heq, setFrame_get _ _ _ (xs.length + j.val) (by simp [hxs, hys])]
      exact getD_append_right xs ys j.val
    have hcp := exec_copyToEmpty (src := base + 1 + n + j.val) (dst := base) (tmp := base + 1 + n + m)
      (by omega) (by omega) (by omega) (setFrame σ (base + 1) (xs ++ ys)) hbase htmp
    rw [hsrc] at hcp
    have hlen_j : (ys.getD j.val []).length ≤ K := getD_length_le ys j.val hlenY
    exact ⟨9 * (ys.getD j.val []).length + 2, by omega, hcp⟩
  | s0 =>
    simp only [compileBC, Fn.timePoly, Poly.eval_linear, Fn.eval_s0]
    cases xs with
    | cons _ _ => contradiction
    | nil =>
      simp only [List.nil_append]
      have hbase : setFrame σ (base + 1) ys base = [] := by
        rw [setFrame_outside _ _ _ _ (by omega)]
        exact hempty base (Nat.le_refl base)
      have htmp : setFrame σ (base + 1) ys (base + 2) = [] := by
        rw [setFrame_outside _ _ _ _ (by simp [hys])]
        exact hempty _ (by omega)
      have hsrc : setFrame σ (base + 1) ys (base + 1) = ys.getD 0 [] := by
        have hget := setFrame_get σ (base + 1) ys 0 (by omega)
        simpa using hget
      have hcp := exec_copyToEmpty (src := base + 1) (dst := base) (tmp := base + 2)
        (by omega) (by omega) (by omega) (setFrame σ (base + 1) ys) hbase htmp
      rw [hsrc] at hcp
      have hpush := Exec.push base false ((setFrame σ (base + 1) ys).set base (ys.getD 0 []))
      rw [Stacks.set_same, Stacks.set_set_same] at hpush
      have hlen0 : (ys.getD 0 []).length ≤ K := getD_length_le ys 0 hlenY
      exact ⟨(9 * (ys.getD 0 []).length + 2) + 1, by omega, Exec.seq hcp hpush⟩
  | s1 =>
    simp only [compileBC, Fn.timePoly, Poly.eval_linear, Fn.eval_s1]
    cases xs with
    | cons _ _ => contradiction
    | nil =>
      simp only [List.nil_append]
      have hbase : setFrame σ (base + 1) ys base = [] := by
        rw [setFrame_outside _ _ _ _ (by omega)]
        exact hempty base (Nat.le_refl base)
      have htmp : setFrame σ (base + 1) ys (base + 2) = [] := by
        rw [setFrame_outside _ _ _ _ (by simp [hys])]
        exact hempty _ (by omega)
      have hsrc : setFrame σ (base + 1) ys (base + 1) = ys.getD 0 [] := by
        have hget := setFrame_get σ (base + 1) ys 0 (by omega)
        simpa using hget
      have hcp := exec_copyToEmpty (src := base + 1) (dst := base) (tmp := base + 2)
        (by omega) (by omega) (by omega) (setFrame σ (base + 1) ys) hbase htmp
      rw [hsrc] at hcp
      have hpush := Exec.push base true ((setFrame σ (base + 1) ys).set base (ys.getD 0 []))
      rw [Stacks.set_same, Stacks.set_set_same] at hpush
      have hlen0 : (ys.getD 0 []).length ≤ K := getD_length_le ys 0 hlenY
      exact ⟨(9 * (ys.getD 0 []).length + 2) + 1, by omega, Exec.seq hcp hpush⟩
  | pred =>
    simp only [compileBC, Fn.timePoly, Poly.eval_linear, Fn.eval_pred]
    cases xs with
    | cons _ _ => contradiction
    | nil =>
      simp only [List.nil_append]
      have hbase : setFrame σ (base + 1) ys base = [] := by
        rw [setFrame_outside _ _ _ _ (by omega)]
        exact hempty base (Nat.le_refl base)
      have htmp : setFrame σ (base + 1) ys (base + 2) = [] := by
        rw [setFrame_outside _ _ _ _ (by simp [hys])]
        exact hempty _ (by omega)
      have hsrc : setFrame σ (base + 1) ys (base + 1) = ys.getD 0 [] := by
        have hget := setFrame_get σ (base + 1) ys 0 (by omega)
        simpa using hget
      have hcp := exec_copyToEmpty (src := base + 1) (dst := base) (tmp := base + 2)
        (by omega) (by omega) (by omega) (setFrame σ (base + 1) ys) hbase htmp
      rw [hsrc] at hcp
      have hpop := Exec.pop base ((setFrame σ (base + 1) ys).set base (ys.getD 0 []))
      rw [Stacks.set_same, Stacks.set_set_same] at hpop
      have hlen0 : (ys.getD 0 []).length ≤ K := getD_length_le ys 0 hlenY
      exact ⟨(9 * (ys.getD 0 []).length + 2) + 1, by omega, Exec.seq hcp hpop⟩
  | cond =>
    simp only [compileBC, Fn.timePoly, Poly.eval_linear, Fn.eval_cond]
    cases xs with
    | cons _ _ => contradiction
    | nil =>
      simp only [List.nil_append]
      have hbase : setFrame σ (base + 1) ys base = [] := by
        rw [setFrame_outside _ _ _ _ (by omega)]
        exact hempty base (Nat.le_refl base)
      have htmp : setFrame σ (base + 1) ys (base + 5) = [] := by
        rw [setFrame_outside _ _ _ _ (by simp [hys])]
        exact hempty _ (by omega)
      have hy0 : setFrame σ (base + 1) ys (base + 1) = ys.getD 0 [] := by
        have hget := setFrame_get σ (base + 1) ys 0 (by omega)
        simpa using hget
      have hy1 : setFrame σ (base + 1) ys (base + 2) = ys.getD 1 [] := by
        have hget := setFrame_get σ (base + 1) ys 1 (by omega)
        have heq : (base + 1) + 1 = base + 2 := by omega
        rw [heq] at hget; exact hget
      have hy2 : setFrame σ (base + 1) ys (base + 3) = ys.getD 2 [] := by
        have hget := setFrame_get σ (base + 1) ys 2 (by omega)
        have heq : (base + 1) + 2 = base + 3 := by omega
        rw [heq] at hget; exact hget
      have hy3 : setFrame σ (base + 1) ys (base + 4) = ys.getD 3 [] := by
        have hget := setFrame_get σ (base + 1) ys 3 (by omega)
        have heq : (base + 1) + 3 = base + 4 := by omega
        rw [heq] at hget; exact hget
      cases h0 : ys.getD 0 [] with
      | nil =>
        simp only [condW]
        rw [h0] at hy0
        have hcp := exec_copyToEmpty (src := base + 2) (dst := base) (tmp := base + 5)
          (by omega) (by omega) (by omega) (setFrame σ (base + 1) ys) hbase htmp
        rw [hy1] at hcp
        have hlen1 : (ys.getD 1 []).length ≤ K := getD_length_le ys 1 hlenY
        exact ⟨(9 * (ys.getD 1 []).length + 2) + 1, by omega, Exec.ifE hy0 hcp⟩
      | cons b w =>
        rw [h0] at hy0
        cases b with
        | false =>
          simp only [condW]
          have hcp := exec_copyToEmpty (src := base + 3) (dst := base) (tmp := base + 5)
            (by omega) (by omega) (by omega) (setFrame σ (base + 1) ys) hbase htmp
          rw [hy2] at hcp
          have hlen2 : (ys.getD 2 []).length ≤ K := getD_length_le ys 2 hlenY
          exact ⟨(9 * (ys.getD 2 []).length + 2) + 1, by omega, Exec.if0 hy0 hcp⟩
        | true =>
          simp only [condW]
          have hcp := exec_copyToEmpty (src := base + 4) (dst := base) (tmp := base + 5)
            (by omega) (by omega) (by omega) (setFrame σ (base + 1) ys) hbase htmp
          rw [hy3] at hcp
          have hlen3 : (ys.getD 3 []).length ≤ K := getD_length_le ys 3 hlenY
          exact ⟨(9 * (ys.getD 3 []).length + 2) + 1, by omega, Exec.if1 hy0 hcp⟩
  | @comp n m k l h rs ts ihh ihrs ihts =>
    simp only [compileBC, Fn.timePoly, Poly.eval, Poly.eval_linear, Fn.eval_comp]
    have hxy_len : (xs ++ ys).length = n + m := by simp [hxs, hys]
    have hxy_le : ∀ w ∈ (xs ++ ys), w.length ≤ K := by
      intro w hw
      rcases List.mem_append.mp hw with h1 | h2
      · exact hlenX w h1
      · exact hlenY w h2
    have h_arg_rs : ∀ i : Fin k, ((rs i).eval xs []).length ≤
        (Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
        (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K := by
      intro i
      have h1 := (rs i).eval_length_le_fullSizePoly xs [] hlenX (by intro _ h; cases h)
      have h2 := Poly.le_eval_sumFin (fun i' => (rs i').fullSizePoly) i K
      omega
    have h_arg_ts : ∀ j : Fin l, ((ts j).eval xs ys).length ≤
        (Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
        (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K := by
      intro j
      have h1 := (ts j).eval_length_le_fullSizePoly xs ys hlenX hlenY
      have h2 := Poly.le_eval_sumFin (fun j' => (ts j').fullSizePoly) j K
      omega
    have hts_tuple : ∃ c₁ : Nat,
        c₁ ≤ (Poly.sumFin fun j => (ts j).timePoly).eval K +
          l * ((n + m) * (11 * K + 3) +
            (8 * ((Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
                  (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K) + 2)) ∧
        Exec (evalTuple (base + 1) (n + m) (base + 1 + n + m + 1 + k) (base + 1 + n + m + 1 + k + l)
                (fun j => compileBC (base + 1 + n + m + 1 + k + l) (ts j)))
          (setFrame σ (base + 1) (xs ++ ys)) c₁
          (setFrame (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1 + k)
            (List.ofFn fun j => (ts j).eval xs ys)) := by
      rw [← hxy_len]
      exact exec_evalTuple (base + 1) (xs ++ ys) (base + 1 + n + m + 1 + k) (base + 1 + n + m + 1 + k + l)
        (fun j => compileBC (base + 1 + n + m + 1 + k + l) (ts j))
        (fun j => (ts j).eval xs ys)
        (fun j => (ts j).timePoly)
        (setFrame σ (base + 1) (xs ++ ys))
        (by simp [hxs, hys]; omega)
        (by omega)
        (fun a ha => setFrame_get σ (base + 1) (xs ++ ys) a ha)
        (fun r hr _ => by
          rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
          exact hempty r (by omega))
        (fun r hr => by
          rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
          exact hempty r (by omega))
        hxy_le
        h_arg_ts
        (fun j σ' hσ' => ihts j (base + 1 + n + m + 1 + k + l) σ' xs ys K hxs hys hσ' hlenX hlenY)
    rcases hts_tuple with ⟨c₁, hc₁, hexec₁⟩
    have hrs_tuple : ∃ c₂ : Nat,
        c₂ ≤ (Poly.sumFin fun i => (rs i).timePoly).eval K +
          k * (n * (11 * K + 3) +
            (8 * ((Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
                  (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K) + 2)) ∧
        Exec (evalTuple (base + 1) n (base + 1 + n + m + 1) (base + 1 + n + m + 1 + k + l)
                (fun i => compileBC (base + 1 + n + m + 1 + k + l) (rs i)))
          (setFrame (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1 + k)
            (List.ofFn fun j => (ts j).eval xs ys)) c₂
          (setFrame (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1)
            ((List.ofFn fun i => (rs i).eval xs []) ++ (List.ofFn fun j => (ts j).eval xs ys))) := by
      have hlen_rs : (List.ofFn fun i => (rs i).eval xs []).length = k := List.length_ofFn
      rcases exec_evalTuple (base + 1) xs (base + 1 + n + m + 1) (base + 1 + n + m + 1 + k + l)
          (fun i => compileBC (base + 1 + n + m + 1 + k + l) (rs i))
          (fun i => (rs i).eval xs [])
          (fun i => (rs i).timePoly)
          (setFrame (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1 + k)
            (List.ofFn fun j => (ts j).eval xs ys))
          (by simp [hxs]; omega)
          (by omega)
          (fun a ha => by
            rw [setFrame_outside _ _ _ _ (by simp [hxs] at ha; omega)]
            rw [setFrame_get _ _ _ a (by simp [hxs, hys]; omega)]
            exact getD_append_left xs ys a ha)
          (fun r hr1 hr2 => by
            rw [setFrame_outside _ _ _ _ (by omega)]
            rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
            exact hempty r (by omega))
          (fun r hr => by
            rw [setFrame_outside _ _ _ _ (by simp [List.length_ofFn]; omega)]
            rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
            exact hempty r (by omega))
          hlenX
          h_arg_rs
          (fun i σ' hσ' => by
            have h := ihrs i (base + 1 + n + m + 1 + k + l) σ' xs [] K hxs rfl hσ' hlenX (by intro _ h; cases h)
            simpa using h) with
        ⟨c₂, hc₂, hexec₂⟩
      have happ : setFrame
          (setFrame (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1 + k)
            (List.ofFn fun j => (ts j).eval xs ys))
          (base + 1 + n + m + 1)
          (List.ofFn fun i => (rs i).eval xs []) =
        setFrame (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1)
          ((List.ofFn fun i => (rs i).eval xs []) ++ (List.ofFn fun j => (ts j).eval xs ys)) := by
        have h := setFrame_append (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1)
          (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)
        rw [List.length_ofFn] at h
        exact h
      rw [happ] at hexec₂
      rw [hxs] at hc₂ hexec₂
      exact ⟨c₂, hc₂, hexec₂⟩
    rcases hrs_tuple with ⟨c₂, hc₂, hexec₂⟩
    have hrs_mem : ∀ x' ∈ (List.ofFn fun i => (rs i).eval xs []),
        x'.length ≤ (Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
                    (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K := by
      intro x' hx'
      rcases List.mem_ofFn.mp hx' with ⟨i, rfl⟩
      exact h_arg_rs i
    have hts_mem : ∀ y' ∈ (List.ofFn fun j => (ts j).eval xs ys),
        y'.length ≤ (Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
                    (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K := by
      intro y' hy'
      rcases List.mem_ofFn.mp hy' with ⟨j, rfl⟩
      exact h_arg_ts j
    rcases ihh (base + 1 + n + m) (setFrame σ (base + 1) (xs ++ ys))
        (List.ofFn fun i => (rs i).eval xs [])
        (List.ofFn fun j => (ts j).eval xs ys)
        ((Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
         (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K)
        List.length_ofFn List.length_ofFn
        (fun r hr => by
          rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
          exact hempty r (by omega))
        hrs_mem hts_mem with
      ⟨c₃, hc₃, hexec₃⟩
    have hframe_eq :
        (setFrame (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1)
          ((List.ofFn fun i => (rs i).eval xs []) ++ (List.ofFn fun j => (ts j).eval xs ys))).set
          (base + 1 + n + m)
          (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)) =
        setFrame
          ((setFrame σ (base + 1) (xs ++ ys)).set (base + 1 + n + m)
            (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)))
          (base + 1 + n + m + 1)
          ((List.ofFn fun i => (rs i).eval xs []) ++ (List.ofFn fun j => (ts j).eval xs ys)) :=
      (setFrame_set_below (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1) _ _ (by omega)).symm
    rw [hframe_eq] at hexec₃
    have hkl_len : ((List.ofFn fun i => (rs i).eval xs []) ++ (List.ofFn fun j => (ts j).eval xs ys)).length = k + l := by
      simp [List.length_ofFn]
    have hkl_mem : ∀ w ∈ ((List.ofFn fun i => (rs i).eval xs []) ++ (List.ofFn fun j => (ts j).eval xs ys)),
        w.length ≤ (Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
                   (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K := by
      intro w hw
      rcases List.mem_append.mp hw with h1 | h2
      · exact hrs_mem w h1
      · exact hts_mem w h2
    have hclear : ∃ c₄ : Nat,
        c₄ ≤ (k + l) * (2 * ((Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
                             (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K) + 1) ∧
        Exec (clearRange (base + 1 + n + m + 1) (k + l))
          (setFrame
            ((setFrame σ (base + 1) (xs ++ ys)).set (base + 1 + n + m)
              (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)))
            (base + 1 + n + m + 1)
            ((List.ofFn fun i => (rs i).eval xs []) ++ (List.ofFn fun j => (ts j).eval xs ys)))
          c₄
          ((setFrame σ (base + 1) (xs ++ ys)).set (base + 1 + n + m)
            (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys))) := by
      rw [← hkl_len]
      exact exec_clearRange (base + 1 + n + m + 1) _ _
        (fun r hr => by
          rw [Stacks.set_other _ _ (by omega)]
          rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
          exact hempty r (by omega))
        hkl_mem
    rcases hclear with ⟨c₄, hc₄, hexec₄⟩
    have hmove : Exec (moveStack (base + 1 + n + m) base (base + 1 + n + m + 1))
        ((setFrame σ (base + 1) (xs ++ ys)).set (base + 1 + n + m)
          (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)))
        (8 * (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)).length + 2)
        ((setFrame σ (base + 1) (xs ++ ys)).set base
          (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys))) := by
      have hmv := exec_moveStack (src := base + 1 + n + m) (dst := base) (tmp := base + 1 + n + m + 1)
        (by omega) (by omega) (by omega)
        ((setFrame σ (base + 1) (xs ++ ys)).set (base + 1 + n + m)
          (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)))
        (by
          rw [Stacks.set_other _ _ (by omega), setFrame_outside _ _ _ _ (by omega)]
          exact hempty base (Nat.le_refl base))
        (by
          rw [Stacks.set_other _ _ (by omega), setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
          exact hempty _ (by omega))
      have hchild_empty : setFrame σ (base + 1) (xs ++ ys) (base + 1 + n + m) = [] := by
        rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
        exact hempty _ (by omega)
      rw [Stacks.set_same, Stacks.set_set_same, Stacks.set_eq_self hchild_empty] at hmv
      exact hmv
    have hh_len : (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)).length ≤
        h.fullSizePoly.eval
          ((Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
           (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K) :=
      h.eval_length_le_fullSizePoly _ _ hrs_mem hts_mem
    exact ⟨c₁ + (c₂ + (c₃ + (c₄ + (8 * (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)).length + 2)))),
      by omega,
      Exec.seq hexec₁ (Exec.seq hexec₂ (Exec.seq hexec₃ (Exec.seq hexec₄ hmove)))⟩
  | @srec n m g h0 h1 ihg ih0 ih1 =>
    simp only [compileBC, Fn.timePoly, Poly.eval, Poly.eval_linear]
    cases xs with
    | nil => contradiction
    | cons w xs_tail =>
      simp only [List.length_cons] at hxs
      have hxs_tail : xs_tail.length = n := by omega
      have hw_le : w.length ≤ K := hlenX w (.head xs_tail)
      have hlen_tail : ∀ x ∈ xs_tail, x.length ≤ K := fun x hx => hlenX x (.tail w hx)
      let σ_core := setFrame σ (base + 2) (xs_tail ++ ys)
      have hframe_cons : setFrame σ (base + 1) ((w :: xs_tail) ++ ys) = σ_core.set (base + 1) w := rfl
      have hcore_base : σ_core base = [] := by
        dsimp only [σ_core]
        rw [setFrame_outside _ _ _ _ (by omega)]
        exact hempty base (Nat.le_refl base)
      have hcore_b1 : σ_core (base + 1) = [] := by
        dsimp only [σ_core]
        rw [setFrame_outside _ _ _ _ (by omega)]
        exact hempty (base + 1) (by omega)
      have hcore_rev : ∀ r : Nat, base + 2 + n + m ≤ r → σ_core r = [] := by
        intro r hr
        dsimp only [σ_core]
        rw [setFrame_outside _ _ _ _ (by simp [hxs_tail, hys]; omega)]
        exact hempty r (by omega)
      have hcore_xs : ∀ i : Nat, i < n → σ_core (base + 2 + i) = xs_tail.getD i [] := by
        intro i hi
        dsimp only [σ_core]
        rw [setFrame_get _ _ _ i (by simp [hxs_tail, hys]; omega)]
        exact getD_append_left xs_tail ys i (by omega)
      have hcore_ys : ∀ j : Nat, j < m → σ_core (base + 2 + n + j) = ys.getD j [] := by
        intro j hj
        dsimp only [σ_core]
        have heq : base + 2 + n + j = (base + 2) + (xs_tail.length + j) := by omega
        rw [heq, setFrame_get _ _ _ (xs_tail.length + j) (by simp [hxs_tail, hys]; omega)]
        exact getD_append_right xs_tail ys j
      have hcore_xy : ∀ a : Nat, a < (xs_tail ++ ys).length → σ_core ((base + 2) + a) = (xs_tail ++ ys).getD a [] :=
        fun a ha => setFrame_get σ (base + 2) (xs_tail ++ ys) a ha
      -- Step 1: moveRev (base + 1) (base + 2 + n + m)
      have hmv_w : Exec (moveRev (base + 1) (base + 2 + n + m)) (σ_core.set (base + 1) w)
          (4 * w.length + 1) (σ_core.set (base + 2 + n + m) w.reverse) := by
        have hm := exec_moveRev (src := base + 1) (dst := base + 2 + n + m) (by omega) (σ_core.set (base + 1) w)
        have hrev0 : (σ_core.set (base + 1) w) (base + 2 + n + m) = [] := by
          rw [Stacks.set_other _ _ (by omega)]
          exact hcore_rev _ (Nat.le_refl _)
        rw [Stacks.set_same, hrev0, List.append_nil, Stacks.set_set_same,
            Stacks.set_eq_self hcore_b1] at hm
        exact hm
      -- Step 2: evalSubTo (base + 2) (n + m) base (base + 3 + n + m) (compileBC (base + 3 + n + m) g)
      have hxy_tail_len : (xs_tail ++ ys).length = n + m := by simp [hxs_tail, hys]
      have hxy_tail_le : ∀ z ∈ (xs_tail ++ ys), z.length ≤ K := by
        intro z hz
        rcases List.mem_append.mp hz with h1 | h2
        · exact hlen_tail z h1
        · exact hlenY z h2
      have hrec_bound_le : ∀ u : Word, u.length ≤ K →
          ((Fn.srec g h0 h1).eval (u :: xs_tail) ys).length ≤
            (Fn.srec g h0 h1).fullSizePoly.eval K := by
        intro u hu
        apply (Fn.srec g h0 h1).eval_length_le_fullSizePoly (u :: xs_tail) ys _ hlenY
        intro z hz
        cases hz with
        | head => exact hu
        | tail _ hm => exact hlen_tail z hm
      have hg_len_le : (g.eval xs_tail ys).length ≤ (Fn.srec g h0 h1).fullSizePoly.eval K := by
        have h0 := hrec_bound_le [] (Nat.zero_le K)
        simpa [Fn.eval_srec_nil] using h0
      have hg_eval : ∃ c₂ : Nat,
          c₂ ≤ g.timePoly.eval K + (n + m) * (11 * K + 3) +
            (8 * (Fn.srec g h0 h1).fullSizePoly.eval K + 2) ∧
          Exec (evalSubTo (base + 2) (n + m) base (base + 3 + n + m) (compileBC (base + 3 + n + m) g))
            (σ_core.set (base + 2 + n + m) w.reverse) c₂
            ((σ_core.set (base + 2 + n + m) w.reverse).set base (g.eval xs_tail ys)) := by
        rcases ihg (base + 3 + n + m) (σ_core.set (base + 2 + n + m) w.reverse) xs_tail ys K
            hxs_tail hys
            (fun r hr => by
              rw [Stacks.set_other _ _ (by omega)]
              exact hcore_rev r (by omega))
            hlen_tail hlenY with
          ⟨c_g, hc_g, hexec_g⟩
        rcases exec_evalSubTo (base + 2) (xs_tail ++ ys) base (base + 3 + n + m)
            (compileBC (base + 3 + n + m) g)
            (σ_core.set (base + 2 + n + m) w.reverse)
            (g.eval xs_tail ys)
            (by simp [hxs_tail, hys]; omega)
            (by omega)
            (fun a ha => by
              rw [Stacks.set_other _ _ (by simp [hxs_tail, hys] at ha; omega)]
              exact hcore_xy a ha)
            (by rw [Stacks.set_other _ _ (by omega)]; exact hcore_base)
            (fun r hr => by
              rw [Stacks.set_other _ _ (by omega)]
              exact hcore_rev r (by omega))
            hxy_tail_le
            hg_len_le
            hexec_g with
          ⟨c₂, hc₂, hexec₂⟩
        rw [hxy_tail_len] at hc₂ hexec₂
        exact ⟨c₂, by omega, hexec₂⟩
      rcases hg_eval with ⟨c₂, hc₂, hexec₂⟩
      -- Step 3: recLoop
      let stepFn : Bool → Word → Word → Word :=
        fun b u r => if b then h1.eval (u :: xs_tail) (r :: ys) else h0.eval (u :: xs_tail) (r :: ys)
      have hstate_init : ((σ_core.set (base + 2 + n + m) w.reverse).set base (g.eval xs_tail ys)) =
          recLoopState σ_core base n m (g.eval xs_tail ys) stepFn [] w.reverse := by
        simp only [recLoopState, recIter_nil]
        have hb1 : ((σ_core.set base (g.eval xs_tail ys)).set (base + 2 + n + m) w.reverse) (base + 1) = [] := by
          rw [Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega)]
          exact hcore_b1
        rw [Stacks.set_eq_self hb1]
        exact Stacks.set_set_comm σ_core w.reverse (g.eval xs_tail ys) (by omega)
      rw [hstate_init] at hexec₂
      have hK_le_Krec : K ≤ (Fn.srec g h0 h1).fullSizePoly.eval K := by
        simp [Fn.fullSizePoly, Poly.eval_add, Poly.eval_var]
      have hxs_le_Krec : ∀ x ∈ xs_tail, x.length ≤ (Fn.srec g h0 h1).fullSizePoly.eval K :=
        fun x hx => Nat.le_trans (hlen_tail x hx) hK_le_Krec
      have hys_le_Krec : ∀ y ∈ ys, y.length ≤ (Fn.srec g h0 h1).fullSizePoly.eval K :=
        fun y hy => Nat.le_trans (hlenY y hy) hK_le_Krec
      have hstep0 : ∀ (u acc : Word) (σ' : Stacks),
          u.length ≤ (Fn.srec g h0 h1).fullSizePoly.eval K →
          acc.length ≤ (Fn.srec g h0 h1).fullSizePoly.eval K →
          (∀ r : Nat, base + 3 + n + m ≤ r → σ' r = []) →
          ∃ c : Nat,
            c ≤ h0.timePoly.eval ((Fn.srec g h0 h1).fullSizePoly.eval K) +
                h1.timePoly.eval ((Fn.srec g h0 h1).fullSizePoly.eval K) ∧
            Exec (compileBC (base + 3 + n + m) h0)
              (setFrame σ' ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))) c
              ((setFrame σ' ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))).set
                (base + 3 + n + m) (stepFn false u acc)) := by
        intro u acc σ' hu_le hacc_le hσ'
        rcases ih0 (base + 3 + n + m) σ' (u :: xs_tail) (acc :: ys)
            ((Fn.srec g h0 h1).fullSizePoly.eval K)
            (by simp [hxs_tail]) (by simp [hys]) hσ'
            (by intro z hz; cases hz with | head => exact hu_le | tail _ hm => exact hxs_le_Krec z hm)
            (by intro z hz; cases hz with | head => exact hacc_le | tail _ hm => exact hys_le_Krec z hm) with
          ⟨c, hc, hexec⟩
        exact ⟨c, by omega, hexec⟩
      have hstep1 : ∀ (u acc : Word) (σ' : Stacks),
          u.length ≤ (Fn.srec g h0 h1).fullSizePoly.eval K →
          acc.length ≤ (Fn.srec g h0 h1).fullSizePoly.eval K →
          (∀ r : Nat, base + 3 + n + m ≤ r → σ' r = []) →
          ∃ c : Nat,
            c ≤ h0.timePoly.eval ((Fn.srec g h0 h1).fullSizePoly.eval K) +
                h1.timePoly.eval ((Fn.srec g h0 h1).fullSizePoly.eval K) ∧
            Exec (compileBC (base + 3 + n + m) h1)
              (setFrame σ' ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))) c
              ((setFrame σ' ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))).set
                (base + 3 + n + m) (stepFn true u acc)) := by
        intro u acc σ' hu_le hacc_le hσ'
        rcases ih1 (base + 3 + n + m) σ' (u :: xs_tail) (acc :: ys)
            ((Fn.srec g h0 h1).fullSizePoly.eval K)
            (by simp [hxs_tail]) (by simp [hys]) hσ'
            (by intro z hz; cases hz with | head => exact hu_le | tail _ hm => exact hxs_le_Krec z hm)
            (by intro z hz; cases hz with | head => exact hacc_le | tail _ hm => exact hys_le_Krec z hm) with
          ⟨c, hc, hexec⟩
        exact ⟨c, by omega, hexec⟩
      rcases exec_recLoop base n m (compileBC (base + 3 + n + m) h0) (compileBC (base + 3 + n + m) h1)
          σ_core xs_tail ys (g.eval xs_tail ys) stepFn
          hK_le_Krec hxs_tail hys hcore_xs hcore_ys
          (fun r hr => hcore_rev r (by omega))
          hxs_le_Krec hys_le_Krec
          (fun u hu => hrec_bound_le u hu)
          hstep0 hstep1
          w.reverse [] (by simp [List.length_reverse]; exact hw_le) with
        ⟨c₃, hc₃, hexec₃⟩
      simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hc₃ hexec₃
      have hstate_final :
          recLoopState σ_core base n m (g.eval xs_tail ys) stepFn w [] =
          (setFrame σ (base + 1) ((w :: xs_tail) ++ ys)).set base ((Fn.srec g h0 h1).eval (w :: xs_tail) ys) := by
        rw [hframe_cons]
        simp only [recLoopState, Fn.eval_srec, List.headD_cons, List.tail_cons]
        have hrev_empty : (σ_core.set base (recIter (g.eval xs_tail ys) stepFn w)) (base + 2 + n + m) = [] := by
          rw [Stacks.set_other _ _ (by omega)]
          exact hcore_rev (base + 2 + n + m) (Nat.le_refl _)
        rw [Stacks.set_eq_self hrev_empty]
        exact Stacks.set_set_comm σ_core (recIter (g.eval xs_tail ys) stepFn w) w (by omega)
      rw [hstate_final] at hexec₃
      have hmul_bound :
          w.length *
            ((h0.timePoly.eval ((Fn.srec g h0 h1).fullSizePoly.eval K) +
              h1.timePoly.eval ((Fn.srec g h0 h1).fullSizePoly.eval K)) +
             ((n + 1) + (m + 1)) * (11 * (Fn.srec g h0 h1).fullSizePoly.eval K + 3) +
             (10 * (Fn.srec g h0 h1).fullSizePoly.eval K + 7)) ≤
          K *
            ((h0.timePoly.eval ((Fn.srec g h0 h1).fullSizePoly.eval K) +
              h1.timePoly.eval ((Fn.srec g h0 h1).fullSizePoly.eval K)) +
             ((n + 1) + (m + 1)) * (11 * (Fn.srec g h0 h1).fullSizePoly.eval K + 3) +
             (10 * (Fn.srec g h0 h1).fullSizePoly.eval K + 7)) :=
        Nat.mul_le_mul_right _ hw_le
      exact ⟨(4 * w.length + 1) + (c₂ + c₃),
        by omega,
        Exec.seq hmv_w (Exec.seq hexec₂ hexec₃)⟩

/-- Top-level stack statement for a unary BC program `prog : Fn 1 0`:
    moves the input word from stack `0` to stack `1` and executes `compileBC 0 prog`
    so the result is left on stack `0`. -/
def topCompileBC (prog : Fn 1 0) : Stmt :=
  .seq (moveStack 0 1 2) (compileBC 0 prog)

/-- Syntactic polynomial bounding the TM step count of `stmtToTM (topCompileBC prog)`. -/
def topTimePoly (prog : Fn 1 0) : Poly :=
  .mul (.const 2) (.add (.linear 8 2) prog.timePoly)

theorem topCompileBC_haltsWithin (prog : Fn 1 0) (x : Word) :
    (stmtToTM (topCompileBC prog)).HaltsWithin x
      ((topTimePoly prog).eval x.length)
      (prog.eval [x] []) := by
  let σ_empty : Stacks := fun _ => []
  have hmv : Exec (moveStack 0 1 2) (initStacks x) (8 * x.length + 2)
      (setFrame σ_empty 1 ([x] ++ [])) := by
    have hm := exec_moveStack (src := 0) (dst := 1) (tmp := 2)
      (by decide) (by decide) (by decide) (initStacks x) rfl rfl
    have h0 : (initStacks x 0).length = x.length := rfl
    have hst : ((initStacks x).set 0 []).set 1 (initStacks x 0) = setFrame σ_empty 1 ([x] ++ []) := by
      funext k
      simp only [initStacks, List.cons_append, List.nil_append, setFrame_cons, setFrame_nil, σ_empty, Stacks.set]
      by_cases hk1 : k = 1
      · subst hk1; rfl
      · by_cases hk0 : k = 0
        · subst hk0; rfl
        · simp [hk1, hk0]
    rw [hst] at hm
    exact hm
  rcases exec_compileBC prog 0 σ_empty [x] [] x.length rfl rfl
      (fun _ _ => rfl)
      (fun z hz => by cases hz with | head => exact Nat.le_refl _ | tail _ h => cases h)
      (fun _ h => by cases h) with
    ⟨c, hc, hexec⟩
  have hfull := Exec.seq hmv hexec
  rcases stmtToTM_haltsWithin (topCompileBC prog) x hfull with ⟨s, hs, hstep, hout⟩
  rw [Stacks.set_same] at hout
  refine ⟨s, ?_, hstep, hout⟩
  simp only [topTimePoly, Poly.eval, Poly.eval_linear]
  omega

/-- **Bellantoni–Cook Polynomial-Time Soundness (`BCDefinable f → FP f`)**:
    Every unary word function definable in the Bellantoni–Cook safe recursion algebra
    is computable in polynomial time by a deterministic multi-tape Turing machine. -/
theorem bc_soundness (f : Word → Word) (h : BCDefinable f) : FP f := by
  rcases h with ⟨prog, hprog⟩
  refine ⟨stmtToTM (topCompileBC prog), topTimePoly prog, fun x => ?_⟩
  rw [← hprog x]
  exact topCompileBC_haltsWithin prog x

end FeasibleUnivalence.BC
