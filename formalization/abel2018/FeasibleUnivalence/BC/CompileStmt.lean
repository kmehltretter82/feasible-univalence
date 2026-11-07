/-
  FeasibleUnivalence/BC/CompileStmt.lean

  Compilation of structured stack programs (`Stmt` in `StackProg.lean`) to deterministic
  multi-tape Turing machines (`TM` in `TM.lean`), together with the big-step-to-TM
  simulation theorem showing that every `Exec s σ c σ'` is simulated in at most `2 * c`
  TM transitions.
-/

import FeasibleUnivalence.BC.StackProg
import FeasibleUnivalence.BC.TM

namespace FeasibleUnivalence.BC

/-! ## 1. Basic `TM.run` and `Cfg` Lemmas -/

theorem Cfg.ext {k Q G : Nat} {c₁ c₂ : Cfg k Q G}
    (hs : c₁.state.val = c₂.state.val)
    (ht : ∀ j : Fin k, c₁.tapes j = c₂.tapes j) : c₁ = c₂ := by
  cases c₁
  cases c₂
  simp only [Cfg.mk.injEq] at hs ht ⊢
  exact ⟨Fin.ext hs, funext ht⟩

namespace TM

variable (M : TM)

theorem run_of_step_none {c : Cfg M.k M.Q M.G} (h : M.step c = none) :
    ∀ n : Nat, M.run n c = c
  | 0 => rfl
  | n + 1 => by simp [run, h]

theorem run_add (a b : Nat) (c : Cfg M.k M.Q M.G) :
    M.run (a + b) c = M.run b (M.run a c) := by
  induction a generalizing c with
  | zero => simp [run]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [run]
    cases h : M.step c with
    | none => exact (M.run_of_step_none h b).symm
    | some c' => exact ih c'

theorem run_one_of_step_some {c c' : Cfg M.k M.Q M.G} (h : M.step c = some c') :
    M.run 1 c = c' := by
  simp [run, h]

@[simp] theorem blank_val : M.blank.val = 0 := rfl

@[simp] theorem bitSym_val (b : Bool) : (M.bitSym b).val = if b then 2 else 1 := rfl

@[simp] theorem decodeBit_blank : M.decodeBit M.blank = none := by
  simp [decodeBit, blank]

@[simp] theorem decodeBit_bitSym (b : Bool) : M.decodeBit (M.bitSym b) = some b := by
  cases b <;> simp [decodeBit, bitSym]

@[simp] theorem readBits_map_bitSym : ∀ w : Word, M.readBits (w.map M.bitSym) = w
  | [] => rfl
  | b :: w => by simp [readBits, readBits_map_bitSym w]

theorem output_of_inputTape (c : Cfg M.k M.Q M.G) (w : Word)
    (h0 : c.tapes ⟨0, M.hk⟩ = M.inputTape w) :
    M.output c = w := by
  unfold output
  rw [h0]
  cases w with
  | nil => simp [inputTape, readBits]
  | cons b w => simp [inputTape, readBits, readBits_map_bitSym]

theorem inputTape_nil : M.inputTape [] = M.blankTape := rfl

theorem write_head_move_S (t : Tape (Fin M.G)) :
    (t.write t.head).move M.blank .S = t := by
  cases t
  rfl

theorem write_head_move_L_inputTape (w : Word) :
    ((M.inputTape w).write (M.inputTape w).head).move M.blank .L =
      ⟨[], M.blank, w.map M.bitSym⟩ := by
  cases w with
  | nil =>
    simp [inputTape, Tape.write, Tape.move, Tape.consB]
  | cons b w =>
    cases w with
    | nil =>
      have hne : M.bitSym b ≠ M.blank := by
        intro h
        have hv := congrArg Fin.val h
        cases b <;> simp [bitSym, blank] at hv
      simp [inputTape, Tape.write, Tape.move, Tape.consB, hne]
    | cons b' w' =>
      simp [inputTape, Tape.write, Tape.move, Tape.consB]

theorem write_bitSym_move_S_after_L (b : Bool) (w : Word) :
    ((⟨[], M.blank, w.map M.bitSym⟩ : Tape (Fin M.G)).write (M.bitSym b)).move M.blank .S =
      M.inputTape (b :: w) := rfl

theorem write_blank_move_R_inputTape (w : Word) :
    ((M.inputTape w).write M.blank).move M.blank .R = M.inputTape w.tail := by
  cases w with
  | nil =>
    simp [inputTape, Tape.write, Tape.move, Tape.consB]
  | cons b w =>
    cases w with
    | nil =>
      simp [inputTape, Tape.write, Tape.move, Tape.consB]
    | cons b' w' =>
      simp [inputTape, Tape.write, Tape.move, Tape.consB]

end TM

/-! ## 2. Stack Bounds & Flat TM Instruction Code (`TMInstr`) -/

/-- Highest stack index referenced by a `Stmt`. -/
def Stmt.maxStack : Stmt → Nat
  | .skip => 0
  | .push i _ => i
  | .pop i => i
  | .seq s t => max s.maxStack t.maxStack
  | .ifTop i sE s0 s1 => max i (max sE.maxStack (max s0.maxStack s1.maxStack))
  | .whileNE i body => max i body.maxStack

/-- Flat Turing-machine instructions for simulating stack programs. -/
inductive TMInstr : Type where
  | moveL (i : Nat)
  | writeBit (i : Nat) (b : Bool)
  | popR (i : Nat)
  | branch (i : Nat) (pcE pc0 pc1 : Nat)
  deriving DecidableEq, Repr

/-- Unconditional jump instruction (branches to `target` on all 3 symbols of tape 0). -/
def TMInstr.jump (target : Nat) : TMInstr :=
  .branch 0 target target target

/-- Compile a `Stmt` starting at instruction offset `pc` into a flat list of `TMInstr`. -/
def compileStmt : Stmt → Nat → List TMInstr
  | .skip, _ => []
  | .push i b, _ => [.moveL i, .writeBit i b]
  | .pop i, _ => [.popR i]
  | .seq s t, pc =>
      let cs := compileStmt s pc
      cs ++ compileStmt t (pc + cs.length)
  | .ifTop i sE s0 s1, pc =>
      let pE := pc + 1
      let cE := compileStmt sE pE
      let p0 := pE + cE.length + 1
      let c0 := compileStmt s0 p0
      let p1 := p0 + c0.length + 1
      let c1 := compileStmt s1 p1
      let pEnd := p1 + c1.length
      [.branch i pE p0 p1] ++ cE ++ [.jump pEnd] ++ c0 ++ [.jump pEnd] ++ c1
  | .whileNE i body, pc =>
      let pBody := pc + 1
      let cBody := compileStmt body pBody
      let pEnd := pBody + cBody.length + 1
      [.branch i pEnd pBody pBody] ++ cBody ++ [.jump pc]

/-- Clamp a program counter `pc : Nat` into `Fin (len + 1)`. -/
def clampPC (len pc : Nat) : Fin (len + 1) :=
  if h : pc < len + 1 then ⟨pc, h⟩ else ⟨len, Nat.lt_succ_self len⟩

@[simp] theorem clampPC_val_of_le {len pc : Nat} (h : pc ≤ len) :
    (clampPC len pc).val = pc := by
  unfold clampPC
  have hlt : pc < len + 1 := Nat.lt_succ_of_le h
  simp [hlt]

@[simp] theorem clampPC_self (len : Nat) :
    clampPC len len = ⟨len, Nat.lt_succ_self len⟩ := by
  ext
  exact clampPC_val_of_le (Nat.le_refl len)

/-- Bit symbol in `Fin 3` (definitionally equal to `(codeTM k hk code).bitSym b`). -/
def bitFin3 (b : Bool) : Fin 3 :=
  ⟨if b then 2 else 1, by cases b <;> decide⟩

/-- Blank symbol in `Fin 3`. -/
def blankFin3 : Fin 3 := ⟨0, by omega⟩

/-- Turn a flat instruction list `code : List TMInstr` over `k` tapes into a `TM`. -/
def codeTM (k : Nat) (hk : 0 < k) (code : List TMInstr) : TM where
  k := k
  Q := code.length + 1
  G := 3
  hk := hk
  hQ := Nat.zero_lt_succ code.length
  hG := by omega
  δ q heads :=
    match code[q.val]? with
    | none => none
    | some (.moveL i) =>
        some (clampPC code.length (q.val + 1),
              heads,
              fun j => if j.val = i then .L else .S)
    | some (.writeBit i b) =>
        some (clampPC code.length (q.val + 1),
              fun j => if j.val = i then bitFin3 b else heads j,
              fun _ => .S)
    | some (.popR i) =>
        some (clampPC code.length (q.val + 1),
              fun j => if j.val = i then blankFin3 else heads j,
              fun j => if j.val = i then .R else .S)
    | some (.branch i pcE pc0 pc1) =>
        let sym := if h : i < k then (heads ⟨i, h⟩).val else 0
        let nextPC := if sym = 0 then pcE else if sym = 1 then pc0 else pc1
        some (clampPC code.length nextPC, heads, fun _ => .S)

@[simp] theorem codeTM_bitSym (k : Nat) (hk : 0 < k) (code : List TMInstr) (b : Bool) :
    (codeTM k hk code).bitSym b = bitFin3 b := by
  cases b <;> rfl

@[simp] theorem codeTM_blank (k : Nat) (hk : 0 < k) (code : List TMInstr) :
    (codeTM k hk code).blank = blankFin3 := rfl

/-- Canonical `TM` configuration corresponding to program counter `pc` and stack assignment `σ`. -/
def cfgOf (k : Nat) (hk : 0 < k) (code : List TMInstr) (pc : Nat) (σ : Stacks) :
    Cfg (codeTM k hk code).k (codeTM k hk code).Q (codeTM k hk code).G where
  state := clampPC code.length pc
  tapes := fun j => (codeTM k hk code).inputTape (σ j.val)

theorem cfgOf_eq {k : Nat} {hk : 0 < k} {code : List TMInstr}
    {pc₁ pc₂ : Nat} {σ₁ σ₂ : Stacks} (hpc : pc₁ = pc₂) (hσ : ∀ j : Fin k, σ₁ j.val = σ₂ j.val) :
    cfgOf k hk code pc₁ σ₁ = cfgOf k hk code pc₂ σ₂ := by
  subst hpc
  apply Cfg.ext
  · rfl
  · intro j
    simp only [cfgOf]
    rw [hσ j]

theorem init_eq_cfgOf (k : Nat) (hk : 0 < k) (code : List TMInstr) (x : Word) :
    (codeTM k hk code).init x = cfgOf k hk code 0 (initStacks x) := by
  apply Cfg.ext
  · simp [TM.init, cfgOf]
  · intro j
    simp only [TM.init, cfgOf, initStacks]
    by_cases hj : j.val = 0
    · simp [hj]
    · simp [hj, TM.inputTape_nil]

theorem step_cfgOf_end (k : Nat) (hk : 0 < k) (code : List TMInstr) (σ : Stacks) :
    (codeTM k hk code).step (cfgOf k hk code code.length σ) = none := by
  simp [TM.step, codeTM, cfgOf]

/-! ## 3. Subcode Slice Predicate & Single-Instruction Stepping Lemmas -/

/-- `sub` occurs as a contiguous slice of `code` starting at index `pc`. -/
def SubcodeAt (code sub : List TMInstr) (pc : Nat) : Prop :=
  pc + sub.length ≤ code.length ∧
  ∀ j : Nat, j < sub.length → code[pc + j]? = sub[j]?

theorem subcodeAt_self (code : List TMInstr) : SubcodeAt code code 0 := by
  refine ⟨by omega, fun j _ => by simp⟩

theorem subcodeAt_append_left {code s1 s2 : List TMInstr} {pc : Nat}
    (h : SubcodeAt code (s1 ++ s2) pc) : SubcodeAt code s1 pc := by
  rcases h with ⟨hlen, hget⟩
  rw [List.length_append] at hlen
  refine ⟨by omega, fun j hj => ?_⟩
  rw [hget j (by rw [List.length_append]; omega)]
  exact List.getElem?_append_left hj

theorem subcodeAt_append_right {code s1 s2 : List TMInstr} {pc : Nat}
    (h : SubcodeAt code (s1 ++ s2) pc) : SubcodeAt code s2 (pc + s1.length) := by
  rcases h with ⟨hlen, hget⟩
  rw [List.length_append] at hlen
  refine ⟨by omega, fun j hj => ?_⟩
  have h1 := hget (s1.length + j) (by rw [List.length_append]; omega)
  rw [← Nat.add_assoc] at h1
  rw [h1, List.getElem?_append_right (Nat.le_add_right s1.length j)]
  simp [Nat.add_sub_cancel_left]

theorem subcodeAt_singleton {code : List TMInstr} {instr : TMInstr} {pc : Nat}
    (h : SubcodeAt code [instr] pc) :
    pc + 1 ≤ code.length ∧ code[pc]? = some instr := by
  rcases h with ⟨hlen, hget⟩
  have h0 := hget 0 Nat.zero_lt_one
  simp only [Nat.add_zero, List.length_singleton] at h0 hlen
  exact ⟨hlen, h0⟩

theorem step_push_pair {k : Nat} (hk : 0 < k) (code : List TMInstr)
    {i : Nat} (b : Bool) {pc : Nat} (σ : Stacks)
    (hsub : SubcodeAt code [.moveL i, .writeBit i b] pc) :
    (codeTM k hk code).run 2 (cfgOf k hk code pc σ) =
      cfgOf k hk code (pc + 2) (σ.set i (b :: σ i)) := by
  have h1 := subcodeAt_singleton (subcodeAt_append_left (s1 := [.moveL i]) (s2 := [.writeBit i b]) hsub)
  have h2 := subcodeAt_singleton (subcodeAt_append_right (s1 := [.moveL i]) (s2 := [.writeBit i b]) hsub)
  simp only [List.length_singleton] at h2
  have hpc : pc ≤ code.length := by omega
  have hpc1 : pc + 1 ≤ code.length := h1.1
  let midCfg : Cfg (codeTM k hk code).k (codeTM k hk code).Q (codeTM k hk code).G :=
    ⟨clampPC code.length (pc + 1),
     fun j => if j.val = i then ⟨[], (codeTM k hk code).blank, (σ i).map (codeTM k hk code).bitSym⟩
              else (codeTM k hk code).inputTape (σ j.val)⟩
  have hstep1 : (codeTM k hk code).step (cfgOf k hk code pc σ) = some midCfg := by
    unfold TM.step
    rw [show (codeTM k hk code).δ (cfgOf k hk code pc σ).state
          (fun j => ((cfgOf k hk code pc σ).tapes j).head) =
        some (clampPC code.length (pc + 1),
              fun j => ((cfgOf k hk code pc σ).tapes j).head,
              fun j => if j.val = i then .L else .S) by
      simp [codeTM, cfgOf, clampPC_val_of_le hpc, h1.2]]
    dsimp only
    congr 1
    apply Cfg.ext
    · rfl
    · intro j
      dsimp only [midCfg, cfgOf]
      by_cases hj : j.val = i
      · rw [if_pos hj, if_pos hj, ← hj]
        exact (codeTM k hk code).write_head_move_L_inputTape (σ j.val)
      · rw [if_neg hj, if_neg hj]
        exact (codeTM k hk code).write_head_move_S _
  have hstep2 : (codeTM k hk code).step midCfg =
      some (cfgOf k hk code (pc + 2) (σ.set i (b :: σ i))) := by
    unfold TM.step
    have hδ2 : (codeTM k hk code).δ midCfg.state (fun j => (midCfg.tapes j).head) =
        some (clampPC code.length (pc + 1 + 1),
              fun j => if j.val = i then (codeTM k hk code).bitSym b else (midCfg.tapes j).head,
              fun _ => .S) := by
      dsimp only [codeTM, midCfg]
      rw [clampPC_val_of_le hpc1, h2.2]
      rfl
    rw [hδ2]
    dsimp only
    congr 1
    apply Cfg.ext
    · rfl
    · intro j
      dsimp only [midCfg, cfgOf]
      by_cases hj : j.val = i
      · rw [if_pos hj, if_pos hj, hj, Stacks.set_same]
        exact (codeTM k hk code).write_bitSym_move_S_after_L b (σ i)
      · rw [if_neg hj, if_neg hj, Stacks.set_other σ _ hj]
        exact (codeTM k hk code).write_head_move_S _
  change (codeTM k hk code).run (1 + 1) (cfgOf k hk code pc σ) = _
  rw [(codeTM k hk code).run_add 1 1,
      (codeTM k hk code).run_one_of_step_some hstep1,
      (codeTM k hk code).run_one_of_step_some hstep2]

theorem step_popR_single {k : Nat} (hk : 0 < k) (code : List TMInstr)
    {i : Nat} {pc : Nat} (σ : Stacks)
    (hsub : SubcodeAt code [.popR i] pc) :
    (codeTM k hk code).run 1 (cfgOf k hk code pc σ) =
      cfgOf k hk code (pc + 1) (σ.set i (σ i).tail) := by
  rcases subcodeAt_singleton hsub with ⟨hpc1, hget⟩
  have hpc : pc ≤ code.length := by omega
  have hstep : (codeTM k hk code).step (cfgOf k hk code pc σ) =
      some (cfgOf k hk code (pc + 1) (σ.set i (σ i).tail)) := by
    unfold TM.step
    have hδ : (codeTM k hk code).δ (cfgOf k hk code pc σ).state
          (fun j => ((cfgOf k hk code pc σ).tapes j).head) =
        some (clampPC code.length (pc + 1),
              fun j => if j.val = i then (codeTM k hk code).blank else ((cfgOf k hk code pc σ).tapes j).head,
              fun j => if j.val = i then .R else .S) := by
      dsimp only [codeTM, cfgOf]
      rw [clampPC_val_of_le hpc, hget]
      rfl
    rw [hδ]
    dsimp only
    congr 1
    apply Cfg.ext
    · rfl
    · intro j
      dsimp only [cfgOf]
      by_cases hj : j.val = i
      · rw [if_pos hj, if_pos hj, hj, Stacks.set_same]
        exact (codeTM k hk code).write_blank_move_R_inputTape (σ i)
      · rw [if_neg hj, if_neg hj, Stacks.set_other σ _ hj]
        exact (codeTM k hk code).write_head_move_S _
  exact (codeTM k hk code).run_one_of_step_some hstep

theorem step_jump_single {k : Nat} (hk : 0 < k) (code : List TMInstr)
    {target pc : Nat} (σ : Stacks)
    (hsub : SubcodeAt code [.jump target] pc) :
    (codeTM k hk code).run 1 (cfgOf k hk code pc σ) =
      cfgOf k hk code target σ := by
  rcases subcodeAt_singleton hsub with ⟨hpc1, hget⟩
  have hpc : pc ≤ code.length := by omega
  have hstep : (codeTM k hk code).step (cfgOf k hk code pc σ) =
      some (cfgOf k hk code target σ) := by
    unfold TM.step
    rw [show (codeTM k hk code).δ (cfgOf k hk code pc σ).state
          (fun j => ((cfgOf k hk code pc σ).tapes j).head) =
        some (clampPC code.length target,
              fun j => ((cfgOf k hk code pc σ).tapes j).head,
              fun _ => .S) by
      simp [codeTM, cfgOf, TMInstr.jump, clampPC_val_of_le hpc, hget]]
    rfl
  exact (codeTM k hk code).run_one_of_step_some hstep

theorem step_branch_single {k : Nat} (hk : 0 < k) (code : List TMInstr)
    {i pcE pc0 pc1 pc : Nat} (hi : i < k)
    (σ : Stacks) (hsub : SubcodeAt code [.branch i pcE pc0 pc1] pc) :
    (match σ i with
     | [] => (codeTM k hk code).run 1 (cfgOf k hk code pc σ) = cfgOf k hk code pcE σ
     | false :: _ => (codeTM k hk code).run 1 (cfgOf k hk code pc σ) = cfgOf k hk code pc0 σ
     | true :: _ => (codeTM k hk code).run 1 (cfgOf k hk code pc σ) = cfgOf k hk code pc1 σ) := by
  rcases subcodeAt_singleton hsub with ⟨hpc1, hget⟩
  have hpc : pc ≤ code.length := by omega
  cases hσi : σ i with
  | nil =>
    have hstep : (codeTM k hk code).step (cfgOf k hk code pc σ) =
        some (cfgOf k hk code pcE σ) := by
      unfold TM.step
      rw [show (codeTM k hk code).δ (cfgOf k hk code pc σ).state
            (fun j => ((cfgOf k hk code pc σ).tapes j).head) =
          some (clampPC code.length pcE,
                fun j => ((cfgOf k hk code pc σ).tapes j).head,
                fun _ => .S) by
        simp [codeTM, cfgOf, clampPC_val_of_le hpc, hget, hi, hσi, TM.inputTape]]
      rfl
    exact (codeTM k hk code).run_one_of_step_some hstep
  | cons b w =>
    cases b
    · have hstep : (codeTM k hk code).step (cfgOf k hk code pc σ) =
          some (cfgOf k hk code pc0 σ) := by
        unfold TM.step
        rw [show (codeTM k hk code).δ (cfgOf k hk code pc σ).state
              (fun j => ((cfgOf k hk code pc σ).tapes j).head) =
            some (clampPC code.length pc0,
                  fun j => ((cfgOf k hk code pc σ).tapes j).head,
                  fun _ => .S) by
          simp [codeTM, cfgOf, clampPC_val_of_le hpc, hget, hi, hσi, TM.inputTape]]
        rfl
      exact (codeTM k hk code).run_one_of_step_some hstep
    · have hstep : (codeTM k hk code).step (cfgOf k hk code pc σ) =
          some (cfgOf k hk code pc1 σ) := by
        unfold TM.step
        rw [show (codeTM k hk code).δ (cfgOf k hk code pc σ).state
              (fun j => ((cfgOf k hk code pc σ).tapes j).head) =
            some (clampPC code.length pc1,
                  fun j => ((cfgOf k hk code pc σ).tapes j).head,
                  fun _ => .S) by
          simp [codeTM, cfgOf, clampPC_val_of_le hpc, hget, hi, hσi, TM.inputTape]]
        rfl
      exact (codeTM k hk code).run_one_of_step_some hstep

/-! ## 4. Main `Stmt` → `TM` Simulation Theorem -/

/-- Every big-step execution `Exec s σ c σ'` of a stack program `s` (whose stack indices
    are `< k`) is simulated by `(codeTM k hk code)` in at most `2 * c` transitions. -/
theorem exec_sim_tm {k : Nat} (hk : 0 < k) (code : List TMInstr)
    {s : Stmt} {σ σ' : Stacks} {c : Nat} (hexec : Exec s σ c σ')
    (hmax : s.maxStack < k) (pc : Nat)
    (hsub : SubcodeAt code (compileStmt s pc) pc) :
    ∃ steps : Nat,
      steps ≤ 2 * c ∧
      (codeTM k hk code).run steps (cfgOf k hk code pc σ) =
        cfgOf k hk code (pc + (compileStmt s pc).length) σ' := by
  induction hexec generalizing pc with
  | skip σ =>
    exact ⟨0, Nat.le_refl 0, cfgOf_eq (by simp [compileStmt]) (fun _ => rfl)⟩
  | push i b σ =>
    exact ⟨2, Nat.le_refl 2, step_push_pair hk code b σ hsub⟩
  | pop i σ =>
    exact ⟨1, by omega, step_popR_single hk code σ hsub⟩
  | @seq s t σ₁ σ₂ σ₃ c₁ c₂ _ _ ihs iht =>
    simp only [Stmt.maxStack] at hmax
    have hmax_s : s.maxStack < k := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax
    have hmax_t : t.maxStack < k := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax
    have hsub_s : SubcodeAt code (compileStmt s pc) pc :=
      subcodeAt_append_left hsub
    have hsub_t : SubcodeAt code (compileStmt t (pc + (compileStmt s pc).length))
        (pc + (compileStmt s pc).length) :=
      subcodeAt_append_right hsub
    rcases ihs hmax_s pc hsub_s with ⟨steps₁, hle₁, hrun₁⟩
    rcases iht hmax_t (pc + (compileStmt s pc).length) hsub_t with ⟨steps₂, hle₂, hrun₂⟩
    refine ⟨steps₁ + steps₂, by omega, ?_⟩
    rw [(codeTM k hk code).run_add steps₁ steps₂, hrun₁, hrun₂]
    exact cfgOf_eq (by simp [compileStmt, List.length_append, Nat.add_assoc]) (fun _ => rfl)
  | @ifE i sE s0 s1 σ σ' c htop _ ihE =>
    simp only [Stmt.maxStack] at hmax
    have hi : i < k := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax
    have hmax_rest := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax
    have hmax_E : sE.maxStack < k := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax_rest
    let pE := pc + 1
    let cE := compileStmt sE pE
    let p0 := pE + cE.length + 1
    let c0 := compileStmt s0 p0
    let p1 := p0 + c0.length + 1
    let c1 := compileStmt s1 p1
    let pEnd := p1 + c1.length
    have hsub_all : SubcodeAt code ([.branch i pE p0 p1] ++ (cE ++ ([.jump pEnd] ++ (c0 ++ ([.jump pEnd] ++ c1))))) pc := by
      simpa [compileStmt, pE, cE, p0, c0, p1, c1, pEnd, List.append_assoc] using hsub
    have hsub_br := subcodeAt_append_left hsub_all
    have hsub_r1 := subcodeAt_append_right hsub_all
    have hsub_cE : SubcodeAt code cE pE := subcodeAt_append_left hsub_r1
    have hsub_r2 := subcodeAt_append_right hsub_r1
    have hsub_jE : SubcodeAt code [.jump pEnd] (pE + cE.length) := subcodeAt_append_left hsub_r2
    have hbr := step_branch_single hk code hi σ hsub_br
    rw [htop] at hbr
    rcases ihE hmax_E pE hsub_cE with ⟨stepsE, hleE, hrunE⟩
    have hjump := step_jump_single hk code σ' hsub_jE
    refine ⟨1 + stepsE + 1, by omega, ?_⟩
    rw [(codeTM k hk code).run_add (1 + stepsE) 1,
        (codeTM k hk code).run_add 1 stepsE,
        hbr, hrunE, hjump]
    exact cfgOf_eq (by simp [compileStmt, pE, cE, p0, c0, p1, c1, pEnd]; omega) (fun _ => rfl)
  | @if0 i sE s0 s1 σ σ' c w htop _ ih0 =>
    simp only [Stmt.maxStack] at hmax
    have hi : i < k := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax
    have hmax_rest := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax
    have hmax_rest2 := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax_rest
    have hmax_0 : s0.maxStack < k := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax_rest2
    let pE := pc + 1
    let cE := compileStmt sE pE
    let p0 := pE + cE.length + 1
    let c0 := compileStmt s0 p0
    let p1 := p0 + c0.length + 1
    let c1 := compileStmt s1 p1
    let pEnd := p1 + c1.length
    have hsub_all : SubcodeAt code ([.branch i pE p0 p1] ++ (cE ++ ([.jump pEnd] ++ (c0 ++ ([.jump pEnd] ++ c1))))) pc := by
      simpa [compileStmt, pE, cE, p0, c0, p1, c1, pEnd, List.append_assoc] using hsub
    have hsub_br := subcodeAt_append_left hsub_all
    have hsub_r1 := subcodeAt_append_right hsub_all
    have hsub_r2 := subcodeAt_append_right hsub_r1
    have hsub_r3 := subcodeAt_append_right hsub_r2
    have hsub_c0 : SubcodeAt code c0 p0 := by
      simpa [pE, p0, Nat.add_assoc] using subcodeAt_append_left hsub_r3
    have hsub_r4 := subcodeAt_append_right hsub_r3
    have hsub_j0 : SubcodeAt code [.jump pEnd] (p0 + c0.length) := by
      simpa [pE, p0, Nat.add_assoc] using subcodeAt_append_left hsub_r4
    have hbr := step_branch_single hk code hi σ hsub_br
    rw [htop] at hbr
    rcases ih0 hmax_0 p0 hsub_c0 with ⟨steps0, hle0, hrun0⟩
    have hjump := step_jump_single hk code σ' hsub_j0
    refine ⟨1 + steps0 + 1, by omega, ?_⟩
    rw [(codeTM k hk code).run_add (1 + steps0) 1,
        (codeTM k hk code).run_add 1 steps0,
        hbr, hrun0, hjump]
    exact cfgOf_eq (by simp [compileStmt, pE, cE, p0, c0, p1, c1, pEnd]; omega) (fun _ => rfl)
  | @if1 i sE s0 s1 σ σ' c w htop _ ih1 =>
    simp only [Stmt.maxStack] at hmax
    have hi : i < k := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax
    have hmax_rest := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax
    have hmax_rest2 := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax_rest
    have hmax_1 : s1.maxStack < k := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax_rest2
    let pE := pc + 1
    let cE := compileStmt sE pE
    let p0 := pE + cE.length + 1
    let c0 := compileStmt s0 p0
    let p1 := p0 + c0.length + 1
    let c1 := compileStmt s1 p1
    let pEnd := p1 + c1.length
    have hsub_all : SubcodeAt code ([.branch i pE p0 p1] ++ (cE ++ ([.jump pEnd] ++ (c0 ++ ([.jump pEnd] ++ c1))))) pc := by
      simpa [compileStmt, pE, cE, p0, c0, p1, c1, pEnd, List.append_assoc] using hsub
    have hsub_br := subcodeAt_append_left hsub_all
    have hsub_r1 := subcodeAt_append_right hsub_all
    have hsub_r2 := subcodeAt_append_right hsub_r1
    have hsub_r3 := subcodeAt_append_right hsub_r2
    have hsub_r4 := subcodeAt_append_right hsub_r3
    have hsub_c1 : SubcodeAt code c1 p1 := by
      simpa [pE, p0, p1, Nat.add_assoc] using subcodeAt_append_right hsub_r4
    have hbr := step_branch_single hk code hi σ hsub_br
    rw [htop] at hbr
    rcases ih1 hmax_1 p1 hsub_c1 with ⟨steps1, hle1, hrun1⟩
    refine ⟨1 + steps1, by omega, ?_⟩
    rw [(codeTM k hk code).run_add 1 steps1, hbr, hrun1]
    exact cfgOf_eq (by simp [compileStmt, pE, cE, p0, c0, p1]; omega) (fun _ => rfl)
  | @whileDone i body σ htop =>
    simp only [Stmt.maxStack] at hmax
    have hi : i < k := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax
    let pBody := pc + 1
    let cBody := compileStmt body pBody
    let pEnd := pBody + cBody.length + 1
    have hsub_all : SubcodeAt code ([.branch i pEnd pBody pBody] ++ (cBody ++ [.jump pc])) pc := by
      simpa [compileStmt, pBody, cBody, pEnd, List.append_assoc] using hsub
    have hsub_br := subcodeAt_append_left hsub_all
    have hbr := step_branch_single hk code hi σ hsub_br
    rw [htop] at hbr
    refine ⟨1, by omega, ?_⟩
    rw [hbr]
    exact cfgOf_eq (by simp [compileStmt, pBody, cBody, pEnd]; omega) (fun _ => rfl)
  | @whileStep i body σ σ' σ'' c c' hne _ _ ihbody ihwhile =>
    have hmax_orig : (Stmt.whileNE i body).maxStack < k := hmax
    simp only [Stmt.maxStack] at hmax
    have hi : i < k := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax
    have hmax_body : body.maxStack < k := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax
    let pBody := pc + 1
    let cBody := compileStmt body pBody
    let pEnd := pBody + cBody.length + 1
    have hsub_all : SubcodeAt code ([.branch i pEnd pBody pBody] ++ (cBody ++ [.jump pc])) pc := by
      simpa [compileStmt, pBody, cBody, pEnd, List.append_assoc] using hsub
    have hsub_br := subcodeAt_append_left hsub_all
    have hsub_r1 := subcodeAt_append_right hsub_all
    have hsub_cBody : SubcodeAt code cBody pBody := subcodeAt_append_left hsub_r1
    have hsub_jpc : SubcodeAt code [.jump pc] (pBody + cBody.length) := subcodeAt_append_right hsub_r1
    have hbr := step_branch_single hk code hi σ hsub_br
    have hbr_step : (codeTM k hk code).run 1 (cfgOf k hk code pc σ) =
        cfgOf k hk code pBody σ := by
      cases hσi : σ i with
      | nil => exact absurd hσi hne
      | cons b w =>
        rw [hσi] at hbr
        cases b <;> exact hbr
    rcases ihbody hmax_body pBody hsub_cBody with ⟨stepsB, hleB, hrunB⟩
    have hjump := step_jump_single hk code σ' hsub_jpc
    rcases ihwhile hmax_orig pc hsub with ⟨stepsW, hleW, hrunW⟩
    refine ⟨1 + stepsB + 1 + stepsW, by omega, ?_⟩
    rw [(codeTM k hk code).run_add (1 + stepsB + 1) stepsW,
        (codeTM k hk code).run_add (1 + stepsB) 1,
        (codeTM k hk code).run_add 1 stepsB,
        hbr_step, hrunB, hjump, hrunW]

/-- Top-level `TM` compiled from a `Stmt`. -/
def stmtToTM (s : Stmt) : TM :=
  codeTM (s.maxStack + 1) (Nat.zero_lt_succ _) (compileStmt s 0)

/-- If `s` executes on `initStacks x` with cost `c` and post-state `σ'`, then `stmtToTM s`
    halts on `x` within `2 * c` steps with output `σ' 0`. -/
theorem stmtToTM_haltsWithin (s : Stmt) (x : Word) {c : Nat} {σ' : Stacks}
    (hexec : Exec s (initStacks x) c σ') :
    (stmtToTM s).HaltsWithin x (2 * c) (σ' 0) := by
  let k := s.maxStack + 1
  have hk : 0 < k := Nat.zero_lt_succ _
  let code := compileStmt s 0
  have hmax : s.maxStack < k := Nat.lt_succ_self _
  rcases exec_sim_tm hk code hexec hmax 0 (subcodeAt_self code) with ⟨steps, hle, hrun⟩
  refine ⟨steps, hle, ?_, ?_⟩
  · change (codeTM k hk code).step ((codeTM k hk code).run steps ((codeTM k hk code).init x)) = none
    rw [init_eq_cfgOf k hk code x, hrun]
    have hcfg : cfgOf k hk code (0 + code.length) σ' = cfgOf k hk code code.length σ' :=
      cfgOf_eq (Nat.zero_add _) (fun _ => rfl)
    rw [hcfg]
    exact step_cfgOf_end k hk code σ'
  · change (codeTM k hk code).output ((codeTM k hk code).run steps ((codeTM k hk code).init x)) = σ' 0
    rw [init_eq_cfgOf k hk code x, hrun]
    exact (codeTM k hk code).output_of_inputTape _ (σ' 0) rfl

end FeasibleUnivalence.BC
