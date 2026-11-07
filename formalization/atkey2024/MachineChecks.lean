import Atkey2024

/- Executable smoke tests, theorem signatures, and axiom audit for M4.0. -/
open Atkey2024

-- The unary input 5 is traversed in 3 * 5 + 6 = 21 steps, matching `countdown_cost`.
#guard (run 100 countdown (.snoc .nil (natValue 5))).map Prod.fst == some 21
#guard (run 100 countdown (.snoc .nil (natValue 0))).map Prod.fst == some 6
#guard (run 1000 countdown (.snoc .nil (natValue 100))).map Prod.fst == some 306
-- Running out of fuel is not a result.
#guard (run 1 countdown (.snoc .nil (natValue 5))).isNone
-- Applying a non-closure is stuck rather than an error value.
#guard (run 10 (.app 0 0 : Expr 1) (.snoc .nil .unit)).isNone
-- `seq` charges k₁ + 1 + k₂: two unit constructions cost 1 + 1 + 1.
#guard (run 10 (.seq .unit .unit : Expr 0) .nil).map Prod.fst == some 3
-- `letpair` binds the second component at index 0 and the first at index 1.
#guard match run 10 (.letpair 0 (.var 1) : Expr 1) (.snoc .nil (.pair .true .false)) with
  | some (2, .true) => true
  | _ => false
-- `cond` takes the branch selected by the boolean at the given index.
#guard match run 10 (.cond 0 .unit .false : Expr 1) (.snoc .nil .false) with
  | some (2, .false) => true
  | _ => false

-- Verified M4.0 signatures.
#check @lookup_iff_get
#check @Eval.deterministic
#check @run_sound
#check @run_complete
#check @eval_iff_run
#check @countdown_cost

#print axioms lookup_iff_get
#print axioms Eval.deterministic
#print axioms run_sound
#print axioms run_complete
#print axioms eval_iff_run
#print axioms countdown_cost
