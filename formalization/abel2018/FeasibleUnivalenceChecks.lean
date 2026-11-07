/-
  FeasibleUnivalenceChecks.lean

  Executable `#guard` regression tests and `#print axioms` footprint checks across
  M1, M2, M3, Paper A, Paper B, Paper C, and the Final Feasible Univalence Synthesis.
-/

import FeasibleUnivalence

open Abel2018
open FeasibleUnivalence
open FeasibleUnivalence.PaperB
open FeasibleUnivalence.PaperC
open FeasibleUnivalence.Synthesis

/-! ## 1. Executable `#guard` Regression Checks -/

-- Paper A: Target closure machine compilation of `foldCapturingClosureTerm`
#guard erase ErasureGrade.erasureModality false .nonStrict
    (foldCapturingClosureTerm ErasureGrade ErasureGrade.erasureModality) ==
  .app .nonStrict
    (.lam
      (.natrec false .nonStrict true false
        (.lam (.var 2))
        (.lam (.lam (.lam (.app .nonStrict (.var 1) (.var 0)))))
        (.succ .zero)))
    .undef

-- Paper B: Static polynomial certificate synthesis and operational evaluation
#guard (synthSizePoly copyWordProg).eval 5 == 5
#guard (synthTimePoly copyWordProg).eval 5 == 7
#guard (synthSizePoly composedTraversalsProg).eval 5 == 5
#guard (synthTimePoly composedTraversalsProg).eval 5 == 15
#guard (evalProg copyWordProg [true, false, true]).output == [true, false, true]
#guard (evalProg copyWordProg [true, false, true]).steps == 5
#guard (evalProg negateWordProg [true, false, true]).output == [false, true, false]
#guard (evalProg .dupIter [true, false, true, true]).output.length == 16

-- Paper C: Finite-map representation transfer & distinct cost profiles
#guard batchLookup listMapImpl (buildMap listMapImpl [(1, 10), (3, 30), (2, 20)]) [1, 2, 3, 4] ==
  [some 10, some 20, some 30, none]
#guard batchLookup treeMapImpl (buildMap treeMapImpl [(1, 10), (3, 30), (2, 20)]) [1, 2, 3, 4] ==
  [some 10, some 20, some 30, none]
#guard listMapImpl.lookupCost 0 (buildMap listMapImpl [(1, 10), (3, 30), (2, 20)]) == 4
#guard treeMapImpl.lookupCost 0 (buildMap treeMapImpl [(1, 10), (3, 30), (2, 20)]) == 3

/-! ## 2. Axiom Footprint Verification (`[propext]` / `[Quot.sound]` Only — Zero `Classical.choice`, Zero `sorry`) -/

-- M1: Conversion Decidability
#print axioms Abel2018.theorem_4_12_computational

-- M2: Graded Usage & Syntactic Erasure
#print axioms FeasibleUnivalence.Usage.substₘ_lemma
#print axioms FeasibleUnivalence.Usage.usagePresTerm
#print axioms FeasibleUnivalence.Usage.erased_not_hasX
#print axioms FeasibleUnivalence.fundamental
#print axioms FeasibleUnivalence.soundness_nat_canonical

-- M3: Graded Heap Machine & Non-Interference
#print axioms FeasibleUnivalence.usage_pres_step
#print axioms FeasibleUnivalence.numStep_not_pres_usage
#print axioms FeasibleUnivalence.usage_pres_numStar_empty
#print axioms FeasibleUnivalence.tracked_to_untracked_star
#print axioms FeasibleUnivalence.untracked_to_tracked_star
#print axioms FeasibleUnivalence.unfold_heapStar
#print axioms FeasibleUnivalence.unfold_heapNumStar
#print axioms FeasibleUnivalence.initial_eval_numeral_sound
#print axioms FeasibleUnivalence.SecurityLevel.non_interference

-- Paper A (Gates G2 & G3): Resource-Aware Extraction & Closure Machine
#print axioms FeasibleUnivalence.erased_slot_never_accessed
#print axioms FeasibleUnivalence.erased_heap_lockstep_sim
#print axioms FeasibleUnivalence.returned_closure_captures_budget
#print axioms FeasibleUnivalence.paper_A_resource_correctness_after_erasure
#print axioms FeasibleUnivalence.fold_capturing_closure_example
#print axioms FeasibleUnivalence.cbv_erased_eval_counterexample
#print axioms FeasibleUnivalence.affine_duplication_counterexample
#print axioms FeasibleUnivalence.linear_discard_counterexample

-- Bellantoni–Cook Library (`FeasibleUnivalence.BC`): Soundness, Completeness, & FP Equivalence
#print axioms FeasibleUnivalence.BC.Fn.eval_length_le_sizePoly
#print axioms FeasibleUnivalence.BC.bc_soundness
#print axioms FeasibleUnivalence.BC.bc_completeness
#print axioms FeasibleUnivalence.BC.defFun_eq_FP

-- Paper B (Gate G4): Feasible Dependent Types without Equality Reflection
#print axioms FeasibleUnivalence.PaperB.comp_certificate_formula
#print axioms FeasibleUnivalence.PaperB.paper_B_polytime_soundness
#print axioms FeasibleUnivalence.PaperB.paper_B_tm_soundness
#print axioms FeasibleUnivalence.PaperB.paper_B_intensional_idJ_soundness
#print axioms FeasibleUnivalence.PaperB.paper_B_FP_completeness
#print axioms FeasibleUnivalence.PaperB.paper_B_defFun_eq_FP
#print axioms FeasibleUnivalence.PaperB.two_traversals_and_composition_cert
#print axioms FeasibleUnivalence.PaperB.dependent_iterator_with_idJ_example
#print axioms FeasibleUnivalence.PaperB.exponential_duplication_counterexample
#print axioms FeasibleUnivalence.PaperB.erased_clock_counterexample

-- Paper C (Gate G5): The Cost of Transport & Representation Transfer
#print axioms FeasibleUnivalence.PaperC.transport_obstruction_xor
#print axioms FeasibleUnivalence.PaperC.cubical_certs_substDim_eq
#print axioms FeasibleUnivalence.PaperC.paper_C_quantitative_transport_soundness
#print axioms FeasibleUnivalence.PaperC.vType_transport_simulation
#print axioms FeasibleUnivalence.PaperC.erased_equiv_cannot_execute_at_runtime
#print axioms FeasibleUnivalence.PaperC.hcomp_linear_duplication_rejected
#print axioms FeasibleUnivalence.PaperC.zero_cost_cast_fallacy
#print axioms FeasibleUnivalence.PaperC.ListMap.listMap_abstraction_not_injective
#print axioms FeasibleUnivalence.PaperC.finMap_client_transfer_theorem
#print axioms FeasibleUnivalence.PaperC.bst_invariant_violation_and_cost_separation

-- Final Synthesis (Gate G6): Quantitative Gluing & Main Feasible Univalence Theorem
#print axioms FeasibleUnivalence.Synthesis.feasible_univalence_fundamental
#print axioms FeasibleUnivalence.Synthesis.pi_sigma_quantitative_extraction
#print axioms FeasibleUnivalence.Synthesis.normalization_vs_runtime_cost_separation
#print axioms FeasibleUnivalence.Synthesis.feasible_univalence_main_theorem
