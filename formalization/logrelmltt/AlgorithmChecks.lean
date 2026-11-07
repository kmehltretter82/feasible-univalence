import LogrelMLTT

/- Executable smoke tests and verified theorem signature checks for LogrelMLTT. -/
open LogrelMLTT

-- Exhaustion is not a negative answer.
#guard compareTypeUp 0 [] .nat .nat = none
-- Distinct well-formed type constructors.
#guard compareTypeUp 10 [] .nat .univ = some false
#guard compareTypeUp 10 [] .empty .unit = some false
#guard compareTypeUp 10 [] (.pi .nat .nat) (.sigma .nat .nat) = some false
-- Beta reduction at natural-number type.
#guard compareTermUp 20 [] (.app (.lam (.var 0)) .zero) .zero .nat = some true
-- Eta comparison of an open function with its expansion.
#guard compareTermUp 30 [.pi .nat .nat] (.var 0)
  (.lam (.app (.var 1) (.var 0))) (.pi .nat .nat) = some true
-- Sigma beta1 and beta2 reductions.
#guard compareTermUp 20 [] (.fst (.prod .zero (.succ .zero))) .zero .nat = some true
#guard compareTermUp 20 [] (.snd (.prod .zero (.succ .zero))) (.succ .zero) .nat = some true
-- Sigma eta comparison of an open pair with its expansion (fst x, snd x).
#guard compareTermUp 30 [.sigma .nat .nat] (.var 0)
  (.prod (.fst (.var 0)) (.snd (.var 0))) (.sigma .nat .nat) = some true
-- Unit eta comparison of an open term of type Unit with star.
#guard compareTermUp 20 [.unit] (.var 0) .star .unit = some true
-- Emptyrec comparison on a neutral of type Empty.
#guard compareTermUp 20 [.empty] (.emptyrec .nat (.var 0)) (.emptyrec .nat (.var 0)) .nat = some true
-- Distinct naturals.
#guard compareTermUp 10 [] .zero (.succ .zero) .nat = some false
-- Natural recursion computing the identity on the numeral two.
#guard compareTermUp 50 []
  (.natrec .nat .zero (.lam (.lam (.succ (.var 0)))) (.succ (.succ .zero)))
  (.succ (.succ .zero)) .nat = some true
-- Large elimination: a type computed by recursion is compared with Nat.
#guard compareTypeUp 50 []
  (.natrec .univ .nat (.lam (.lam (.var 0))) (.succ (.succ .zero))) .nat = some true
-- Context [x : A, A : U]: x's type shifts to index 1.
#guard lookupType [.var 0, .univ] 0 = some (.var 1)
#guard lookupType [.var 0, .univ] 1 = some .univ
-- Comparison at a neutral type, and agreement of the inferred universe type.
#guard compareTermUp 20 [.var 0, .univ] (.var 0) (.var 0) (.var 1) = some true
#guard compareTypeUp 20 [.univ] (.var 0) (.var 0) = some true
-- Neutral recursor; disagreement of base cases is a definitive negative answer.
#guard compareTermUp 40 [.nat]
  (.natrec .nat .zero (.lam (.lam (.succ (.var 0)))) (.var 0))
  (.natrec .nat (.succ .zero) (.lam (.lam (.succ (.var 0)))) (.var 0)) .nat = some false

-- Fuel-free deciders (`LogrelMLTT.Decider`): no fuel argument, answers certified by
-- `decideTypeEq_iff` / `decideTermEq_iff`.
#guard decideTypeEq (TypeWf.nat CtxWf.nil) (TypeWf.univ CtxWf.nil) = false
#guard decideTypeEq (TypeWf.nat CtxWf.nil) (TypeWf.nat CtxWf.nil) = true
#guard decideTypeEq (TypeWf.empty CtxWf.nil) (TypeWf.unit CtxWf.nil) = false
#guard decideTermEq (HasType.zero CtxWf.nil) (HasType.succ (HasType.zero CtxWf.nil)) = false
#guard decideTermEq (HasType.succ (HasType.zero CtxWf.nil))
  (HasType.succ (HasType.zero CtxWf.nil)) = true
#guard decideTermEq (HasType.star CtxWf.nil) (HasType.star CtxWf.nil) = true

-- Verified milestone and main theorem signatures.
#check @wkTypeWf
#check @wkHasType
#check @wkTypeEq
#check @wkTermEq
#check @valid
#check @fundamentalSubst
#check @syntacticEq
#check @syntacticTerm
#check @syntacticEqTerm
#check @injectivity
#check @sigma_injectivity
#check @whNorm
#check @whNormTerm
#check @canonicity
#check @canonicity_unit
#check @canonicity_unit_red
#check @noEmpty
#check @substitution
#check @zero_ne_one
#check @soundnessConvUp
#check @soundnessConvUpTerm
#check @decConvTypeUp
#check @decConvTermUp
#check @completeEq
#check @completeEqTerm
#check @dec
#check @decTerm
#check @compareTypeUp_decides_typeEq
#check @compareTermUp_decides_termEq
#check @theorem_4_12_computational
#check @decTypeEq
#check @decTermEq
#check @decideTypeEq_iff
#check @decideTermEq_iff
#check @theorem_4_12_decidable
