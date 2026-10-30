import Abel2018.Algorithm

/- Executable smoke tests only. These do not prove conversion correctness. -/
open Abel2018

-- Exhaustion is not a negative answer.
#guard compareTypeUp 0 [] .nat .nat = none
-- Distinct well-formed type constructors.
#guard compareTypeUp 10 [] .nat .univ = some false
-- Beta reduction at natural-number type.
#guard compareTermUp 20 [] (.app (.lam (.var 0)) .zero) .zero .nat = some true
-- Eta comparison of an open function with its expansion.
#guard compareTermUp 30 [.pi .nat .nat] (.var 0)
  (.lam (.app (.var 1) (.var 0))) (.pi .nat .nat) = some true
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
