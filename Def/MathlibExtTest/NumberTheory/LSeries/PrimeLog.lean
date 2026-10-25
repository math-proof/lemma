/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/PrimeLog.lean -/


import Def.NumberTheory.LSeries.PrimeLog
import Lemma.Nat.LSeries.PrimeLog
import Theorem.MathlibExtTest.NumberTheory.LSeries.PrimeLog


namespace PrimeLogTest

open scoped LSeries.notation

/-- Shifted continuation `s ↦ g (s + 1)`: smoke test for the N323 interface. -/
noncomputable def shiftedLogDirichletContinuation (s : ℂ) : ℂ :=
  Nat.Primes.logDirichletContinuation (s + 1)

end PrimeLogTest
