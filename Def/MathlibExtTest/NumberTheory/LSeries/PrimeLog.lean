/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/PrimeLog.lean -/

module

public import Def.NumberTheory.LSeries.PrimeLog
public import Theorem.Nat.LSeries.PrimeLog
public import Theorem.MathlibExtTest.NumberTheory.LSeries.PrimeLog

@[expose] public section

namespace PrimeLogTest

open scoped LSeries.notation

/-- Shifted continuation `s ↦ g (s + 1)`: smoke test for the N323 interface. -/
noncomputable def shiftedLogDirichletContinuation (s : ℂ) : ℂ :=
  Nat.Primes.logDirichletContinuation (s + 1)

end PrimeLogTest
