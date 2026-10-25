/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/AbelContinuation.lean -/


import Def.NumberTheory.LSeries.AbelContinuation
import Lemma.Nat.LSeries.AbelContinuation
import Theorem.MathlibExtTest.NumberTheory.LSeries.AbelContinuation
/-!
# Tests for the Abel continuation

Zero, one-point finite-support, and alternating examples: each has `O(n ^ 0)`
partial sums, so the continuation is holomorphic on `0 < s.re` and ordered
Dirichlet partial sums converge to it there with no summability assumed.
The alternating example additionally exercises absolute `LSeriesSummable`
at `1 < s.re` and agreement of the continuation with `LSeries` there. Every
`LSeriesSummable` check below is absolute summability; no conditional
convergence is claimed.
-/


namespace AbelContinuationTest

open Filter Asymptotics Topology

/-- The alternating sequence. -/
noncomputable def alt : ℕ → ℂ := fun n => (-1) ^ n

end AbelContinuationTest
