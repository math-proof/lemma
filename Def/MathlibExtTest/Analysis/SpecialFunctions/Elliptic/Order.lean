/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Elliptic/Order.lean -/


import Def.Analysis.SpecialFunctions.Elliptic.Order
import Lemma.Real.SpecialFunctions.Elliptic.Order
import Theorem.MathlibExtTest.Analysis.SpecialFunctions.Elliptic.Order
open scoped Topology

/-!
# Tests for pole sets and elliptic order

Compile-time examples exercising `PeriodPair.poleMultiplicity`,
`PeriodPair.poleSetInFundamentalParallelogram`,
`PeriodPair.ellipticOrderInFundamentalParallelogram`, and `PeriodPair.ellipticOrder`.
It also contains an honest far-away failure witness: a function with pole
multiplicity one at `0` that is nonmeromorphic on every neighborhood of the
remote point `1`, hence not globally meromorphic.
-/


namespace PeriodPair

open Classical in
/-- A function with a genuine pole at `0` but no global meromorphicity: it agrees
with the inverse pole `z ↦ (z - 0)⁻¹` away from a small ball around the remote
point `1`, and equals complex conjugation on that ball. Unlike a single-point
value change (which preserves `MeromorphicAt` by punctured-locality, see above),
conjugation is nonmeromorphic on every neighborhood of `1`. -/
noncomputable def poleWithConjBranch : ℂ → ℂ := fun z =>
  if z ∈ Metric.ball (1 : ℂ) (1 / 2 : ℝ) then (starRingEnd ℂ) z else (z - 0)⁻¹

end PeriodPair
