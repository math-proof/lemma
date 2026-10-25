import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddLogInterface.Part2
open StatMech StatMech.FrontierD


/--
[eventually_sixVertexCanonicalFixedChargeCandidate_odd_eq_density](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddLogInterface.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalFixedChargeCandidate_odd_eq_density_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  (fun k => sixVertexCanonicalFixedChargeBetheCandidateLogRatio hc (2 * s + 1) k) =ᶠ[atTop] sixVertexCanonicalFixedOddDensityCandidateLogRatio hc s := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalFixedChargeCandidate_odd_eq_density hc s

/--
[eventually_sixVertexCanonicalFixedOddDensityCandidate_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddLogInterface.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalFixedOddDensityCandidate_decomposition_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexCanonicalFixedOddDensityCandidateLogRatio hc s k = sixVertexCanonicalOddZeroModeWallisCorrection hc s k + 2 * sixVertexCanonicalOddBulkLogDisplacement hc s k - 2 * sixVertexCanonicalOddBoundaryLogSum hc s k := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalFixedOddDensityCandidate_decomposition hc s

/--
[sixVertexCanonicalFixedOddCharge_matchesOffsetFourier_of_three_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddLogInterface.lean)
-/
@[path]
private lemma sixVertexCanonicalFixedOddCharge_matchesOffsetFourier_of_three_limits_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c)
  (hbulk : Tendsto (sixVertexCanonicalOddBulkLogDisplacement hc s) atTop (nhds (((2 * s + 1 : Nat) : Real) / 2 * (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) - sixVertexAntiferroelectricGapRate (sixVertexAntiferroelectricLambda c)))))
  (hwallis : SixVertexCanonicalOddZeroModeWallisLimit hc s)
  (hboundary : Tendsto (sixVertexCanonicalOddBoundaryLogSum hc s) atTop (nhds ((s + 1 : Nat) * Real.log (Real.cosh (sixVertexAntiferroelectricLambda c))))) :
-- imply
  SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc (2 * s + 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalFixedOddCharge_matchesOffsetFourier_of_three_limits hc s hbulk hwallis hboundary


-- created on 2026-10-23
