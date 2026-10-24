import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisLimit
open StatMech StatMech.FrontierD


/--
[sixVertexCanonicalOddSmoothWallisLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisLimit.lean)
-/
@[path]
private lemma sixVertexCanonicalOddSmoothWallisLimit_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexCanonicalOddSmoothWallisLimit hc s := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddSmoothWallisLimit hc s

/--
[sixVertexCanonicalOddGeneralizedWallisComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisLimit.lean)
-/
@[path]
private lemma sixVertexCanonicalOddGeneralizedWallisComparison_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexCanonicalOddGeneralizedWallisComparison hc s := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddGeneralizedWallisComparison hc s

/--
[sixVertexCanonicalOddZeroModeWallisLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisLimit.lean)
-/
@[path]
private lemma sixVertexCanonicalOddZeroModeWallisLimit_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexCanonicalOddZeroModeWallisLimit hc s := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddZeroModeWallisLimit hc s

/--
[sixVertexCanonicalFixedOddCharge_matchesOffsetFourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisLimit.lean)
-/
@[path]
private lemma sixVertexCanonicalFixedOddCharge_matchesOffsetFourier_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc (2 * s + 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalFixedOddCharge_matchesOffsetFourier hc s

/--
[sixVertexCanonicalFixedCharge_matchesOffsetFourier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisLimit.lean)
-/
@[path]
private lemma sixVertexCanonicalFixedCharge_matchesOffsetFourier_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc r := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalFixedCharge_matchesOffsetFourier hc r

/--
[sixVertexAntiferroelectricTransferConclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisLimit.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricTransferConclusion_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexAntiferroelectricTransferConclusion c (sixVertexAntiferroelectricLambda c) := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricTransferConclusion hc

/--
[sixVertexAntiferroelectricTransferConclusion_of_parameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisLimit.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricTransferConclusion_of_parameter_eq
  {c lam : Real}
-- given
  (hc : 2 < c)
  (hlam : 0 < lam)
  (hcosh : Real.cosh lam = (c ^ 2 - 2) / 2) :
-- imply
  SixVertexAntiferroelectricTransferConclusion c lam := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricTransferConclusion_of_parameter hc hlam hcosh


-- created on 2026-10-23
