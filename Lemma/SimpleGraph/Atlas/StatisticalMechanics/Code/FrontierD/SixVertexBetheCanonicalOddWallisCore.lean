import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisCore
open StatMech StatMech.FrontierD


/--
[tendsto_sixVertexCanonicalOddZeroPrefactorNormalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisCore.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddZeroPrefactorNormalized_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexCanonicalOddZeroPrefactorNormalized hc s) atTop (nhds (c ^ 2 * (2 * Real.pi) * sixVertexFourierPhysicalDensity c hc 0)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddZeroPrefactorNormalized hc s

/--
[sixVertexCanonicalOddZeroPrefactorNormalized_limit_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisCore.lean)
-/
@[path]
private lemma sixVertexCanonicalOddZeroPrefactorNormalized_limit_pos_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  0 < c ^ 2 * (2 * Real.pi) * sixVertexFourierPhysicalDensity c hc 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddZeroPrefactorNormalized_limit_pos hc

/--
[tendsto_log_sixVertexCanonicalOddZeroPrefactorNormalized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisCore.lean)
-/
@[path]
private lemma tendsto_log_sixVertexCanonicalOddZeroPrefactorNormalized_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => Real.log (sixVertexCanonicalOddZeroPrefactorNormalized hc s k)) atTop (nhds (Real.log (c ^ 2 * (2 * Real.pi) * sixVertexFourierPhysicalDensity c hc 0))) := by
-- proof
  apply StatMech.FrontierD.tendsto_log_sixVertexCanonicalOddZeroPrefactorNormalized hc s

/--
[tendsto_sixVertexIdealWallisLogCorrection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisCore.lean)
-/
@[path]
private lemma tendsto_sixVertexIdealWallisLogCorrection_eq :
-- imply
  Tendsto sixVertexIdealWallisLogCorrection atTop (nhds (-Real.log (Real.pi / 2))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexIdealWallisLogCorrection

/--
[sixVertexIdealWallisLogCorrection_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisCore.lean)
-/
@[path]
private lemma sixVertexIdealWallisLogCorrection_eq_sum_eq
  {n : Nat} :
-- imply
  sixVertexIdealWallisLogCorrection n = ∑ j ∈ Finset.range n, Real.log (((2 * (j : Real) + 1) * (2 * j + 3)) / (2 * j + 2) ^ 2) := by
-- proof
  apply StatMech.FrontierD.sixVertexIdealWallisLogCorrection_eq_sum n

/--
[two_sum_midpoint_sub_eq_endpoint_add_secondDifference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisCore.lean)
-/
@[path]
private lemma two_sum_midpoint_sub_eq_endpoint_add_secondDifference_eq
  {n : Nat}
-- given
  (x : Nat -> Real)
  (f : Real -> Real) :
-- imply
  2 * ∑ j ∈ Finset.range n, (f ((x j + x (j + 1)) / 2) - f (x j)) = f (x n) - f (x 0) + ∑ j ∈ Finset.range n, (2 * f ((x j + x (j + 1)) / 2) - f (x j) - f (x (j + 1))) := by
-- proof
  apply StatMech.FrontierD.two_sum_midpoint_sub_eq_endpoint_add_secondDifference n x f


-- created on 2026-10-23
