import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBalancedShareVerticalRate
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexTorusArrowPartitionSum_eq_fixedWidthPartitionSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedShareVerticalRate.lean)
-/
@[path]
private lemma sixVertexTorusArrowPartitionSum_eq_fixedWidthPartitionSum_eq
  {T : EvenTorus}
  {c : Real} :
-- imply
  sixVertexTorusArrowPartitionSum T c = sixVertexFixedWidthPartitionSum T.width T.height c := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusArrowPartitionSum_eq_fixedWidthPartitionSum T c

/--
[sixVertexRectangleBalancedShare_eq_traceShare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedShareVerticalRate.lean)
-/
@[path]
private lemma sixVertexRectangleBalancedShare_eq_traceShare_eq
  {T : EvenTorus}
  {c : Real} :
-- imply
  sixVertexRectangleBalancedPartitionSum T.width T.height c / sixVertexRectangleToroidalPartitionSum T.width T.height c = sixVertexBalancedTraceShare T.width T.height c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBalancedShare_eq_traceShare T c

/--
[sixVertexBalancedTraceShare_negLog_div_height_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedShareVerticalRate.lean)
-/
@[path]
private lemma sixVertexBalancedTraceShare_negLog_div_height_tendsto_eq
  {N : Nat}
  {c : Real}
-- given
  (hN : Even N)
  (hc : 0 < c) :
-- imply
  Tendsto (fun M : Nat => -Real.log (sixVertexBalancedTraceShare N M c) / (M : Real)) atTop (nhds (Real.log (sixVertexWidthTopEigenvalue N c) - Real.log (sixVertexLambda N 0 hN (Nat.zero_le _) c))) := by
-- proof
  apply StatMech.FrontierD.sixVertexBalancedTraceShare_negLog_div_height_tendsto N hN hc


-- created on 2026-10-23
