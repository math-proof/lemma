import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalLogUnregularizationBridge
open StatMech StatMech.FrontierD


/--
[tendsto_sixVertexCanonicalEvenBulkLogDisplacement_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalLogUnregularizationBridge.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalEvenBulkLogDisplacement_bridge_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexCanonicalEvenBulkLogDisplacement hc s) atTop (nhds ((2 * s : Real) / 2 * (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) - sixVertexAntiferroelectricGapRate (sixVertexAntiferroelectricLambda c)))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalEvenBulkLogDisplacement_bridge hc s


-- created on 2026-10-23
