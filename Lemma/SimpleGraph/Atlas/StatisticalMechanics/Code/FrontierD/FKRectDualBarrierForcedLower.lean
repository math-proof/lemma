import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierForcedLower
open StatMech StatMech.FrontierD


/--
[fkRectWindingBlockColumn_forcedAuxiliary_le_dualPullbackSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierForcedLower.lean)
-/
@[path]
private lemma fkRectWindingBlockColumn_forcedAuxiliary_le_dualPullbackSource_eq
  {k scale blocks right : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
  {q a b c : Real}
-- given
  (hright : 1 ≤ right)
  (hproper : right + 1 < (fkRectWindingBlockVerticalFamily k scale blocks).width)
  (hxleft : 1 ≤ x.val)
  (hxright : x.val ≤ right)
  (hq : 1 ≤ q)
  (ha : 0 < a)
  (ha1 : a ≤ 1)
  (hb : 0 < b)
  (hb1 : b ≤ 1)
  (hattachment : c ≤ fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectUnitAttachmentOpenEvent (fkRectWindingBlockVerticalFamily k scale blocks)))
  (hbulk : ∀ xy ∈ fkRectWindingBlockColumnBulkPairs k scale blocks right x hxleft hxright, a ≤ FK.twoPointFun (fkRectInducedGraph (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectColumnBand (fkRectWindingBlockVerticalFamily k scale blocks) 1 right 1 ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1))) (fkRectCriticalP q) q xy.1 xy.2)
  (hconnector : ∀ xy ∈ fkRectWindingBlockColumnConnectorPairs k scale blocks right hright x hxleft hxright, b ≤ FK.twoPointFun (fkRectInducedGraph (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectColumnBand (fkRectWindingBlockVerticalFamily k scale blocks) 1 right 1 ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1))) (fkRectCriticalP q) q xy.1 xy.2) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ (2 * (fkRectWindingBlockVerticalFamily k scale blocks).width) * (c * b ^ 2 * a ^ (blocks + 1)) ≤ fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDualPullbackSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) right (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks))) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockColumn_forcedAuxiliary_le_dualPullbackSource k scale blocks right hright hproper x hxleft hxright hq ha ha1 hb hb1 hattachment hbulk hconnector


-- created on 2026-10-23
