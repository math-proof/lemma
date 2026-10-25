import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierBlockLower
open StatMech StatMech.FrontierD


/--
[fkRectWindingBlockColumn_attachment_mul_connector_sq_mul_bulk_pow_le_auxiliary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierBlockLower.lean)
-/
@[path]
private lemma fkRectWindingBlockColumn_attachment_mul_connector_sq_mul_bulk_pow_le_auxiliary_eq
  {k scale blocks right : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
  {q a b c : Real}
-- given
  (hright : 1 <= right)
  (hxleft : 1 <= x.val)
  (hxright : x.val <= right)
  (hq : 1 <= q)
  (ha : 0 < a)
  (ha1 : a <= 1)
  (hb : 0 < b)
  (hb1 : b <= 1)
  (hattachment : c <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectUnitAttachmentOpenEvent (fkRectWindingBlockVerticalFamily k scale blocks)))
  (hbulk : ∀ xy ∈ fkRectWindingBlockColumnBulkPairs k scale blocks right x hxleft hxright, a <= FK.twoPointFun (fkRectInducedGraph (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectColumnBand (fkRectWindingBlockVerticalFamily k scale blocks) 1 right 1 ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1))) (fkRectCriticalP q) q xy.1 xy.2)
  (hconnector : ∀ xy ∈ fkRectWindingBlockColumnConnectorPairs k scale blocks right hright x hxleft hxright, b <= FK.twoPointFun (fkRectInducedGraph (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectColumnBand (fkRectWindingBlockVerticalFamily k scale blocks) 1 right 1 ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1))) (fkRectCriticalP q) q xy.1 xy.2) :
-- imply
  c * b ^ 2 * a ^ (blocks + 1) <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectUnitDualBarrierAuxiliary (fkRectWindingBlockVerticalFamily k scale blocks) right (fkRectWindingBlockColumnAuxiliaryPairs k scale blocks right hright x hxleft hxright)) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockColumn_attachment_mul_connector_sq_mul_bulk_pow_le_auxiliary k scale blocks right hright x hxleft hxright hq ha ha1 hb hb1 hattachment hbulk hconnector


-- created on 2026-10-23
