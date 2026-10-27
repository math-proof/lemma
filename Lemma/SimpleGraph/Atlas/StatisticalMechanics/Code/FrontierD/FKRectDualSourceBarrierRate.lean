import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierRate
open Filter Topology StatMech StatMech.FrontierD


/--
[fkRectDualEvent_pullbackSourceLeftBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualSourceBarrierRate.lean)
-/
@[path]
private lemma fkRectDualEvent_pullbackSourceLeftBarrier_eq
  {R : FKRectTorus}
  {leftRight : Nat}
  {gap : R.EdgeIndex} :
-- imply
  fkRectDualEvent R (fkRectDualPullbackSourceLeftBarrier R leftRight gap) = fkRectSourceLeftBarrier R leftRight gap := by
-- proof
  apply StatMech.FrontierD.fkRectDualEvent_pullbackSourceLeftBarrier R leftRight gap

/--
[one_div_q_mul_dualPullbackSourceMass_le_sourceBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualSourceBarrierRate.lean)
-/
@[path]
private lemma one_div_q_mul_dualPullbackSourceMass_le_sourceBarrier_eq
  {R : FKRectTorus}
  {leftRight : Nat}
  {q : Real}
  {gap : R.EdgeIndex}
-- given
  (hq : 1 <= q) :
-- imply
  (1 / q) * fkRectCriticalEventMass R q (fkRectDualPullbackSourceLeftBarrier R leftRight gap) <= fkRectCriticalEventMass R q (fkRectSourceLeftBarrier R leftRight gap) := by
-- proof
  apply StatMech.FrontierD.one_div_q_mul_dualPullbackSourceMass_le_sourceBarrier R leftRight hq gap

/--
[fkRectSourceBarrier_negLogRate_le_of_dualPullback_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualSourceBarrierRate.lean)
-/
@[path]
private lemma fkRectSourceBarrier_negLogRate_le_of_dualPullback_mul_pow_eq
  {R : FKRectTorus}
  {leftRight blocks : Nat}
  {q C a : Real}
-- given
  (hone : 1 <= leftRight)
  (hleft : leftRight + 1 < R.width)
  (hq : 1 <= q)
  (hC : 0 < C)
  (ha : 0 < a)
  (haux : C * a ^ blocks <= fkRectCriticalEventMass R q (fkRectDualPullbackSourceLeftBarrier R leftRight (fkRectUnitLeftBarrierGap R))) :
-- imply
  -Real.log (fkRectCriticalEventMass R q (fkRectSourceLeftBarrier R leftRight (fkRectUnitLeftBarrierGap R))) / R.height <= (blocks : Real) * (-Real.log a) / R.height + (-Real.log ((1 / q) * C)) / R.height := by
-- proof
  apply StatMech.FrontierD.fkRectSourceBarrier_negLogRate_le_of_dualPullback_mul_pow R leftRight blocks hone hleft hq hC ha haux

/--
[fkRectSourceBarrier_negLogRate_le_of_dualPullbackPow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualSourceBarrierRate.lean)
-/
@[path]
private lemma fkRectSourceBarrier_negLogRate_le_of_dualPullbackPow_eq
  {R : FKRectTorus}
  {leftRight blocks : Nat}
  {q a : Real}
-- given
  (hone : 1 <= leftRight)
  (hleft : leftRight + 1 < R.width)
  (hq : 1 <= q)
  (ha : 0 < a)
  (haux : a ^ blocks <= fkRectCriticalEventMass R q (fkRectDualPullbackSourceLeftBarrier R leftRight (fkRectUnitLeftBarrierGap R))) :
-- imply
  -Real.log (fkRectCriticalEventMass R q (fkRectSourceLeftBarrier R leftRight (fkRectUnitLeftBarrierGap R))) / R.height <= (blocks : Real) * (-Real.log a) / R.height + (-Real.log (1 / q)) / R.height := by
-- proof
  apply StatMech.FrontierD.fkRectSourceBarrier_negLogRate_le_of_dualPullbackPow R leftRight blocks hone hleft hq ha haux

/--
[fkRectWindingBlock_sourceBarrier_eventualUpper_of_dualPullback_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualSourceBarrierRate.lean)
-/
@[path]
private lemma fkRectWindingBlock_sourceBarrier_eventualUpper_of_dualPullback_mul_pow_eq
  {k scale leftRight : Nat}
  {q C a : Real}
-- given
  (hone : 1 <= leftRight)
  (hleft : leftRight + 1 < 2 * (k + 3))
  (hq : 1 <= q)
  (hC : 0 < C)
  (ha : 0 < a)
  (haux : forall blocks, C * a ^ (blocks + 1) <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDualPullbackSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) leftRight (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) :
-- imply
  forall epsilon : Real, 0 < epsilon -> ∀ᶠ blocks in atTop, -Real.log (fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) leftRight (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) / (fkRectWindingBlockVerticalFamily k scale blocks).height <= -Real.log a / (2 * (scale + 1) : Real) + epsilon := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlock_sourceBarrier_eventualUpper_of_dualPullback_mul_pow k scale leftRight hone hleft hq hC ha haux

/--
[fkRectWindingBlock_sourceBarrier_eventualUpper_of_dualPullback](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualSourceBarrierRate.lean)
-/
@[path]
private lemma fkRectWindingBlock_sourceBarrier_eventualUpper_of_dualPullback_eq
  {k scale leftRight : Nat}
  {q a : Real}
-- given
  (hone : 1 <= leftRight)
  (hleft : leftRight + 1 < 2 * (k + 3))
  (hq : 1 <= q)
  (ha : 0 < a)
  (haux : forall blocks, a ^ (blocks + 1) <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDualPullbackSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) leftRight (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) :
-- imply
  forall epsilon : Real, 0 < epsilon -> ∀ᶠ blocks in atTop, -Real.log (fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) leftRight (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) / (fkRectWindingBlockVerticalFamily k scale blocks).height <= -Real.log a / (2 * (scale + 1) : Real) + epsilon := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlock_sourceBarrier_eventualUpper_of_dualPullback k scale leftRight hone hleft hq ha haux


-- created on 2026-10-23
