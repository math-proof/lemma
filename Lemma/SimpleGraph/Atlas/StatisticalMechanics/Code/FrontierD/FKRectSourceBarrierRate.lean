import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectSourceBarrierRate
open Filter Topology StatMech StatMech.FrontierD


/--
[fkRectCriticalEventMass_auxiliaryChain_ge_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceBarrierRate.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_auxiliaryChain_ge_pow_eq
  {R : FKRectTorus}
  {q a : Real}
  {s : Finset ι}
-- given
  (hq : 1 <= q)
  (ha : 0 <= a)
  (E : ι -> Set R.Configuration)
  (hE : ∀ i ∈ s, IsIncreasing (E i))
  (hlower : ∀ i ∈ s, a <= fkRectCriticalEventMass R q (E i)) :
-- imply
  a ^ s.card <= fkRectCriticalEventMass R q (fkRectFiniteEventIntersection s E) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_auxiliaryChain_ge_pow R hq ha s E hE hlower

/--
[fkRectCriticalEventMass_auxiliaryDecreasingChain_ge_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceBarrierRate.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_auxiliaryDecreasingChain_ge_pow_eq
  {R : FKRectTorus}
  {q a : Real}
  {s : Finset ι}
-- given
  (hq : 1 <= q)
  (ha : 0 <= a)
  (E : ι -> Set R.Configuration)
  (hE : ∀ i ∈ s, IsDecreasing (E i))
  (hlower : ∀ i ∈ s, a <= fkRectCriticalEventMass R q (E i)) :
-- imply
  a ^ s.card <= fkRectCriticalEventMass R q (fkRectFiniteEventIntersection s E) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_auxiliaryDecreasingChain_ge_pow R hq ha s E hE hlower

/--
[fkRectCritical_cFE_pow_width_mul_auxiliary_le_sourceBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceBarrierRate.lean)
-/
@[path]
private lemma fkRectCritical_cFE_pow_width_mul_auxiliary_le_sourceBarrier_eq
  {R : FKRectTorus}
  {leftRight : Nat}
  {q : Real}
  {gap : R.EdgeIndex}
  {A : Set R.Configuration}
-- given
  (hq : 1 <= q)
  (hforce : ∀ omega ∈ A, fkRectForceIndexedPattern R (fkRectHorizontalCutEdges R) (fkRectAllButOneOpenConfiguration R gap) omega ∈ fkRectNoLeftStripCrossingEvent R leftRight) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) * fkRectCriticalEventMass R q A <= fkRectCriticalEventMass R q (fkRectSourceLeftBarrier R leftRight gap) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_pow_width_mul_auxiliary_le_sourceBarrier R leftRight hq gap A hforce

/--
[fkRectCritical_cFE_pow_width_mul_auxiliaryPow_le_sourceBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceBarrierRate.lean)
-/
@[path]
private lemma fkRectCritical_cFE_pow_width_mul_auxiliaryPow_le_sourceBarrier_eq
  {R : FKRectTorus}
  {leftRight blocks : Nat}
  {q a : Real}
  {gap : R.EdgeIndex}
  {A : Set R.Configuration}
-- given
  (hq : 1 <= q)
  (haux : a ^ blocks <= fkRectCriticalEventMass R q A)
  (hforce : ∀ omega ∈ A, fkRectForceIndexedPattern R (fkRectHorizontalCutEdges R) (fkRectAllButOneOpenConfiguration R gap) omega ∈ fkRectNoLeftStripCrossingEvent R leftRight) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) * a ^ blocks <= fkRectCriticalEventMass R q (fkRectSourceLeftBarrier R leftRight gap) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_pow_width_mul_auxiliaryPow_le_sourceBarrier R leftRight blocks hq gap A haux hforce

/--
[fkRectSourceBarrier_negLogRate_le_of_auxiliaryPow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceBarrierRate.lean)
-/
@[path]
private lemma fkRectSourceBarrier_negLogRate_le_of_auxiliaryPow_eq
  {R : FKRectTorus}
  {leftRight blocks : Nat}
  {q a : Real}
  {A : Set R.Configuration}
-- given
  (hone : 1 <= leftRight)
  (hleft : leftRight + 1 < R.width)
  (hq : 1 <= q)
  (ha : 0 < a)
  (haux : a ^ blocks <= fkRectCriticalEventMass R q A)
  (hforce : ∀ omega ∈ A, fkRectForceIndexedPattern R (fkRectHorizontalCutEdges R) (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R)) omega ∈ fkRectNoLeftStripCrossingEvent R leftRight) :
-- imply
  -Real.log (fkRectCriticalEventMass R q (fkRectSourceLeftBarrier R leftRight (fkRectUnitLeftBarrierGap R))) / R.height <= (blocks : Real) * (-Real.log a) / R.height + (2 * R.width : Nat) * (-Real.log (FK.cFE (fkRectCriticalP q) q)) / R.height := by
-- proof
  apply StatMech.FrontierD.fkRectSourceBarrier_negLogRate_le_of_auxiliaryPow R leftRight blocks hone hleft hq ha A haux hforce

/--
[fkRectWindingBlock_sourceBarrier_eventualUpper_of_auxiliary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceBarrierRate.lean)
-/
@[path]
private lemma fkRectWindingBlock_sourceBarrier_eventualUpper_of_auxiliary_eq
  {k scale leftRight : Nat}
  {q a : Real}
  {A : forall blocks, Set (fkRectWindingBlockVerticalFamily k scale blocks).Configuration}
-- given
  (hone : 1 <= leftRight)
  (hleft : leftRight + 1 < 2 * (k + 3))
  (hq : 1 <= q)
  (ha : 0 < a)
  (haux : forall blocks, a ^ (blocks + 1) <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (A blocks))
  (hforce : forall blocks, ∀ omega ∈ A blocks, fkRectForceIndexedPattern (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectHorizontalCutEdges (fkRectWindingBlockVerticalFamily k scale blocks)) (fkRectAllButOneOpenConfiguration (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks))) omega ∈ fkRectNoLeftStripCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) leftRight) :
-- imply
  forall epsilon : Real, 0 < epsilon -> ∀ᶠ blocks in atTop, -Real.log (fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) leftRight (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) / (fkRectWindingBlockVerticalFamily k scale blocks).height <= -Real.log a / (2 * (scale + 1) : Real) + epsilon := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlock_sourceBarrier_eventualUpper_of_auxiliary k scale leftRight hone hleft hq ha A haux hforce

/--
[fkRectWindingBlock_chargeOneRate_le_connectionAndAuxiliary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceBarrierRate.lean)
-/
@[path]
private lemma fkRectWindingBlock_chargeOneRate_le_connectionAndAuxiliary_eq
  {q connectionLower auxiliaryLower : Real}
  {k scale leftRight cut : Nat}
  {x : Fin (2 * (k + 3))}
  {A : forall blocks, Set (fkRectWindingBlockVerticalFamily k scale blocks).Configuration}
-- given
  (hq : 4 < q)
  (hconnectionPos : 0 < connectionLower)
  (hconnectionOne : connectionLower <= 1)
  (hauxiliaryPos : 0 < auxiliaryLower)
  (hone : 1 <= leftRight)
  (hsep : leftRight < cut)
  (hleft : leftRight + 1 < 2 * (k + 3))
  (hx : cut <= x.val)
  (hblock : forall blocks, ∀ xy ∈ connectionPathPairs (blocks + 1) (fkRectWindingBlockPathVertex k scale blocks cut x hx), connectionLower <= FK.twoPointFun (fkRectInducedGraph (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectRightStripBand (fkRectWindingBlockVerticalFamily k scale blocks) cut 1 ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1))) (fkRectCriticalP q) q xy.1 xy.2)
  (haux : forall blocks, auxiliaryLower ^ (blocks + 1) <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (A blocks))
  (hforce : forall blocks, ∀ omega ∈ A blocks, fkRectForceIndexedPattern (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectHorizontalCutEdges (fkRectWindingBlockVerticalFamily k scale blocks)) (fkRectAllButOneOpenConfiguration (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks))) omega ∈ fkRectNoLeftStripCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) leftRight) :
-- imply
  -sixVertexFixedChargeLogRatio (fkQgt4SixVertexWeight q) 1 (k + 1) <= -Real.log connectionLower / (2 * (scale + 1) : Real) + -Real.log auxiliaryLower / (2 * (scale + 1) : Real) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlock_chargeOneRate_le_connectionAndAuxiliary hq hconnectionPos hconnectionOne hauxiliaryPos k scale leftRight cut hone hsep hleft x hx hblock A haux hforce


-- created on 2026-10-23
