import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectIndexedPatternPushforward
open Finset StatMech StatMech.FrontierD


/--
[fkRectForceIndexedPattern_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectIndexedPatternPushforward.lean)
-/
@[path]
private lemma fkRectForceIndexedPattern_of_mem_eq
  {R : FKRectTorus}
  {I : Finset R.EdgeIndex}
  {eta omega : R.Configuration}
  {a : R.EdgeIndex}
-- given
  (ha : a ∈ I) :
-- imply
  fkRectForceIndexedPattern R I eta omega a = eta a := by
-- proof
  apply StatMech.FrontierD.fkRectForceIndexedPattern_of_mem R eta omega ha

/--
[fkRectForceIndexedPattern_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectIndexedPatternPushforward.lean)
-/
@[path]
private lemma fkRectForceIndexedPattern_of_not_mem_eq
  {R : FKRectTorus}
  {I : Finset R.EdgeIndex}
  {eta omega : R.Configuration}
  {a : R.EdgeIndex}
-- given
  (ha : a ∉ I) :
-- imply
  fkRectForceIndexedPattern R I eta omega a = omega a := by
-- proof
  apply StatMech.FrontierD.fkRectForceIndexedPattern_of_not_mem R eta omega ha

/--
[fkRectPatternOpenEdges_card_add_closedEdges_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectIndexedPatternPushforward.lean)
-/
@[path]
private lemma fkRectPatternOpenEdges_card_add_closedEdges_card_eq
  {R : FKRectTorus}
  {I : Finset R.EdgeIndex}
  {eta : R.Configuration} :
-- imply
  (fkRectPatternOpenEdges R I eta).card + (fkRectPatternClosedEdges R I eta).card = I.card := by
-- proof
  apply StatMech.FrontierD.fkRectPatternOpenEdges_card_add_closedEdges_card R I eta

/--
[fkRectCritical_cFE_pow_mul_forceIndexedPattern_preimage_le_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectIndexedPatternPushforward.lean)
-/
@[path]
private lemma fkRectCritical_cFE_pow_mul_forceIndexedPattern_preimage_le_event_eq
  {R : FKRectTorus}
  {q : Real}
  {I : Finset R.EdgeIndex}
  {eta : R.Configuration}
  {A : Set R.Configuration}
-- given
  (hq : 1 ≤ q) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ I.card * fkRectCriticalEventMass R q (fkRectForceIndexedPattern R I eta ⁻¹' A) ≤ fkRectCriticalEventMass R q A := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_pow_mul_forceIndexedPattern_preimage_le_event R hq I eta A

/--
[fkRectCritical_cFE_pow_mul_event_le_indexedPattern_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectIndexedPatternPushforward.lean)
-/
@[path]
private lemma fkRectCritical_cFE_pow_mul_event_le_indexedPattern_inter_eq
  {R : FKRectTorus}
  {q : Real}
  {I : Finset R.EdgeIndex}
  {eta : R.Configuration}
  {B : Set R.Configuration}
-- given
  (hq : 1 ≤ q)
  (hB : FKRectDependsOnOutsideEdges R I B) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ I.card * fkRectCriticalEventMass R q B ≤ fkRectCriticalEventMass R q (fkRectIndexedPatternEvent R I eta ∩ B) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_pow_mul_event_le_indexedPattern_inter R hq I eta B hB


-- created on 2026-10-23
