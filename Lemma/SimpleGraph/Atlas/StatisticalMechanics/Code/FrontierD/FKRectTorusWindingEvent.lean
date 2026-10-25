import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part3
open StatMech StatMech.FrontierD


/--
[fkRectOpenAdjacencyEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingEvent.lean)
-/
@[path]
private lemma fkRectOpenAdjacencyEvent_isIncreasing_eq
  {R : FKRectTorus}
  {x y : R.Vertex} :
-- imply
  IsIncreasing (fkRectOpenAdjacencyEvent R x y) := by
-- proof
  apply StatMech.FrontierD.fkRectOpenAdjacencyEvent_isIncreasing R x y

/--
[fkRectVerticalCutGraph_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingEvent.lean)
-/
@[path]
private lemma fkRectVerticalCutGraph_mono_eq
  {R : FKRectTorus}
  {omega tau : R.Configuration}
-- given
  (hot : omega ≤ tau) :
-- imply
  fkRectVerticalCutGraph R omega ≤ fkRectVerticalCutGraph R tau := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalCutGraph_mono R hot

/--
[fkRectVerticalCutGraph_le_openGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingEvent.lean)
-/
@[path]
private lemma fkRectVerticalCutGraph_le_openGraph_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectVerticalCutGraph R omega ≤ fkRectOpenGraph R omega := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalCutGraph_le_openGraph R omega

/--
[fkRectVerticalSeamIncrement_eq_zero_of_not_crosses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingEvent.lean)
-/
@[path]
private lemma fkRectVerticalSeamIncrement_eq_zero_of_not_crosses_eq
  {R : FKRectTorus}
  {x y : R.Vertex}
-- given
  (hnot : ¬ fkRectCrossesVerticalSeam R s(x, y)) :
-- imply
  fkRectVerticalSeamIncrement R x y = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalSeamIncrement_eq_zero_of_not_crosses R x y hnot

/--
[fkRectVerticalSeamIncrement_ne_zero_of_crosses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingEvent.lean)
-/
@[path]
private lemma fkRectVerticalSeamIncrement_ne_zero_of_crosses_eq
  {R : FKRectTorus}
  {x y : R.Vertex}
-- given
  (hcross : fkRectCrossesVerticalSeam R s(x, y)) :
-- imply
  fkRectVerticalSeamIncrement R x y ≠ 0 := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalSeamIncrement_ne_zero_of_crosses R x y hcross

/--
[fkRectVerticalCutWalk_winding_snd_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingEvent.lean)
-/
@[path]
private lemma fkRectVerticalCutWalk_winding_snd_eq_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
  {p : (fkRectVerticalCutGraph R omega).Walk x y} :
-- imply
  (fkRectWalkWinding R p).2 = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalCutWalk_winding_snd_eq_zero R omega p

/--
[FKRectVerticalWindingWitness.exists_closedWalk_winding_snd_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingEvent.lean)
-/
@[path]
private lemma exists_closedWalk_winding_snd_ne_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
-- given
  (h : FKRectVerticalWindingWitness R omega x y) :
-- imply
  ∃ p : (fkRectOpenGraph R omega).Walk x x, (fkRectWalkWinding R p).2 ≠ 0 := by
-- proof
  apply StatMech.FrontierD.FKRectVerticalWindingWitness.exists_closedWalk_winding_snd_ne_zero R omega x y h

/--
[fkRectVerticalCutConnectionEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingEvent.lean)
-/
@[path]
private lemma fkRectVerticalCutConnectionEvent_isIncreasing_eq
  {R : FKRectTorus}
  {x y : R.Vertex} :
-- imply
  IsIncreasing (fkRectVerticalCutConnectionEvent R x y) := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalCutConnectionEvent_isIncreasing R x y

/--
[fkRectVerticalCutConnection_inter_subset_connection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingEvent.lean)
-/
@[path]
private lemma fkRectVerticalCutConnection_inter_subset_connection_eq
  {R : FKRectTorus}
  {x y z : R.Vertex} :
-- imply
  fkRectVerticalCutConnectionEvent R x y ∩ fkRectVerticalCutConnectionEvent R y z ⊆ fkRectVerticalCutConnectionEvent R x z := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalCutConnection_inter_subset_connection R x y z

/--
[fkRectCriticalVerticalCutConnectionMass_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingEvent.lean)
-/
@[path]
private lemma fkRectCriticalVerticalCutConnectionMass_mul_le_eq
  {R : FKRectTorus}
  {q : Real}
  {x y z : R.Vertex}
-- given
  (hq : 1 ≤ q) :
-- imply
  fkRectCriticalEventMass R q (fkRectVerticalCutConnectionEvent R x y) * fkRectCriticalEventMass R q (fkRectVerticalCutConnectionEvent R y z) ≤ fkRectCriticalEventMass R q (fkRectVerticalCutConnectionEvent R x z) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalVerticalCutConnectionMass_mul_le R hq x y z

/--
[fkRectVerticalWindingEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingEvent.lean)
-/
@[path]
private lemma fkRectVerticalWindingEvent_isIncreasing_eq
  {R : FKRectTorus} :
-- imply
  IsIncreasing (fkRectVerticalWindingEvent R) := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalWindingEvent_isIncreasing R

/--
[fkRectOpenAdjacency_inter_verticalCutConnection_subset_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingEvent.lean)
-/
@[path]
private lemma fkRectOpenAdjacency_inter_verticalCutConnection_subset_winding_eq
  {R : FKRectTorus}
  {x y : R.Vertex}
-- given
  (hseam : fkRectCrossesVerticalSeam R s(x, y)) :
-- imply
  fkRectOpenAdjacencyEvent R x y ∩ fkRectVerticalCutConnectionEvent R x y ⊆ fkRectVerticalWindingEvent R := by
-- proof
  apply StatMech.FrontierD.fkRectOpenAdjacency_inter_verticalCutConnection_subset_winding R x y hseam

/--
[fkRectCriticalVerticalWindingMass_ge_fixedWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingEvent.lean)
-/
@[path]
private lemma fkRectCriticalVerticalWindingMass_ge_fixedWitness_eq
  {R : FKRectTorus}
  {q : Real}
  {x y : R.Vertex}
-- given
  (hq : 1 ≤ q)
  (hseam : fkRectCrossesVerticalSeam R s(x, y)) :
-- imply
  fkRectCriticalEventMass R q (fkRectOpenAdjacencyEvent R x y) * fkRectCriticalEventMass R q (fkRectVerticalCutConnectionEvent R x y) ≤ fkRectCriticalEventMass R q (fkRectVerticalWindingEvent R) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalVerticalWindingMass_ge_fixedWitness R hq x y hseam


-- created on 2026-10-23
