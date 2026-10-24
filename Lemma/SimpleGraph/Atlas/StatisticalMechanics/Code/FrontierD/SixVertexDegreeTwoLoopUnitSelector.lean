import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoLoopUnitSelector
open StatMech StatMech.FrontierD


/--
[sixVertexHorizontalDegreeTwoLoop_unitSelector_or_highCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoLoopUnitSelector.lean)
-/
@[path]
private lemma sixVertexHorizontalDegreeTwoLoop_unitSelector_or_highCharge_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoLoopHallSource T middle hmiddle_pos hmiddle_lt grade}
-- given
  (hdegree : SixVertexLocallyDegreeTwo source.1.1.1.1 source.1.1.2.1) :
-- imply
  Nonempty (SixVertexHorizontalDegreeTwoLoopUnitSelector source) ∨ sixVertexHorizontalDegreeTwoLoopHighCharge source := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalDegreeTwoLoop_unitSelector_or_highCharge source hdegree

/--
[sixVertexHorizontalDegreeTwoLoopUnitSelector_nonempty_of_not_high](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoLoopUnitSelector.lean)
-/
@[path]
private lemma sixVertexHorizontalDegreeTwoLoopUnitSelector_nonempty_of_not_high_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoLoopHallSource T middle hmiddle_pos hmiddle_lt grade}
-- given
  (hdegree : SixVertexLocallyDegreeTwo source.1.1.1.1 source.1.1.2.1)
  (hnon : ¬ sixVertexHorizontalDegreeTwoLoopHighCharge source) :
-- imply
  Nonempty (SixVertexHorizontalDegreeTwoLoopUnitSelector source) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalDegreeTwoLoopUnitSelector_nonempty_of_not_high source hdegree hnon

/--
[SixVertexHorizontalDegreeTwoLoopUnitSelector.transitionBit_branches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoLoopUnitSelector.lean)
-/
@[path]
private lemma transitionBit_branches_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoLoopHallSource T middle hmiddle_pos hmiddle_lt grade}
  {selector : SixVertexHorizontalDegreeTwoLoopUnitSelector source}
  {dart : SixVertexOrientedDisagreementDart source.1.1.1.1 source.1.1.2.1} :
-- imply
  sixVertexDegreeTwoSynchronizedComponentTransitionBit source.1.1.1.2.1 source.1.1.2.2.1 selector.hdegree selector.component (dart, false) = sixVertexDegreeTwoSynchronizedComponentTransitionBit source.1.1.1.2.1 source.1.1.2.2.1 selector.hdegree selector.component (dart, true) := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopUnitSelector.transitionBit_branches selector dart

/--
[SixVertexHorizontalDegreeTwoLoopUnitSelector.seamSum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoLoopUnitSelector.lean)
-/
@[path]
private lemma seamSum_eq_one_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {grade : Nat × Nat}
  {source : SixVertexHorizontalDegreeTwoLoopHallSource T middle hmiddle_pos hmiddle_lt grade}
  {selector : SixVertexHorizontalDegreeTwoLoopUnitSelector source} :
-- imply
  (∑ dart : SixVertexOrientedDisagreementDart source.1.1.1.1 source.1.1.2.1, if sixVertexDegreeTwoSynchronizedComponentSelector source.1.1.1.2.1 source.1.1.2.2.1 selector.hdegree selector.component dart then sixVertexDegreeTwoStrandStepSeamSign selector.hdegree dart else 0) = 1 := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalDegreeTwoLoopUnitSelector.seamSum_eq_one selector


-- created on 2026-10-23
