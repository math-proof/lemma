import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyComponentRouting.Part2
open StatMech StatMech.FrontierD


/--
[activeKeyFiberRoutings_of_componentRoutings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyComponentRouting.lean)
-/
@[path]
private lemma activeKeyFiberRoutings_of_componentRoutings_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hroutings : SixVertexHorizontalTwoCycleActiveKeyComponentRoutings T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalTwoCycleActiveKeyFiberRoutings T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.activeKeyFiberRoutings_of_componentRoutings T middle hmiddle_pos hmiddle_lt hroutings

/--
[twoCycleKeyCapacityHall_of_activeKeyComponentRoutings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyComponentRouting.lean)
-/
@[path]
private lemma twoCycleKeyCapacityHall_of_activeKeyComponentRoutings_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hroutings : SixVertexHorizontalTwoCycleActiveKeyComponentRoutings T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalTwoCycleKeyCapacityHall T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.twoCycleKeyCapacityHall_of_activeKeyComponentRoutings T middle hmiddle_pos hmiddle_lt hroutings

/--
[offDiagonalTwoCycleMatching_of_tokenComponentRoutings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyComponentRouting.lean)
-/
@[path]
private lemma offDiagonalTwoCycleMatching_of_tokenComponentRoutings_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hroutings : SixVertexHorizontalTwoCycleTokenComponentRoutings T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexHorizontalOffDiagonalTwoCycleMatching T middle hmiddle_pos hmiddle_lt := by
-- proof
  apply StatMech.FrontierD.offDiagonalTwoCycleMatching_of_tokenComponentRoutings T middle hmiddle_pos hmiddle_lt hroutings

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_tokenComponentRoutings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyComponentRouting.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_tokenComponentRoutings_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hroutings : SixVertexHorizontalTwoCycleTokenComponentRoutings T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_tokenComponentRoutings T middle hmiddle_pos hmiddle_lt hroutings


-- created on 2026-10-23
