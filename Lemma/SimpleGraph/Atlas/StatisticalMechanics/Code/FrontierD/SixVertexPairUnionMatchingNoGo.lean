import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionMatchingNoGo.Part2
open StatMech StatMech.FrontierD


/--
[sixVertexPairSwitch_eq_target_of_union_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionMatchingNoGo.lean)
-/
@[path]
private lemma sixVertexPairSwitch_eq_target_of_union_eq_eq
  {T : EvenTorus}
  {source target : SixVertexArrows T × SixVertexArrows T}
-- given
  (hhorizontal : sixVertexPairUnionHorizontal source = sixVertexPairUnionHorizontal target)
  (hvertical : sixVertexPairUnionVertical source = sixVertexPairUnionVertical target) :
-- imply
  sixVertexTorusSwitchFirst (sixVertexPairSwitchMaskToTarget source target) source.1 source.2 = target.1 /\ sixVertexTorusSwitchSecond (sixVertexPairSwitchMaskToTarget source target) source.1 source.2 = target.2 := by
-- proof
  apply StatMech.FrontierD.sixVertexPairSwitch_eq_target_of_union_eq source target hhorizontal hvertical

/--
[sixVertexFourByTwo_no_unionEqual_middlePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionMatchingNoGo.lean)
-/
@[path]
private lemma sixVertexFourByTwo_no_unionEqual_middlePair_eq
  {alpha beta : SixVertexArrows sixVertexFourByTwoTorus}
-- given
  (halphaIce : alpha.IceRule)
  (hbetaIce : beta.IceRule)
  (halphaSector : sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus alpha (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1)
  (hhorizontal : sixVertexPairUnionHorizontal (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) = sixVertexPairUnionHorizontal (alpha, beta))
  (hvertical : sixVertexPairUnionVertical (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) = sixVertexPairUnionVertical (alpha, beta)) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_no_unionEqual_middlePair alpha beta halphaIce hbetaIce halphaSector hhorizontal hvertical

/--
[sixVertexFourByTwo_not_completionUnionMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionMatchingNoGo.lean)
-/
@[path]
private lemma sixVertexFourByTwo_not_completionUnionMatching_eq :
-- imply
  ¬ SixVertexHorizontalFineProfileCompletionUnionMatching sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorTwo := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_not_completionUnionMatching


-- created on 2026-10-23
