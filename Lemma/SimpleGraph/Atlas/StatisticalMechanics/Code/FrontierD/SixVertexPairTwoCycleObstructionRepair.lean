import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
open StatMech StatMech.FrontierD


/--
[sixVertexFourByTwoCycleMiddleFirst_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoCycleMiddleFirst_ice_eq :
-- imply
  sixVertexFourByTwoCycleMiddleFirst.IceRule := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCycleMiddleFirst_ice

/--
[sixVertexFourByTwoCycleMiddleSecond_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoCycleMiddleSecond_ice_eq :
-- imply
  sixVertexFourByTwoCycleMiddleSecond.IceRule := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCycleMiddleSecond_ice

/--
[sixVertexFourByTwoCycleMiddleFirst_seamCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoCycleMiddleFirst_seamCount_eq :
-- imply
  sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus sixVertexFourByTwoCycleMiddleFirst (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCycleMiddleFirst_seamCount

/--
[sixVertexFourByTwoCycleMiddleSecond_seamCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoCycleMiddleSecond_seamCount_eq :
-- imply
  sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus sixVertexFourByTwoCycleMiddleSecond (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCycleMiddleSecond_seamCount

/--
[sixVertexFourByTwo_cycleMiddle_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwo_cycleMiddle_related_eq :
-- imply
  sixVertexPairAtMostTwoCycleRelated (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) (sixVertexFourByTwoCycleMiddleFirst, sixVertexFourByTwoCycleMiddleSecond) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_cycleMiddle_related

/--
[sixVertexFourByTwo_cycleMiddle_fineProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwo_cycleMiddle_fineProfile_eq :
-- imply
  sixVertexHorizontalPairBoundedFineRowProfile (sixVertexFourByTwoLowArrows.horizontal, sixVertexFourByTwoHighArrows.horizontal) = sixVertexHorizontalPairBoundedFineRowProfile (sixVertexFourByTwoCycleMiddleFirst.horizontal, sixVertexFourByTwoCycleMiddleSecond.horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_cycleMiddle_fineProfile

/--
[sixVertexFourByTwo_cycleMiddle_fineRelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwo_cycleMiddle_fineRelated_eq :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) (sixVertexFourByTwoCycleMiddleFirst, sixVertexFourByTwoCycleMiddleSecond) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_cycleMiddle_fineRelated

/--
[sixVertexFourByTwo_exists_cycleSupported_middlePair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwo_exists_cycleSupported_middlePair_eq :
-- imply
  exists alpha beta : SixVertexArrows sixVertexFourByTwoTorus, alpha.IceRule /\ beta.IceRule /\ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus alpha (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 /\ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus beta (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 /\ sixVertexPairAtMostTwoCycleFineRelated (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) (alpha, beta) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_exists_cycleSupported_middlePair

/--
[sixVertexFourByTwoExceptional_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoExceptional_valid_eq
  {i : Fin 4} :
-- imply
  (sixVertexFourByTwoExceptionalSourceFirst i).IceRule /\ (sixVertexFourByTwoExceptionalSourceSecond i).IceRule /\ (sixVertexFourByTwoExceptionalTargetFirst i).IceRule /\ (sixVertexFourByTwoExceptionalTargetSecond i).IceRule /\ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus (sixVertexFourByTwoExceptionalSourceFirst i) (svFinLast sixVertexFourByTwoTorus.height_pos)) = 0 /\ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus (sixVertexFourByTwoExceptionalSourceSecond i) (svFinLast sixVertexFourByTwoTorus.height_pos)) = 2 /\ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus (sixVertexFourByTwoExceptionalTargetFirst i) (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 /\ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus (sixVertexFourByTwoExceptionalTargetSecond i) (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoExceptional_valid i

/--
[sixVertexFourByTwoExceptional_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoExceptional_related_eq
  {i : Fin 4} :
-- imply
  sixVertexPairAtMostTwoCycleRelated (sixVertexFourByTwoExceptionalSourceFirst i, sixVertexFourByTwoExceptionalSourceSecond i) (sixVertexFourByTwoExceptionalTargetFirst i, sixVertexFourByTwoExceptionalTargetSecond i) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoExceptional_related i

/--
[sixVertexFourByTwoExceptional_fineProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoExceptional_fineProfile_eq
  {i : Fin 4} :
-- imply
  sixVertexHorizontalPairBoundedFineRowProfile ((sixVertexFourByTwoExceptionalSourceFirst i).horizontal, (sixVertexFourByTwoExceptionalSourceSecond i).horizontal) = sixVertexHorizontalPairBoundedFineRowProfile ((sixVertexFourByTwoExceptionalTargetFirst i).horizontal, (sixVertexFourByTwoExceptionalTargetSecond i).horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoExceptional_fineProfile i

/--
[sixVertexFourByTwoExceptional_fineRelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleObstructionRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoExceptional_fineRelated_eq
  {i : Fin 4} :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated (sixVertexFourByTwoExceptionalSourceFirst i, sixVertexFourByTwoExceptionalSourceSecond i) (sixVertexFourByTwoExceptionalTargetFirst i, sixVertexFourByTwoExceptionalTargetSecond i) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoExceptional_fineRelated i


-- created on 2026-10-23
