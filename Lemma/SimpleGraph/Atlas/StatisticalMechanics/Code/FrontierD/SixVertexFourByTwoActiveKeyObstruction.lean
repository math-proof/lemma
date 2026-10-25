import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyObstruction.Part4
open Finset StatMech StatMech.FrontierD


/--
[sixVertexFourByTwoActiveHighMiddle_impossible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveHighMiddle_impossible_eq
-- given
  (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
-- imply
  ¬ ((sixVertexArrowsOfFields sixVertexFourByTwoHighArrows.horizontal vertical).IceRule ∧ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus (sixVertexArrowsOfFields sixVertexFourByTwoHighArrows.horizontal vertical) (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveHighMiddle_impossible vertical

/--
[sixVertexFourByTwoActiveLowCompletion_vertical_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveLowCompletion_vertical_unique_eq
-- given
  (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
-- imply
  (sixVertexArrowsOfFields sixVertexFourByTwoLowArrows.horizontal vertical).IceRule ∧ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus (sixVertexArrowsOfFields sixVertexFourByTwoLowArrows.horizontal vertical) (svFinLast sixVertexFourByTwoTorus.height_pos)) = 0 -> vertical = sixVertexFourByTwoLowArrows.vertical := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveLowCompletion_vertical_unique vertical

/--
[sixVertexFourByTwoActiveHighCompletion_vertical_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveHighCompletion_vertical_unique_eq
-- given
  (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
-- imply
  (sixVertexArrowsOfFields sixVertexFourByTwoHighArrows.horizontal vertical).IceRule ∧ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus (sixVertexArrowsOfFields sixVertexFourByTwoHighArrows.horizontal vertical) (svFinLast sixVertexFourByTwoTorus.height_pos)) = 2 -> vertical = sixVertexFourByTwoHighArrows.vertical := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveHighCompletion_vertical_unique vertical

/--
[sixVertexFourByTwoActiveHighMiddle_isEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveHighMiddle_isEmpty_eq :
-- imply
  IsEmpty (SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoHighArrows.horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveHighMiddle_isEmpty

/--
[sixVertexFourByTwoActiveObstructionProfile_deficit_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionProfile_deficit_pos_eq :
-- imply
  0 < sixVertexHorizontalProfileDeficit sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorOne sixVertexFourByTwoActiveObstructionProfile := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionProfile_deficit_pos

/--
[sixVertexFourByTwoActiveLowCompletion_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveLowCompletion_unique_eq
  {completion : SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero sixVertexFourByTwoLowArrows.horizontal} :
-- imply
  completion = sixVertexFourByTwoActiveLowCompletion := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveLowCompletion_unique completion

/--
[sixVertexFourByTwoActiveHighCompletion_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveHighCompletion_unique_eq
  {completion : SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo sixVertexFourByTwoHighArrows.horizontal} :
-- imply
  completion = sixVertexFourByTwoActiveHighCompletion := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveHighCompletion_unique completion

/--
[sixVertexFourByTwoActiveObstructionCompletionPair_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionCompletionPair_eq_eq :
-- imply
  sixVertexHorizontalActualDeficitCompletionPair sixVertexFourByTwoActiveObstructionToken = (sixVertexFourByTwoActiveLowCompletion, sixVertexFourByTwoActiveHighCompletion) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionCompletionPair_eq

/--
[sixVertexFourByTwoActiveObstructionConfigurationPair_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionConfigurationPair_eq_eq :
-- imply
  (sixVertexHorizontalActualDeficitConfigurationPair sixVertexFourByTwoActiveObstructionToken).1 = (sixVertexFourByTwoLowConfiguration, sixVertexFourByTwoHighConfiguration) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionConfigurationPair_eq

/--
[sixVertexFourByTwoActiveObstructionKey_eq_sourceKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionKey_eq_sourceKey_eq :
-- imply
  sixVertexFourByTwoActiveObstructionKey = sixVertexPairFineUnionKey (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionKey_eq_sourceKey

/--
[sixVertexFourByTwoActiveObstructionKey_cycleRepair_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionKey_cycleRepair_related_eq :
-- imply
  SixVertexPairFineUnionKeyTwoCycleRelated sixVertexFourByTwoActiveObstructionKey sixVertexFourByTwoActiveCycleRepairKey := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionKey_cycleRepair_related

/--
[sixVertexFourByTwoActiveObstructionKey_ne_cycleRepairKey](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionKey_ne_cycleRepairKey_eq :
-- imply
  sixVertexFourByTwoActiveObstructionKey ≠ sixVertexFourByTwoActiveCycleRepairKey := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionKey_ne_cycleRepairKey

/--
[sixVertexFourByTwoActiveObstructionMiddle_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionMiddle_pos_eq :
-- imply
  0 < sixVertexFourByTwoSectorOne.val := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionMiddle_pos

/--
[sixVertexFourByTwoActiveObstructionMiddle_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionMiddle_lt_eq :
-- imply
  sixVertexFourByTwoSectorOne.val < sixVertexFourByTwoTorus.width := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionMiddle_lt

/--
[sixVertexFourByTwoActiveObstructionDeficitCapacity_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionDeficitCapacity_pos_eq :
-- imply
  0 < sixVertexHorizontalActualDeficitFineUnionCapacity sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoActiveObstructionKey := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionDeficitCapacity_pos

/--
[sixVertexFourByTwoActiveObstructionSurplusKeyFiber_isEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionSurplusKeyFiber_isEmpty_eq :
-- imply
  IsEmpty (SixVertexHorizontalActualSurplusFineUnionKeyFiber sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoActiveObstructionKey) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionSurplusKeyFiber_isEmpty

/--
[sixVertexFourByTwo_not_reflexiveActiveFiberEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyObstruction.lean)
-/
@[path]
private lemma sixVertexFourByTwo_not_reflexiveActiveFiberEmbeddings_eq :
-- imply
  ¬ SixVertexHorizontalTwoCycleReflexiveActiveFiberEmbeddings sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_not_reflexiveActiveFiberEmbeddings


-- created on 2026-10-23
