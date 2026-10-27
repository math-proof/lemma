import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyRepair.Part6
open StatMech StatMech.FrontierD


/--
[sixVertexFourByTwoActiveCycleMiddleFirstLower_impossible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveCycleMiddleFirstLower_impossible_eq
-- given
  (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
-- imply
  ¬ ((sixVertexArrowsOfFields sixVertexFourByTwoCycleMiddleFirst.horizontal vertical).IceRule ∧ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus (sixVertexArrowsOfFields sixVertexFourByTwoCycleMiddleFirst.horizontal vertical) (svFinLast sixVertexFourByTwoTorus.height_pos)) = 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveCycleMiddleFirstLower_impossible vertical

/--
[sixVertexFourByTwoActiveCycleMiddleFirst_vertical_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveCycleMiddleFirst_vertical_unique_eq
-- given
  (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
-- imply
  (sixVertexArrowsOfFields sixVertexFourByTwoCycleMiddleFirst.horizontal vertical).IceRule ∧ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus (sixVertexArrowsOfFields sixVertexFourByTwoCycleMiddleFirst.horizontal vertical) (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 -> vertical = sixVertexFourByTwoCycleMiddleFirst.vertical := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveCycleMiddleFirst_vertical_unique vertical

/--
[sixVertexFourByTwoActiveCycleMiddleSecond_vertical_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveCycleMiddleSecond_vertical_unique_eq
-- given
  (vertical : sixVertexFourByTwoTorus.Vertex -> Bool) :
-- imply
  (sixVertexArrowsOfFields sixVertexFourByTwoCycleMiddleSecond.horizontal vertical).IceRule ∧ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus (sixVertexArrowsOfFields sixVertexFourByTwoCycleMiddleSecond.horizontal vertical) (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 -> vertical = sixVertexFourByTwoCycleMiddleSecond.vertical := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveCycleMiddleSecond_vertical_unique vertical

/--
[sixVertexFourByTwoActiveCycleRepair_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveCycleRepair_bigrade_eq :
-- imply
  sixVertexHorizontalPairBigrade (sixVertexFourByTwoCycleMiddleFirst.horizontal, sixVertexFourByTwoCycleMiddleSecond.horizontal) = sixVertexFourByTwoActiveObstructionGrade := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveCycleRepair_bigrade

/--
[sixVertexFourByTwoActiveCycleMiddleFirstLower_isEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveCycleMiddleFirstLower_isEmpty_eq :
-- imply
  IsEmpty (SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero sixVertexFourByTwoCycleMiddleFirst.horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveCycleMiddleFirstLower_isEmpty

/--
[sixVertexFourByTwoActiveCycleRepairProfile_sourceWeight_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveCycleRepairProfile_sourceWeight_eq_zero_eq :
-- imply
  sixVertexHorizontalPairProfileChooseWeight sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo sixVertexFourByTwoActiveCycleRepairProfile = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveCycleRepairProfile_sourceWeight_eq_zero

/--
[sixVertexFourByTwoActiveCycleRepairProfile_surplus_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveCycleRepairProfile_surplus_pos_eq :
-- imply
  0 < sixVertexHorizontalProfileSurplus sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorOne sixVertexFourByTwoActiveCycleRepairProfile := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveCycleRepairProfile_surplus_pos

/--
[sixVertexFourByTwoActiveCycleMiddleFirstCompletion_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveCycleMiddleFirstCompletion_unique_eq
  {completion : SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoCycleMiddleFirst.horizontal} :
-- imply
  completion = sixVertexFourByTwoActiveCycleMiddleFirstCompletion := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveCycleMiddleFirstCompletion_unique completion

/--
[sixVertexFourByTwoActiveCycleMiddleSecondCompletion_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveCycleMiddleSecondCompletion_unique_eq
  {completion : SixVertexHorizontalSectorCompletion sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoCycleMiddleSecond.horizontal} :
-- imply
  completion = sixVertexFourByTwoActiveCycleMiddleSecondCompletion := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveCycleMiddleSecondCompletion_unique completion

/--
[sixVertexFourByTwoActiveCycleRepairCompletionPair_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveCycleRepairCompletionPair_eq_eq :
-- imply
  sixVertexHorizontalActualSurplusCompletionPair sixVertexFourByTwoActiveCycleRepairSurplusToken = (sixVertexFourByTwoActiveCycleMiddleFirstCompletion, sixVertexFourByTwoActiveCycleMiddleSecondCompletion) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveCycleRepairCompletionPair_eq

/--
[sixVertexFourByTwoActiveCycleRepairPhysicalTarget_surplusPreimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveCycleRepairPhysicalTarget_surplusPreimage_eq :
-- imply
  ∃ token : SixVertexHorizontalActualSurplusTokens sixVertexFourByTwoTorus sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorOne, sixVertexHorizontalActualSurplusConfigurationPair token = sixVertexFourByTwoActiveCycleRepairPhysicalTarget := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveCycleRepairPhysicalTarget_surplusPreimage

/--
[sixVertexFourByTwoActiveCycleRepairConfigurationPair_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveCycleRepairConfigurationPair_eq_eq :
-- imply
  (sixVertexHorizontalActualSurplusConfigurationPair sixVertexFourByTwoActiveCycleRepairSurplusToken).1 = (sixVertexFourByTwoActiveCycleMiddleFirstConfiguration, sixVertexFourByTwoActiveCycleMiddleSecondConfiguration) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveCycleRepairConfigurationPair_eq

/--
[sixVertexFourByTwoActiveCycleRepairSurplusToken_key](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveCycleRepairSurplusToken_key_eq :
-- imply
  sixVertexHorizontalActualSurplusFineUnionKey sixVertexFourByTwoActiveCycleRepairSurplusToken = sixVertexFourByTwoActiveCycleRepairKey := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveCycleRepairSurplusToken_key

/--
[sixVertexFourByTwoActiveCycleRepairSurplusCapacity_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveCycleRepairSurplusCapacity_pos_eq :
-- imply
  0 < sixVertexHorizontalActualSurplusFineUnionCapacity sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoActiveCycleRepairKey := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveCycleRepairSurplusCapacity_pos

/--
[sixVertexFourByTwoActiveObstructionToken_cycleRepair_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionToken_cycleRepair_supported_eq :
-- imply
  sixVertexHorizontalOffDiagonalTwoCycleSupport sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoActiveObstructionToken sixVertexFourByTwoActiveCycleRepairSurplusToken := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionToken_cycleRepair_supported

/--
[sixVertexFourByTwoActiveSourceIndex_eq_of_signature](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveSourceIndex_eq_of_signature_eq
  {i : Fin 4 × Fin 50} :
-- imply
  ((forall v, ((sixVertexFourByTwoSourceIndexArrows i).1.horizontal v).toNat + ((sixVertexFourByTwoSourceIndexArrows i).2.horizontal v).toNat = (sixVertexFourByTwoLowArrows.horizontal v).toNat + (sixVertexFourByTwoHighArrows.horizontal v).toNat) ∧ (forall v, ((sixVertexFourByTwoSourceIndexArrows i).1.vertical v).toNat + ((sixVertexFourByTwoSourceIndexArrows i).2.vertical v).toNat = (sixVertexFourByTwoLowArrows.vertical v).toNat + (sixVertexFourByTwoHighArrows.vertical v).toNat) ∧ sixVertexHorizontalPairBoundedFineRowProfile ((sixVertexFourByTwoSourceIndexArrows i).1.horizontal, (sixVertexFourByTwoSourceIndexArrows i).2.horizontal) = sixVertexHorizontalPairBoundedFineRowProfile (sixVertexFourByTwoLowArrows.horizontal, sixVertexFourByTwoHighArrows.horizontal)) -> i = (0, 29) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveSourceIndex_eq_of_signature i

/--
[sixVertexFourByTwoActiveSourceIndex_eq_of_key](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveSourceIndex_eq_of_key_eq
  {i : Fin 4 × Fin 50}
-- given
  (hkey : sixVertexPairFineUnionKey (sixVertexFourByTwoSourceIndexArrows i) = sixVertexPairFineUnionKey (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows)) :
-- imply
  i = (0, 29) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveSourceIndex_eq_of_key i hkey

/--
[sixVertexFourByTwoActiveSourceIndexArrows_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveSourceIndexArrows_eq_eq :
-- imply
  sixVertexFourByTwoSourceIndexArrows (0, 29) = (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveSourceIndexArrows_eq

/--
[sixVertexFourByTwoActiveSourceConfigurationPair_unique_of_key](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveSourceConfigurationPair_unique_of_key_eq
  {source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero × SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo}
-- given
  (hkey : sixVertexPairFineUnionKey (source.1.1, source.2.1) = sixVertexPairFineUnionKey (sixVertexFourByTwoLowArrows, sixVertexFourByTwoHighArrows)) :
-- imply
  source = (sixVertexFourByTwoLowConfiguration, sixVertexFourByTwoHighConfiguration) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveSourceConfigurationPair_unique_of_key source hkey

/--
[sixVertexFourByTwoActiveObstructionSourceKeyFiber_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionSourceKeyFiber_eq_eq
  {source : SixVertexHorizontalActualDeficitFineUnionKeyFiber sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoActiveObstructionKey} :
-- imply
  source = ⟨sixVertexFourByTwoActiveObstructionToken, rfl⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionSourceKeyFiber_eq source

/--
[sixVertexFourByTwoActiveObstructionSourceKeyFiber_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionSourceKeyFiber_subsingleton_eq
  {first second : SixVertexHorizontalActualDeficitFineUnionKeyFiber sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoActiveObstructionKey} :
-- imply
  first = second := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionSourceKeyFiber_subsingleton first second

/--
[sixVertexFourByTwoActiveObstructionCycleRepairFiberEmbedding_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionCycleRepairFiberEmbedding_supported_eq
  {source : SixVertexHorizontalActualDeficitFineUnionKeyFiber sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoActiveObstructionKey} :
-- imply
  sixVertexHorizontalOffDiagonalTwoCycleSupport sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt sixVertexFourByTwoActiveObstructionGrade source.1 (sixVertexFourByTwoActiveObstructionCycleRepairFiberEmbedding source).1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionCycleRepairFiberEmbedding_supported source

/--
[sixVertexFourByTwoActiveObstructionCapacity_le_cycleRepair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstructionCapacity_le_cycleRepair_eq :
-- imply
  sixVertexHorizontalActualDeficitFineUnionCapacity sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoActiveObstructionKey ≤ sixVertexHorizontalActualSurplusFineUnionCapacity sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt sixVertexFourByTwoActiveObstructionGrade sixVertexFourByTwoActiveCycleRepairKey := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstructionCapacity_le_cycleRepair

/--
[sixVertexFourByTwoActiveObstruction_singletonKeyCapacityHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean)
-/
@[path]
private lemma sixVertexFourByTwoActiveObstruction_singletonKeyCapacityHall_eq :
-- imply
  (∑ key ∈ ({sixVertexFourByTwoActiveObstructionKey} : Finset (SixVertexPairFineUnionKey sixVertexFourByTwoTorus)), sixVertexHorizontalActualDeficitFineUnionCapacity sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt sixVertexFourByTwoActiveObstructionGrade key) ≤ ∑ key ∈ (Finset.univ.filter fun targetKey => exists sourceKey, sourceKey ∈ ({sixVertexFourByTwoActiveObstructionKey} : Finset (SixVertexPairFineUnionKey sixVertexFourByTwoTorus)) ∧ SixVertexPairFineUnionKeyTwoCycleRelated sourceKey targetKey), sixVertexHorizontalActualSurplusFineUnionCapacity sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne sixVertexFourByTwoActiveObstructionMiddle_pos sixVertexFourByTwoActiveObstructionMiddle_lt sixVertexFourByTwoActiveObstructionGrade key := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoActiveObstruction_singletonKeyCapacityHall


-- created on 2026-10-23
