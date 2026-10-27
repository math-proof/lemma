import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
open StatMech StatMech.FrontierD


/--
[sixVertexFourByTwoMatchingTable_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoMatchingTable_injective_eq :
-- imply
  Function.Injective sixVertexFourByTwoMatchingTable := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoMatchingTable_injective

/--
[sixVertexFourByTwoMatchingIndex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoMatchingIndex_injective_eq :
-- imply
  Function.Injective sixVertexFourByTwoMatchingIndex := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoMatchingIndex_injective

/--
[sixVertexFourByTwoSectorZeroArrows_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorZeroArrows_valid_eq
  {i : Fin 4} :
-- imply
  (sixVertexFourByTwoSectorZeroArrows i).IceRule /\ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus (sixVertexFourByTwoSectorZeroArrows i) (svFinLast sixVertexFourByTwoTorus.height_pos)) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorZeroArrows_valid i

/--
[sixVertexFourByTwoSectorOneArrows_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorOneArrows_valid_eq
  {i : Fin 28} :
-- imply
  (sixVertexFourByTwoSectorOneArrows i).IceRule /\ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus (sixVertexFourByTwoSectorOneArrows i) (svFinLast sixVertexFourByTwoTorus.height_pos)) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorOneArrows_valid i

/--
[sixVertexFourByTwoSectorTwoArrows_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorTwoArrows_valid_eq
  {i : Fin 50} :
-- imply
  (sixVertexFourByTwoSectorTwoArrows i).IceRule /\ sixVertexUpCount (svTorusVerticalRows sixVertexFourByTwoTorus (sixVertexFourByTwoSectorTwoArrows i) (svFinLast sixVertexFourByTwoTorus.height_pos)) = 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorTwoArrows_valid i

/--
[sixVertexFourByTwoOrdinaryFlat_fineUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoOrdinaryFlat_fineUnion_eq
  {i : Fin 200}
-- given
  (hordinary : ¬ sixVertexFourByTwoExceptionalFlatIndex i) :
-- imply
  sixVertexPairUnionHorizontal (sixVertexFourByTwoSourceFlatArrows i) = sixVertexPairUnionHorizontal (sixVertexFourByTwoTargetFlatArrows i) /\ sixVertexPairUnionVertical (sixVertexFourByTwoSourceFlatArrows i) = sixVertexPairUnionVertical (sixVertexFourByTwoTargetFlatArrows i) /\ sixVertexHorizontalPairBoundedFineRowProfile ((sixVertexFourByTwoSourceFlatArrows i).1.horizontal, (sixVertexFourByTwoSourceFlatArrows i).2.horizontal) = sixVertexHorizontalPairBoundedFineRowProfile ((sixVertexFourByTwoTargetFlatArrows i).1.horizontal, (sixVertexFourByTwoTargetFlatArrows i).2.horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoOrdinaryFlat_fineUnion i hordinary

/--
[sixVertexFourByTwoExceptionalFlat_fineRelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoExceptionalFlat_fineRelated_eq
  {i : Fin 4} :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated (sixVertexFourByTwoSourceFlatArrows (sixVertexFourByTwoExceptionalRepairFlatIndex i)) (sixVertexFourByTwoTargetFlatArrows (sixVertexFourByTwoExceptionalRepairFlatIndex i)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoExceptionalFlat_fineRelated i

/--
[sixVertexFourByTwoMatchingTable_fineRelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoMatchingTable_fineRelated_eq
  {i : Fin 200} :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated (sixVertexFourByTwoSourceFlatArrows i) (sixVertexFourByTwoTargetFlatArrows i) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoMatchingTable_fineRelated i

/--
[sixVertexFourByTwoArrowsOf_encodedMasks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoArrowsOf_encodedMasks_eq
  {omega : SixVertexArrows sixVertexFourByTwoTorus} :
-- imply
  sixVertexFourByTwoArrowsOfMasks (sixVertexFourByTwoHorizontalMask omega) (sixVertexFourByTwoVerticalMask omega) = omega := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoArrowsOf_encodedMasks omega

/--
[sixVertexFourByTwoSectorZeroMasks_classify](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorZeroMasks_classify_eq
  {verticalMask : SixVertexFourByTwoVerticalMaskInSector 0}
-- given
  (horizontalMask : Fin 256)
  (hice : (sixVertexFourByTwoArrowsOfMasks horizontalMask.val verticalMask.val).IceRule) :
-- imply
  exists i : Fin 4, sixVertexFourByTwoSectorZeroMasks i = (horizontalMask.val, verticalMask.val.val) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorZeroMasks_classify horizontalMask verticalMask hice

/--
[sixVertexFourByTwoSectorOneMasks_classify](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorOneMasks_classify_eq
  {verticalMask : SixVertexFourByTwoVerticalMaskInSector 1}
-- given
  (horizontalMask : Fin 256)
  (hice : (sixVertexFourByTwoArrowsOfMasks horizontalMask.val verticalMask.val).IceRule) :
-- imply
  exists i : Fin 28, sixVertexFourByTwoSectorOneMasks i = (horizontalMask.val, verticalMask.val.val) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorOneMasks_classify horizontalMask verticalMask hice

/--
[sixVertexFourByTwoSectorTwoMasks_classify](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorTwoMasks_classify_eq
  {verticalMask : SixVertexFourByTwoVerticalMaskInSector 2}
-- given
  (horizontalMask : Fin 256)
  (hice : (sixVertexFourByTwoArrowsOfMasks horizontalMask.val verticalMask.val).IceRule) :
-- imply
  exists i : Fin 50, sixVertexFourByTwoSectorTwoMasks i = (horizontalMask.val, verticalMask.val.val) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorTwoMasks_classify horizontalMask verticalMask hice

/--
[sixVertexFourByTwoSectorZeroArrows_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorZeroArrows_injective_eq :
-- imply
  Function.Injective sixVertexFourByTwoSectorZeroArrows := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorZeroArrows_injective

/--
[sixVertexFourByTwoSectorOneArrows_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorOneArrows_injective_eq :
-- imply
  Function.Injective sixVertexFourByTwoSectorOneArrows := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorOneArrows_injective

/--
[sixVertexFourByTwoSectorTwoArrows_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorTwoArrows_injective_eq :
-- imply
  Function.Injective sixVertexFourByTwoSectorTwoArrows := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorTwoArrows_injective

/--
[sixVertexFourByTwoSectorZeroConfiguration_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorZeroConfiguration_injective_eq :
-- imply
  Function.Injective sixVertexFourByTwoSectorZeroConfiguration := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorZeroConfiguration_injective

/--
[sixVertexFourByTwoSectorOneConfiguration_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorOneConfiguration_injective_eq :
-- imply
  Function.Injective sixVertexFourByTwoSectorOneConfiguration := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorOneConfiguration_injective

/--
[sixVertexFourByTwoSectorTwoConfiguration_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorTwoConfiguration_injective_eq :
-- imply
  Function.Injective sixVertexFourByTwoSectorTwoConfiguration := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorTwoConfiguration_injective

/--
[sixVertexFourByTwoSectorZeroConfiguration_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorZeroConfiguration_surjective_eq :
-- imply
  Function.Surjective sixVertexFourByTwoSectorZeroConfiguration := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorZeroConfiguration_surjective

/--
[sixVertexFourByTwoSectorOneConfiguration_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorOneConfiguration_surjective_eq :
-- imply
  Function.Surjective sixVertexFourByTwoSectorOneConfiguration := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorOneConfiguration_surjective

/--
[sixVertexFourByTwoSectorTwoConfiguration_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorTwoConfiguration_surjective_eq :
-- imply
  Function.Surjective sixVertexFourByTwoSectorTwoConfiguration := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorTwoConfiguration_surjective

/--
[sixVertexFourByTwoMatchingIndex_fineRelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoMatchingIndex_fineRelated_eq
  {i : Fin 4 × Fin 50} :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated (sixVertexFourByTwoSourceIndexArrows i) (sixVertexFourByTwoTargetIndexArrows (sixVertexFourByTwoMatchingIndex i)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoMatchingIndex_fineRelated i

/--
[sixVertexFourByTwoConfigurationPairMatching_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoConfigurationPairMatching_injective_eq :
-- imply
  Function.Injective sixVertexFourByTwoConfigurationPairMatching := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoConfigurationPairMatching_injective

/--
[sixVertexFourByTwoConfigurationPairMatching_fineRelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwoConfigurationPairMatching_fineRelated_eq
  {source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero × SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo} :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated (source.1.1, source.2.1) ((sixVertexFourByTwoConfigurationPairMatching source).1.1, (sixVertexFourByTwoConfigurationPairMatching source).2.1) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoConfigurationPairMatching_fineRelated source

/--
[sixVertexFourByTwo_configurationPairTwoCycleFineHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwo_configurationPairTwoCycleFineHall_eq :
-- imply
  SixVertexConfigurationPairTwoCycleFineHall sixVertexFourByTwoTorus sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorOne sixVertexFourByTwoSectorTwo := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_configurationPairTwoCycleFineHall

/--
[sixVertexFourByTwo_markedTraceCoefficientwiseLogConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwo_markedTraceCoefficientwiseLogConcave_eq :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave 4 2 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_markedTraceCoefficientwiseLogConcave

/--
[sixVertexFourByTwo_sectorTrace_logConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean)
-/
@[path]
private lemma sixVertexFourByTwo_sectorTrace_logConcave_eq
  {c : Real}
-- given
  (hc : 2 <= c) :
-- imply
  Matrix.trace (sixVertexSectorTransfer 4 0 c ^ 2) * Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 2) <= Matrix.trace (sixVertexSectorTransfer 4 1 c ^ 2) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_sectorTrace_logConcave hc


-- created on 2026-10-23
