import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoCentralPhysicalBranch.Part9
open StatMech StatMech.FrontierD


/--
[sixVertexFourByTwoSectorThreeConfiguration_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorThreeConfiguration_injective_eq :
-- imply
  Function.Injective sixVertexFourByTwoSectorThreeConfiguration := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorThreeConfiguration_injective

/--
[sixVertexFourByTwoSectorThreeConfiguration_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorThreeConfiguration_surjective_eq :
-- imply
  Function.Surjective sixVertexFourByTwoSectorThreeConfiguration := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorThreeConfiguration_surjective

/--
[sixVertexFourByTwoConfiguration_cGrade_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoConfiguration_cGrade_certificate_eq :
-- imply
  (∀ i : Fin 28, sixVertexCheckerHorizontalNontransitionCount (sixVertexFourByTwoSectorOneConfiguration i).1 = 4 * (sixVertexFourByTwoSectorOneCGrade i).val) ∧ (∀ i : Fin 50, sixVertexCheckerHorizontalNontransitionCount (sixVertexFourByTwoSectorTwoConfiguration i).1 = 4 * (sixVertexFourByTwoSectorTwoCGrade i).val) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoConfiguration_cGrade_certificate

/--
[sixVertexFourByTwoSectorOneConfiguration_cTypeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorOneConfiguration_cTypeCount_eq
  {i : Fin 28} :
-- imply
  sixVertexTorusCTypeCount (sixVertexFourByTwoSectorOneConfiguration i).1 = 4 * (sixVertexFourByTwoSectorOneCGrade i).val := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorOneConfiguration_cTypeCount i

/--
[sixVertexFourByTwoSectorTwoConfiguration_cTypeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorTwoConfiguration_cTypeCount_eq
  {i : Fin 50} :
-- imply
  sixVertexTorusCTypeCount (sixVertexFourByTwoSectorTwoConfiguration i).1 = 4 * (sixVertexFourByTwoSectorTwoCGrade i).val := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorTwoConfiguration_cTypeCount i

/--
[sixVertexFourByTwoCentralRawMatching_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoCentralRawMatching_certificate_eq :
-- imply
  Function.Injective sixVertexFourByTwoCentralRawMatching ∧ ∀ source, (sixVertexFourByTwoCentralRawMatching source).1 ≠ (sixVertexFourByTwoCentralRawMatching source).2 ∧ sixVertexFourByTwoCentralSourceGrade source = sixVertexFourByTwoCentralRawTargetGrade (sixVertexFourByTwoCentralRawMatching source) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCentralRawMatching_certificate

/--
[sixVertexFourByTwoCentralIndexMatching_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoCentralIndexMatching_injective_eq :
-- imply
  Function.Injective sixVertexFourByTwoCentralIndexMatching := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCentralIndexMatching_injective

/--
[sixVertexFourByTwoCentralIndexMatching_grade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoCentralIndexMatching_grade_eq
  {source : sixVertexFourByTwoCentralSourceIndex} :
-- imply
  sixVertexFourByTwoCentralSourceGrade source = sixVertexFourByTwoCentralTargetGrade (sixVertexFourByTwoCentralIndexMatching source) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCentralIndexMatching_grade source

/--
[sixVertexFourByTwoCentralSourceIndex_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoCentralSourceIndex_totalC_eq
  {source : sixVertexFourByTwoCentralSourceIndex} :
-- imply
  sixVertexConfigurationPairTotalCPhysical (sixVertexFourByTwoCentralSourceEquiv source) = 4 * (sixVertexFourByTwoCentralSourceGrade source).val := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCentralSourceIndex_totalC source

/--
[sixVertexFourByTwoCentralTargetIndex_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoCentralTargetIndex_totalC_eq
  {target : sixVertexFourByTwoCentralTargetIndex} :
-- imply
  sixVertexConfigurationPairTotalCPhysical (sixVertexFourByTwoCentralTargetEquiv target.1) = 4 * (sixVertexFourByTwoCentralTargetGrade target).val := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCentralTargetIndex_totalC target

/--
[sixVertexFourByTwoCentralConfigurationMatching_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoCentralConfigurationMatching_injective_eq :
-- imply
  Function.Injective sixVertexFourByTwoCentralConfigurationMatching := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCentralConfigurationMatching_injective

/--
[sixVertexFourByTwoCentralConfigurationMatching_components_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoCentralConfigurationMatching_components_ne_eq
  {source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne × SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus sixVertexFourByTwoSectorThree} :
-- imply
  (sixVertexFourByTwoCentralConfigurationMatching source).1 ≠ (sixVertexFourByTwoCentralConfigurationMatching source).2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCentralConfigurationMatching_components_ne source

/--
[sixVertexFourByTwoCentralConfigurationMatching_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoCentralConfigurationMatching_totalC_eq
  {source : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus sixVertexFourByTwoSectorOne × SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus sixVertexFourByTwoSectorThree} :
-- imply
  sixVertexConfigurationPairTotalCPhysical (sixVertexFourByTwoCentralConfigurationMatching source) = sixVertexConfigurationPairTotalCPhysical source := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCentralConfigurationMatching_totalC source

/--
[sixVertexFourByTwoCentralPhysicalBranch_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoCentralPhysicalBranch_distinct_eq :
-- imply
  sixVertexFourByTwoCentralPhysicalBranch false source ≠ sixVertexFourByTwoCentralPhysicalBranch true source := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCentralPhysicalBranch_distinct

/--
[sixVertexFourByTwoCentralPhysicalBranch_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoCentralPhysicalBranch_totalC_eq
  {choice : Bool}
  (source) :
-- imply
  sixVertexConfigurationPairTotalCPhysical (sixVertexFourByTwoCentralPhysicalBranch choice source) = sixVertexConfigurationPairTotalCPhysical source := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCentralPhysicalBranch_totalC choice

/--
[sixVertexFourByTwoSectorTwo_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorTwo_pos_eq :
-- imply
  0 < sixVertexFourByTwoSectorTwo.val := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorTwo_pos

/--
[sixVertexFourByTwoSectorTwo_lt_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoSectorTwo_lt_width_eq :
-- imply
  sixVertexFourByTwoSectorTwo.val < sixVertexFourByTwoTorus.width := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoSectorTwo_lt_width

/--
[sixVertexFourByTwoCentralPhysicalSourceEmbedding_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoCentralPhysicalSourceEmbedding_totalC_eq
  {source : SixVertexConfigurationPhysicalSource sixVertexFourByTwoTorus sixVertexFourByTwoSectorTwo sixVertexFourByTwoSectorTwo_pos sixVertexFourByTwoSectorTwo_lt_width} :
-- imply
  sixVertexConfigurationPairTotalCPhysical (sixVertexFourByTwoCentralPhysicalSourceEmbedding source) = sixVertexConfigurationPairTotalCPhysical source := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCentralPhysicalSourceEmbedding_totalC source

/--
[sixVertexFourByTwoCentral_sectorTrace_logConcave_of_physicalBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoCentralPhysicalBranch.lean)
-/
@[path]
private lemma sixVertexFourByTwoCentral_sectorTrace_logConcave_of_physicalBranches_eq
  {c : Real}
-- given
  (hc : 1 ≤ c) :
-- imply
  Matrix.trace (sixVertexSectorTransfer 4 1 c ^ 2) * Matrix.trace (sixVertexSectorTransfer 4 3 c ^ 2) ≤ Matrix.trace (sixVertexSectorTransfer 4 2 c ^ 2) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCentral_sectorTrace_logConcave_of_physicalBranches hc


-- created on 2026-10-23
