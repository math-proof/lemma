import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part3
open StatMech StatMech.FrontierD


/--
[sixVertexHorizontalProfileDeficit_eq_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalResidualCompletions.lean)
-/
@[path]
private lemma sixVertexHorizontalProfileDeficit_eq_sub_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
  {profile : SixVertexHorizontalPairCompletionProfile T} :
-- imply
  sixVertexHorizontalProfileDeficit sourceLeft sourceRight targetLeft targetRight profile = sixVertexHorizontalPairProfileChooseWeight sourceLeft sourceRight profile - sixVertexHorizontalPairProfileChooseWeight targetLeft targetRight profile := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalProfileDeficit_eq_sub sourceLeft sourceRight targetLeft targetRight profile

/--
[sixVertexHorizontalProfileSurplus_eq_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalResidualCompletions.lean)
-/
@[path]
private lemma sixVertexHorizontalProfileSurplus_eq_sub_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
  {profile : SixVertexHorizontalPairCompletionProfile T} :
-- imply
  sixVertexHorizontalProfileSurplus sourceLeft sourceRight targetLeft targetRight profile = sixVertexHorizontalPairProfileChooseWeight targetLeft targetRight profile - sixVertexHorizontalPairProfileChooseWeight sourceLeft sourceRight profile := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalProfileSurplus_eq_sub sourceLeft sourceRight targetLeft targetRight profile

/--
[sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_left_isEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalResidualCompletions.lean)
-/
@[path]
private lemma sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_left_isEmpty_eq
  {T : EvenTorus}
  {sourceLeft sourceRight : Fin (T.width + 1)}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
  (hleft : IsEmpty (SixVertexHorizontalSectorCompletion T sourceLeft horizontal.1)) :
-- imply
  sixVertexHorizontalPairProfileChooseWeight sourceLeft sourceRight (sixVertexHorizontalPairCompletionProfile T horizontal) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_left_isEmpty sourceLeft sourceRight horizontal hleft

/--
[sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_right_isEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalResidualCompletions.lean)
-/
@[path]
private lemma sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_right_isEmpty_eq
  {T : EvenTorus}
  {sourceLeft sourceRight : Fin (T.width + 1)}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
  (hright : IsEmpty (SixVertexHorizontalSectorCompletion T sourceRight horizontal.2)) :
-- imply
  sixVertexHorizontalPairProfileChooseWeight sourceLeft sourceRight (sixVertexHorizontalPairCompletionProfile T horizontal) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_right_isEmpty sourceLeft sourceRight horizontal hright

/--
[sixVertexHorizontalActualDeficitConfigurationPair_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalResidualCompletions.lean)
-/
@[path]
private lemma sixVertexHorizontalActualDeficitConfigurationPair_injective_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
-- imply
  Function.Injective (sixVertexHorizontalActualDeficitConfigurationPair : SixVertexHorizontalActualDeficitTokens T grade sourceLeft sourceRight targetLeft targetRight -> {pair : SixVertexMarkedSectorConfiguration T sourceLeft × SixVertexMarkedSectorConfiguration T sourceRight // sixVertexConfigurationPairBigrade pair = grade}) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalActualDeficitConfigurationPair_injective

/--
[sixVertexHorizontalActualSurplusConfigurationPair_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalResidualCompletions.lean)
-/
@[path]
private lemma sixVertexHorizontalActualSurplusConfigurationPair_injective_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
-- imply
  Function.Injective (sixVertexHorizontalActualSurplusConfigurationPair : SixVertexHorizontalActualSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight -> {pair : SixVertexMarkedSectorConfiguration T targetLeft × SixVertexMarkedSectorConfiguration T targetRight // sixVertexConfigurationPairBigrade pair = grade}) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalActualSurplusConfigurationPair_injective

/--
[sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_sourceWeight_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalResidualCompletions.lean)
-/
@[path]
private lemma sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_sourceWeight_eq_zero_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (configuration : {pair : SixVertexMarkedSectorConfiguration T targetLeft × SixVertexMarkedSectorConfiguration T targetRight // sixVertexConfigurationPairBigrade pair = grade})
  (hzero : sixVertexHorizontalPairProfileChooseWeight sourceLeft sourceRight (sixVertexHorizontalPairCompletionProfile T ((sixVertexConfigurationPairBigradeFiberEquivHorizontalCompletions T targetLeft targetRight grade) configuration).1.1) = 0) :
-- imply
  ∃ token : SixVertexHorizontalActualSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight, sixVertexHorizontalActualSurplusConfigurationPair token = configuration := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_sourceWeight_eq_zero configuration hzero

/--
[sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_horizontalSourceWeight_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalResidualCompletions.lean)
-/
@[path]
private lemma sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_horizontalSourceWeight_eq_zero_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (configuration : {pair : SixVertexMarkedSectorConfiguration T targetLeft × SixVertexMarkedSectorConfiguration T targetRight // sixVertexConfigurationPairBigrade pair = grade})
  (hzero : sixVertexHorizontalPairProfileChooseWeight sourceLeft sourceRight (sixVertexHorizontalPairCompletionProfile T (configuration.1.1.1.horizontal, configuration.1.2.1.horizontal)) = 0) :
-- imply
  ∃ token : SixVertexHorizontalActualSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight, sixVertexHorizontalActualSurplusConfigurationPair token = configuration := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_horizontalSourceWeight_eq_zero configuration hzero

/--
[sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_left_isEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalResidualCompletions.lean)
-/
@[path]
private lemma sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_left_isEmpty_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (configuration : {pair : SixVertexMarkedSectorConfiguration T targetLeft × SixVertexMarkedSectorConfiguration T targetRight // sixVertexConfigurationPairBigrade pair = grade})
  (hleft : IsEmpty (SixVertexHorizontalSectorCompletion T sourceLeft configuration.1.1.1.horizontal)) :
-- imply
  ∃ token : SixVertexHorizontalActualSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight, sixVertexHorizontalActualSurplusConfigurationPair token = configuration := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_left_isEmpty configuration hleft

/--
[sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_right_isEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalResidualCompletions.lean)
-/
@[path]
private lemma sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_right_isEmpty_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (configuration : {pair : SixVertexMarkedSectorConfiguration T targetLeft × SixVertexMarkedSectorConfiguration T targetRight // sixVertexConfigurationPairBigrade pair = grade})
  (hright : IsEmpty (SixVertexHorizontalSectorCompletion T sourceRight configuration.1.2.1.horizontal)) :
-- imply
  ∃ token : SixVertexHorizontalActualSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight, sixVertexHorizontalActualSurplusConfigurationPair token = configuration := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalActualSurplusConfigurationPair_surjective_of_right_isEmpty configuration hright

/--
[configurationBigradeFibers_of_residualConfigurationHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalResidualCompletions.lean)
-/
@[path]
private lemma configurationBigradeFibers_of_residualConfigurationHall_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (support : forall grade, {pair : SixVertexMarkedSectorConfiguration T sourceLeft × SixVertexMarkedSectorConfiguration T sourceRight // sixVertexConfigurationPairBigrade pair = grade} -> {pair : SixVertexMarkedSectorConfiguration T targetLeft × SixVertexMarkedSectorConfiguration T targetRight // sixVertexConfigurationPairBigrade pair = grade} -> Prop)
  (hHall : SixVertexHorizontalActualDeficitTokenHall T sourceLeft sourceRight targetLeft targetRight (sixVertexHorizontalResidualConfigurationSupport T sourceLeft sourceRight targetLeft targetRight support)) :
-- imply
  SixVertexConfigurationPairBigradeFiberDominates T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.configurationBigradeFibers_of_residualConfigurationHall T sourceLeft sourceRight targetLeft targetRight support hHall


-- created on 2026-10-23
