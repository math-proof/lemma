import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileLayerSymmetry
open StatMech StatMech.FrontierD


/--
[sixVertexReflectFirstHorizontalLayer_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma sixVertexReflectFirstHorizontalLayer_involutive_eq
  {T : EvenTorus} :
-- imply
  Function.Involutive (sixVertexReflectFirstHorizontalLayer (T := T)) := by
-- proof
  apply StatMech.FrontierD.sixVertexReflectFirstHorizontalLayer_involutive

/--
[sixVertexReflectSecondHorizontalLayer_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma sixVertexReflectSecondHorizontalLayer_involutive_eq
  {T : EvenTorus} :
-- imply
  Function.Involutive (sixVertexReflectSecondHorizontalLayer (T := T)) := by
-- proof
  apply StatMech.FrontierD.sixVertexReflectSecondHorizontalLayer_involutive

/--
[sixVertexHorizontalPairBigrade_reflectFirst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma sixVertexHorizontalPairBigrade_reflectFirst_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairBigrade (sixVertexReflectFirstHorizontalLayer horizontal) = sixVertexHorizontalPairBigrade horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairBigrade_reflectFirst horizontal

/--
[sixVertexHorizontalPairBigrade_reflectSecond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma sixVertexHorizontalPairBigrade_reflectSecond_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairBigrade (sixVertexReflectSecondHorizontalLayer horizontal) = sixVertexHorizontalPairBigrade horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairBigrade_reflectSecond horizontal

/--
[sixVertexReflectFirstHorizontalPairCompletionProfile_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma sixVertexReflectFirstHorizontalPairCompletionProfile_involutive_eq
  {T : EvenTorus} :
-- imply
  Function.Involutive (sixVertexReflectFirstHorizontalPairCompletionProfile (T := T)) := by
-- proof
  apply StatMech.FrontierD.sixVertexReflectFirstHorizontalPairCompletionProfile_involutive

/--
[sixVertexReflectSecondHorizontalPairCompletionProfile_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma sixVertexReflectSecondHorizontalPairCompletionProfile_involutive_eq
  {T : EvenTorus} :
-- imply
  Function.Involutive (sixVertexReflectSecondHorizontalPairCompletionProfile (T := T)) := by
-- proof
  apply StatMech.FrontierD.sixVertexReflectSecondHorizontalPairCompletionProfile_involutive

/--
[sixVertexHorizontalPairCompletionProfile_reflectFirst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma sixVertexHorizontalPairCompletionProfile_reflectFirst_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairCompletionProfile T (sixVertexReflectFirstHorizontalLayer horizontal) = sixVertexReflectFirstHorizontalPairCompletionProfile (sixVertexHorizontalPairCompletionProfile T horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairCompletionProfile_reflectFirst horizontal

/--
[sixVertexHorizontalPairCompletionProfile_reflectSecond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma sixVertexHorizontalPairCompletionProfile_reflectSecond_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairCompletionProfile T (sixVertexReflectSecondHorizontalLayer horizontal) = sixVertexReflectSecondHorizontalPairCompletionProfile (sixVertexHorizontalPairCompletionProfile T horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairCompletionProfile_reflectSecond horizontal

/--
[sixVertexHorizontalPairProfileMultiplicity_reflectFirst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma sixVertexHorizontalPairProfileMultiplicity_reflectFirst_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {profile : SixVertexHorizontalPairCompletionProfile T} :
-- imply
  sixVertexHorizontalPairProfileMultiplicity T grade (sixVertexReflectFirstHorizontalPairCompletionProfile profile) = sixVertexHorizontalPairProfileMultiplicity T grade profile := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairProfileMultiplicity_reflectFirst T grade profile

/--
[sixVertexHorizontalPairProfileMultiplicity_reflectSecond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma sixVertexHorizontalPairProfileMultiplicity_reflectSecond_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {profile : SixVertexHorizontalPairCompletionProfile T} :
-- imply
  sixVertexHorizontalPairProfileMultiplicity T grade (sixVertexReflectSecondHorizontalPairCompletionProfile profile) = sixVertexHorizontalPairProfileMultiplicity T grade profile := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairProfileMultiplicity_reflectSecond T grade profile

/--
[sixVertexSwapHorizontalLayers_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma sixVertexSwapHorizontalLayers_involutive_eq
  {T : EvenTorus} :
-- imply
  Function.Involutive (sixVertexSwapHorizontalLayers (T := T)) := by
-- proof
  apply StatMech.FrontierD.sixVertexSwapHorizontalLayers_involutive

/--
[sixVertexSwapHorizontalPairCompletionProfile_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma sixVertexSwapHorizontalPairCompletionProfile_involutive_eq
  {T : EvenTorus} :
-- imply
  Function.Involutive (sixVertexSwapHorizontalPairCompletionProfile (T := T)) := by
-- proof
  apply StatMech.FrontierD.sixVertexSwapHorizontalPairCompletionProfile_involutive

/--
[sixVertexHorizontalPairBigrade_swapLayers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma sixVertexHorizontalPairBigrade_swapLayers_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairBigrade (sixVertexSwapHorizontalLayers horizontal) = sixVertexHorizontalPairBigrade horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairBigrade_swapLayers horizontal

/--
[sixVertexHorizontalPairCompletionProfile_swapLayers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma sixVertexHorizontalPairCompletionProfile_swapLayers_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairCompletionProfile T (sixVertexSwapHorizontalLayers horizontal) = sixVertexSwapHorizontalPairCompletionProfile (sixVertexHorizontalPairCompletionProfile T horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairCompletionProfile_swapLayers horizontal

/--
[sixVertexHorizontalPairProfileMultiplicity_swapLayers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma sixVertexHorizontalPairProfileMultiplicity_swapLayers_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {profile : SixVertexHorizontalPairCompletionProfile T} :
-- imply
  sixVertexHorizontalPairProfileMultiplicity T grade (sixVertexSwapHorizontalPairCompletionProfile profile) = sixVertexHorizontalPairProfileMultiplicity T grade profile := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairProfileMultiplicity_swapLayers T grade profile

/--
[sixVertexHorizontalChooseSum_reflectFirst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma sixVertexHorizontalChooseSum_reflectFirst_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {grade : Nat × Nat} :
-- imply
  (∑ horizontal : {horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T // sixVertexHorizontalPairBigrade horizontal = grade}, sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1.1 * sixVertexHorizontalSectorCompletionChooseCount T right horizontal.1.2) = ∑ horizontal : {horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T // sixVertexHorizontalPairBigrade horizontal = grade}, sixVertexHorizontalSectorCompletionChooseCount T (sixVertexHorizontalComplementSector T left) horizontal.1.1 * sixVertexHorizontalSectorCompletionChooseCount T right horizontal.1.2 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalChooseSum_reflectFirst T left right grade

/--
[sixVertexHorizontalChooseSum_reflectSecond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma sixVertexHorizontalChooseSum_reflectSecond_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {grade : Nat × Nat} :
-- imply
  (∑ horizontal : {horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T // sixVertexHorizontalPairBigrade horizontal = grade}, sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1.1 * sixVertexHorizontalSectorCompletionChooseCount T right horizontal.1.2) = ∑ horizontal : {horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T // sixVertexHorizontalPairBigrade horizontal = grade}, sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1.1 * sixVertexHorizontalSectorCompletionChooseCount T (sixVertexHorizontalComplementSector T right) horizontal.1.2 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalChooseSum_reflectSecond T left right grade

/--
[horizontalChooseBigradeFibers_iff_diagonal_of_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean)
-/
@[path]
private lemma horizontalChooseBigradeFibers_iff_diagonal_of_complement_eq
  {T : EvenTorus}
  {lower upper middle : Fin (T.width + 1)}
-- given
  (hcomplement : sixVertexHorizontalComplementSector T lower = upper) :
-- imply
  SixVertexHorizontalChooseBigradeFiberDominates T lower upper middle middle ↔ forall grade, (∑ horizontal : {horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T // sixVertexHorizontalPairBigrade horizontal = grade}, sixVertexHorizontalSectorCompletionChooseCount T upper horizontal.1.1 * sixVertexHorizontalSectorCompletionChooseCount T upper horizontal.1.2) <= ∑ horizontal : {horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T // sixVertexHorizontalPairBigrade horizontal = grade}, sixVertexHorizontalSectorCompletionChooseCount T middle horizontal.1.1 * sixVertexHorizontalSectorCompletionChooseCount T middle horizontal.1.2 := by
-- proof
  apply StatMech.FrontierD.horizontalChooseBigradeFibers_iff_diagonal_of_complement T lower upper middle hcomplement


-- created on 2026-10-23
