import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileAggregate.Part4
open Finset StatMech StatMech.FrontierD


/--
[sixVertexHorizontalSectorCompletionChooseCount_eq_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileAggregate.lean)
-/
@[path]
private lemma sixVertexHorizontalSectorCompletionChooseCount_eq_profile_eq
  {T : EvenTorus}
  {sector : Fin (T.width + 1)}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalSectorCompletionChooseCount T sector horizontal = sixVertexHorizontalProfileChooseCount sector (sixVertexHorizontalCompletionProfile T horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalSectorCompletionChooseCount_eq_profile T sector horizontal

/--
[sixVertexHorizontalPairChooseWeight_eq_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileAggregate.lean)
-/
@[path]
private lemma sixVertexHorizontalPairChooseWeight_eq_profile_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1 * sixVertexHorizontalSectorCompletionChooseCount T right horizontal.2 = sixVertexHorizontalPairProfileChooseWeight left right (sixVertexHorizontalPairCompletionProfile T horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairChooseWeight_eq_profile T left right horizontal

/--
[sixVertexHorizontalChooseSum_eq_profileAggregate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileAggregate.lean)
-/
@[path]
private lemma sixVertexHorizontalChooseSum_eq_profileAggregate_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {grade : Nat × Nat} :
-- imply
  (∑ horizontal : {horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T // sixVertexHorizontalPairBigrade horizontal = grade}, sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1.1 * sixVertexHorizontalSectorCompletionChooseCount T right horizontal.1.2) = ∑ profile : SixVertexHorizontalPairCompletionProfile T, sixVertexHorizontalPairProfileMultiplicity T grade profile * sixVertexHorizontalPairProfileChooseWeight left right profile := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalChooseSum_eq_profileAggregate T left right grade

/--
[horizontalChooseBigradeFibers_iff_profileAggregate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileAggregate.lean)
-/
@[path]
private lemma horizontalChooseBigradeFibers_iff_profileAggregate_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
-- imply
  SixVertexHorizontalChooseBigradeFiberDominates T sourceLeft sourceRight targetLeft targetRight ↔ SixVertexHorizontalProfileAggregateDominates T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.horizontalChooseBigradeFibers_iff_profileAggregate T sourceLeft sourceRight targetLeft targetRight


-- created on 2026-10-23
