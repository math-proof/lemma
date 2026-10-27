import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileDeficitHall
open Finset StatMech StatMech.FrontierD


/--
[card_sixVertexHorizontalProfileDeficitTokens](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileDeficitHall.lean)
-/
@[path]
private lemma card_sixVertexHorizontalProfileDeficitTokens_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
-- imply
  Fintype.card (SixVertexHorizontalProfileDeficitTokens T grade sourceLeft sourceRight targetLeft targetRight) = ∑ profile : SixVertexHorizontalPairCompletionProfile T, sixVertexHorizontalPairProfileMultiplicity T grade profile * sixVertexHorizontalProfileDeficit sourceLeft sourceRight targetLeft targetRight profile := by
-- proof
  apply StatMech.FrontierD.card_sixVertexHorizontalProfileDeficitTokens T grade sourceLeft sourceRight targetLeft targetRight

/--
[card_sixVertexHorizontalProfileSurplusTokens](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileDeficitHall.lean)
-/
@[path]
private lemma card_sixVertexHorizontalProfileSurplusTokens_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
-- imply
  Fintype.card (SixVertexHorizontalProfileSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight) = ∑ profile : SixVertexHorizontalPairCompletionProfile T, sixVertexHorizontalPairProfileMultiplicity T grade profile * sixVertexHorizontalProfileSurplus sourceLeft sourceRight targetLeft targetRight profile := by
-- proof
  apply StatMech.FrontierD.card_sixVertexHorizontalProfileSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight

/--
[profileSignedNonnegative_iff_deficit_le_surplus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileDeficitHall.lean)
-/
@[path]
private lemma profileSignedNonnegative_iff_deficit_le_surplus_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
-- imply
  SixVertexHorizontalProfileAggregateSignedNonnegative T sourceLeft sourceRight targetLeft targetRight ↔ forall grade, Fintype.card (SixVertexHorizontalProfileDeficitTokens T grade sourceLeft sourceRight targetLeft targetRight) <= Fintype.card (SixVertexHorizontalProfileSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight) := by
-- proof
  apply StatMech.FrontierD.profileSignedNonnegative_iff_deficit_le_surplus T sourceLeft sourceRight targetLeft targetRight

/--
[profileSignedNonnegative_iff_deficitEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileDeficitHall.lean)
-/
@[path]
private lemma profileSignedNonnegative_iff_deficitEmbeddings_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
-- imply
  SixVertexHorizontalProfileAggregateSignedNonnegative T sourceLeft sourceRight targetLeft targetRight ↔ forall grade, Nonempty (SixVertexHorizontalProfileDeficitTokens T grade sourceLeft sourceRight targetLeft targetRight ↪ SixVertexHorizontalProfileSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight) := by
-- proof
  apply StatMech.FrontierD.profileSignedNonnegative_iff_deficitEmbeddings T sourceLeft sourceRight targetLeft targetRight


-- created on 2026-10-23
