import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileHall
open Finset StatMech StatMech.FrontierD


/--
[card_sixVertexHorizontalProfileTokens](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileHall.lean)
-/
@[path]
private lemma card_sixVertexHorizontalProfileTokens_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {left right : Fin (T.width + 1)} :
-- imply
  Fintype.card (SixVertexHorizontalProfileTokens T grade left right) = ∑ profile : SixVertexHorizontalPairCompletionProfile T, sixVertexHorizontalPairProfileMultiplicity T grade profile * sixVertexHorizontalPairProfileChooseWeight left right profile := by
-- proof
  apply StatMech.FrontierD.card_sixVertexHorizontalProfileTokens T grade left right

/--
[profileAggregate_iff_tokenEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileHall.lean)
-/
@[path]
private lemma profileAggregate_iff_tokenEmbeddings_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
-- imply
  SixVertexHorizontalProfileAggregateDominates T sourceLeft sourceRight targetLeft targetRight ↔ forall grade, Nonempty (SixVertexHorizontalProfileTokens T grade sourceLeft sourceRight ↪ SixVertexHorizontalProfileTokens T grade targetLeft targetRight) := by
-- proof
  apply StatMech.FrontierD.profileAggregate_iff_tokenEmbeddings T sourceLeft sourceRight targetLeft targetRight

/--
[profileAggregate_of_tokenHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileHall.lean)
-/
@[path]
private lemma profileAggregate_of_tokenHall_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (support : forall grade, SixVertexHorizontalProfileTokens T grade sourceLeft sourceRight -> SixVertexHorizontalProfileTokens T grade targetLeft targetRight -> Prop)
  (hHall : SixVertexHorizontalProfileTokenHall T sourceLeft sourceRight targetLeft targetRight support) :
-- imply
  SixVertexHorizontalProfileAggregateDominates T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.profileAggregate_of_tokenHall T sourceLeft sourceRight targetLeft targetRight support hHall


-- created on 2026-10-23
