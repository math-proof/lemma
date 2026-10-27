import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalActualDeficitSupport.Part3
open Finset StatMech StatMech.FrontierD


/--
[card_sixVertexHorizontalPairProfileFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalActualDeficitSupport.lean)
-/
@[path]
private lemma card_sixVertexHorizontalPairProfileFiber_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {profile : SixVertexHorizontalPairCompletionProfile T} :
-- imply
  Fintype.card (SixVertexHorizontalPairProfileFiber T grade profile) = sixVertexHorizontalPairProfileMultiplicity T grade profile := by
-- proof
  apply StatMech.FrontierD.card_sixVertexHorizontalPairProfileFiber T grade profile

/--
[sixVertexHorizontalActualDeficitPair_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalActualDeficitSupport.lean)
-/
@[path]
private lemma sixVertexHorizontalActualDeficitPair_bigrade_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
  {token : SixVertexHorizontalActualDeficitTokens T grade sourceLeft sourceRight targetLeft targetRight} :
-- imply
  sixVertexHorizontalPairBigrade (sixVertexHorizontalActualDeficitPair token) = grade := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalActualDeficitPair_bigrade token

/--
[sixVertexHorizontalActualSurplusPair_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalActualDeficitSupport.lean)
-/
@[path]
private lemma sixVertexHorizontalActualSurplusPair_bigrade_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
  {token : SixVertexHorizontalActualSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight} :
-- imply
  sixVertexHorizontalPairBigrade (sixVertexHorizontalActualSurplusPair token) = grade := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalActualSurplusPair_bigrade token

/--
[card_sixVertexHorizontalActualDeficitTokens](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalActualDeficitSupport.lean)
-/
@[path]
private lemma card_sixVertexHorizontalActualDeficitTokens_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
-- imply
  Fintype.card (SixVertexHorizontalActualDeficitTokens T grade sourceLeft sourceRight targetLeft targetRight) = Fintype.card (SixVertexHorizontalProfileDeficitTokens T grade sourceLeft sourceRight targetLeft targetRight) := by
-- proof
  apply StatMech.FrontierD.card_sixVertexHorizontalActualDeficitTokens T grade sourceLeft sourceRight targetLeft targetRight

/--
[card_sixVertexHorizontalActualSurplusTokens](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalActualDeficitSupport.lean)
-/
@[path]
private lemma card_sixVertexHorizontalActualSurplusTokens_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
-- imply
  Fintype.card (SixVertexHorizontalActualSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight) = Fintype.card (SixVertexHorizontalProfileSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight) := by
-- proof
  apply StatMech.FrontierD.card_sixVertexHorizontalActualSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight

/--
[profileSignedNonnegative_iff_actualDeficitEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalActualDeficitSupport.lean)
-/
@[path]
private lemma profileSignedNonnegative_iff_actualDeficitEmbeddings_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
-- imply
  SixVertexHorizontalProfileAggregateSignedNonnegative T sourceLeft sourceRight targetLeft targetRight ↔ forall grade, Nonempty (SixVertexHorizontalActualDeficitTokens T grade sourceLeft sourceRight targetLeft targetRight ↪ SixVertexHorizontalActualSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight) := by
-- proof
  apply StatMech.FrontierD.profileSignedNonnegative_iff_actualDeficitEmbeddings T sourceLeft sourceRight targetLeft targetRight

/--
[actualDeficitTokenHall_iff_supportedMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalActualDeficitSupport.lean)
-/
@[path]
private lemma actualDeficitTokenHall_iff_supportedMatching_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (support : forall grade, SixVertexHorizontalActualDeficitTokens T grade sourceLeft sourceRight targetLeft targetRight -> SixVertexHorizontalActualSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight -> Prop) :
-- imply
  SixVertexHorizontalActualDeficitTokenHall T sourceLeft sourceRight targetLeft targetRight support ↔ SixVertexHorizontalActualDeficitSupportedMatching T sourceLeft sourceRight targetLeft targetRight support := by
-- proof
  apply StatMech.FrontierD.actualDeficitTokenHall_iff_supportedMatching T sourceLeft sourceRight targetLeft targetRight support

/--
[configurationBigradeFibers_of_actualDeficitTokenHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalActualDeficitSupport.lean)
-/
@[path]
private lemma configurationBigradeFibers_of_actualDeficitTokenHall_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (support : forall grade, SixVertexHorizontalActualDeficitTokens T grade sourceLeft sourceRight targetLeft targetRight -> SixVertexHorizontalActualSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight -> Prop)
  (hHall : SixVertexHorizontalActualDeficitTokenHall T sourceLeft sourceRight targetLeft targetRight support) :
-- imply
  SixVertexConfigurationPairBigradeFiberDominates T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.configurationBigradeFibers_of_actualDeficitTokenHall T sourceLeft sourceRight targetLeft targetRight support hHall


-- created on 2026-10-23
