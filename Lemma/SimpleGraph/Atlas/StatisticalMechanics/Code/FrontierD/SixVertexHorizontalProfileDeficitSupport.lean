import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileDeficitSupport
open Finset StatMech StatMech.FrontierD


/--
[deficitTokenHall_iff_supportedMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileDeficitSupport.lean)
-/
@[path]
private lemma deficitTokenHall_iff_supportedMatching_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (support : forall grade, SixVertexHorizontalProfileDeficitTokens T grade sourceLeft sourceRight targetLeft targetRight -> SixVertexHorizontalProfileSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight -> Prop) :
-- imply
  SixVertexHorizontalProfileDeficitTokenHall T sourceLeft sourceRight targetLeft targetRight support ↔ SixVertexHorizontalProfileDeficitSupportedMatching T sourceLeft sourceRight targetLeft targetRight support := by
-- proof
  apply StatMech.FrontierD.deficitTokenHall_iff_supportedMatching T sourceLeft sourceRight targetLeft targetRight support

/--
[horizontalChooseBigradeFibers_of_deficitTokenHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileDeficitSupport.lean)
-/
@[path]
private lemma horizontalChooseBigradeFibers_of_deficitTokenHall_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (support : forall grade, SixVertexHorizontalProfileDeficitTokens T grade sourceLeft sourceRight targetLeft targetRight -> SixVertexHorizontalProfileSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight -> Prop)
  (hHall : SixVertexHorizontalProfileDeficitTokenHall T sourceLeft sourceRight targetLeft targetRight support) :
-- imply
  SixVertexHorizontalChooseBigradeFiberDominates T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.horizontalChooseBigradeFibers_of_deficitTokenHall T sourceLeft sourceRight targetLeft targetRight support hHall

/--
[configurationBigradeFibers_of_deficitTokenHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileDeficitSupport.lean)
-/
@[path]
private lemma configurationBigradeFibers_of_deficitTokenHall_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (support : forall grade, SixVertexHorizontalProfileDeficitTokens T grade sourceLeft sourceRight targetLeft targetRight -> SixVertexHorizontalProfileSurplusTokens T grade sourceLeft sourceRight targetLeft targetRight -> Prop)
  (hHall : SixVertexHorizontalProfileDeficitTokenHall T sourceLeft sourceRight targetLeft targetRight support) :
-- imply
  SixVertexConfigurationPairBigradeFiberDominates T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.configurationBigradeFibers_of_deficitTokenHall T sourceLeft sourceRight targetLeft targetRight support hHall


-- created on 2026-10-23
