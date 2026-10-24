import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexCheckerHorizontalBigrade
open StatMech StatMech.FrontierD


/--
[sixVertex_horizontal_agrees_checker_iff_gauged_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCheckerHorizontalBigrade.lean)
-/
@[path]
private lemma sixVertex_horizontal_agrees_checker_iff_gauged_false_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  omega.horizontal v = fkMedialVertexParity v ↔ sixVertexCheckerHorizontalBit omega v = false := by
-- proof
  apply StatMech.FrontierD.sixVertex_horizontal_agrees_checker_iff_gauged_false omega v

/--
[sixVertexArrowCheckerHorizontalAgreementCount_eq_zeroCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCheckerHorizontalBigrade.lean)
-/
@[path]
private lemma sixVertexArrowCheckerHorizontalAgreementCount_eq_zeroCount_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T} :
-- imply
  sixVertexArrowCheckerHorizontalAgreementCount omega = sixVertexCheckerHorizontalZeroCount omega := by
-- proof
  apply StatMech.FrontierD.sixVertexArrowCheckerHorizontalAgreementCount_eq_zeroCount omega

/--
[sixVertex_isCType_iff_checkerHorizontal_nontransition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCheckerHorizontalBigrade.lean)
-/
@[path]
private lemma sixVertex_isCType_iff_checkerHorizontal_nontransition_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  omega.IsCType v ↔ sixVertexCheckerHorizontalBit omega (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = sixVertexCheckerHorizontalBit omega v := by
-- proof
  apply StatMech.FrontierD.sixVertex_isCType_iff_checkerHorizontal_nontransition omega v

/--
[sixVertexTorusCTypeCount_eq_checkerHorizontal_nontransitionCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCheckerHorizontalBigrade.lean)
-/
@[path]
private lemma sixVertexTorusCTypeCount_eq_checkerHorizontal_nontransitionCount_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T} :
-- imply
  sixVertexTorusCTypeCount omega = sixVertexCheckerHorizontalNontransitionCount omega := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusCTypeCount_eq_checkerHorizontal_nontransitionCount omega

/--
[sixVertexArrowPairTrueStrandSlotCount_eq_two_mul_zeroCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCheckerHorizontalBigrade.lean)
-/
@[path]
private lemma sixVertexArrowPairTrueStrandSlotCount_eq_two_mul_zeroCount_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T} :
-- imply
  sixVertexArrowPairTrueStrandSlotCount omega eta = 2 * (sixVertexCheckerHorizontalZeroCount omega + sixVertexCheckerHorizontalZeroCount eta) := by
-- proof
  apply StatMech.FrontierD.sixVertexArrowPairTrueStrandSlotCount_eq_two_mul_zeroCount omega eta


-- created on 2026-10-23
