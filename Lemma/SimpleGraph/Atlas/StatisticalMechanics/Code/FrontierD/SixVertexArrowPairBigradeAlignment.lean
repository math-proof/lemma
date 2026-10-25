import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexArrowPairBigradeAlignment.Part3
open StatMech StatMech.FrontierD


/--
[sixVertexArrowStrandSlotColor_west_succ_eq_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexArrowPairBigradeAlignment.lean)
-/
@[path]
private lemma sixVertexArrowStrandSlotColor_west_succ_eq_east_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  sixVertexArrowStrandSlotColor omega ((finitePeriodicSucc T.width_pos v.1, v.2), false) = sixVertexArrowStrandSlotColor omega (v, true) := by
-- proof
  apply StatMech.FrontierD.sixVertexArrowStrandSlotColor_west_succ_eq_east omega v

/--
[sixVertexArrowStrandSlotColor_west_eq_east_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexArrowPairBigradeAlignment.lean)
-/
@[path]
private lemma sixVertexArrowStrandSlotColor_west_eq_east_pred_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  sixVertexArrowStrandSlotColor omega (v, false) = sixVertexArrowStrandSlotColor omega ((SixVertexArrows.cyclicPred T.width_pos v.1, v.2), true) := by
-- proof
  apply StatMech.FrontierD.sixVertexArrowStrandSlotColor_west_eq_east_pred omega v

/--
[sixVertexArrowStrandSlotColor_east_eq_true_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexArrowPairBigradeAlignment.lean)
-/
@[path]
private lemma sixVertexArrowStrandSlotColor_east_eq_true_iff_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  sixVertexArrowStrandSlotColor omega (v, true) = true ↔ omega.horizontal v = fkMedialVertexParity v := by
-- proof
  apply StatMech.FrontierD.sixVertexArrowStrandSlotColor_east_eq_true_iff omega v

/--
[sixVertexArrowTrueStrandSlotCount_eq_two_mul_alignment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexArrowPairBigradeAlignment.lean)
-/
@[path]
private lemma sixVertexArrowTrueStrandSlotCount_eq_two_mul_alignment_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T} :
-- imply
  sixVertexArrowTrueStrandSlotCount omega = 2 * sixVertexArrowCheckerHorizontalAgreementCount omega := by
-- proof
  apply StatMech.FrontierD.sixVertexArrowTrueStrandSlotCount_eq_two_mul_alignment omega

/--
[sixVertexArrowPairTrueStrandSlotCount_eq_two_mul_alignment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexArrowPairBigradeAlignment.lean)
-/
@[path]
private lemma sixVertexArrowPairTrueStrandSlotCount_eq_two_mul_alignment_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T} :
-- imply
  sixVertexArrowPairTrueStrandSlotCount omega eta = 2 * (sixVertexArrowCheckerHorizontalAgreementCount omega + sixVertexArrowCheckerHorizontalAgreementCount eta) := by
-- proof
  apply StatMech.FrontierD.sixVertexArrowPairTrueStrandSlotCount_eq_two_mul_alignment omega eta


-- created on 2026-10-23
