import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalColumnClassification
open Finset StatMech StatMech.FrontierD


/--
[sixVertexHorizontalColumnSeamAllowed_both_iff_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalColumnClassification.lean)
-/
@[path]
private lemma sixVertexHorizontalColumnSeamAllowed_both_iff_free_eq
  {T : EvenTorus}
  {horizontal : SixVertexHorizontalField T}
  {i : Fin T.width} :
-- imply
  (sixVertexHorizontalColumnSeamAllowed horizontal i false ∧ sixVertexHorizontalColumnSeamAllowed horizontal i true) ↔ forall j, horizontal (SixVertexArrows.cyclicPred T.width_pos i, j) = horizontal (i, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalColumnSeamAllowed_both_iff_free i

/--
[sixVertexHorizontalColumnSeamAllowed_false_iff_forward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalColumnClassification.lean)
-/
@[path]
private lemma sixVertexHorizontalColumnSeamAllowed_false_iff_forward_eq
  {T : EvenTorus}
  {horizontal : SixVertexHorizontalField T}
  {i : Fin T.width} :
-- imply
  sixVertexHorizontalColumnSeamAllowed horizontal i false ↔ SixVertexForwardInterlaced (fun j => horizontal (SixVertexArrows.cyclicPred T.width_pos i, j)) (fun j => horizontal (i, j)) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalColumnSeamAllowed_false_iff_forward i

/--
[sixVertexHorizontalColumnSeamAllowed_true_iff_backward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalColumnClassification.lean)
-/
@[path]
private lemma sixVertexHorizontalColumnSeamAllowed_true_iff_backward_eq
  {T : EvenTorus}
  {horizontal : SixVertexHorizontalField T}
  {i : Fin T.width} :
-- imply
  sixVertexHorizontalColumnSeamAllowed horizontal i true ↔ SixVertexForwardInterlaced (fun j => horizontal (i, j)) (fun j => horizontal (SixVertexArrows.cyclicPred T.width_pos i, j)) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalColumnSeamAllowed_true_iff_backward i

/--
[sixVertexHorizontalTrueAllowed_sdiff_forced_eq_freeColumns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalColumnClassification.lean)
-/
@[path]
private lemma sixVertexHorizontalTrueAllowed_sdiff_forced_eq_freeColumns_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalTrueAllowedColumns horizontal \ sixVertexHorizontalForcedTrueColumns horizontal = sixVertexHorizontalFreeColumns horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalTrueAllowed_sdiff_forced_eq_freeColumns horizontal

/--
[sixVertexHorizontalTrueAllowed_card_sub_forced_card_eq_freeColumns_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalColumnClassification.lean)
-/
@[path]
private lemma sixVertexHorizontalTrueAllowed_card_sub_forced_card_eq_freeColumns_card_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  (sixVertexHorizontalTrueAllowedColumns horizontal).card - (sixVertexHorizontalForcedTrueColumns horizontal).card = (sixVertexHorizontalFreeColumns horizontal).card := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalTrueAllowed_card_sub_forced_card_eq_freeColumns_card horizontal


-- created on 2026-10-23
