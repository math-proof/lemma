/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexArrowPairBigradeAlignment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopPairBigrade.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexArrowPairBigradeAlignment


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexArrowStrandSlotColor_west_succ_eq_east
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    sixVertexArrowStrandSlotColor omega
        ((finitePeriodicSucc T.width_pos v.1, v.2), false) =
      sixVertexArrowStrandSlotColor omega (v, true) := by
  have hc := fkMedialCheckerColor_bondMate_ne T (v, .east)
  have hi := fkMedialDartIncoming_bondMate_ne T omega (v, .east)
  have hxor := boolXor_eq_of_ne_ne hc hi
  simpa [sixVertexArrowStrandSlotColor,
    sixVertexArrowPairStrandSlotColor, fkMedialBondMate] using hxor

theorem sixVertexArrowStrandSlotColor_west_eq_east_pred
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    sixVertexArrowStrandSlotColor omega (v, false) =
      sixVertexArrowStrandSlotColor omega
        ((SixVertexArrows.cyclicPred T.width_pos v.1, v.2), true) := by
  simpa [finitePeriodicSucc_cyclicPred] using
    sixVertexArrowStrandSlotColor_west_succ_eq_east omega
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2)

theorem sixVertexArrowStrandSlotColor_east_eq_true_iff
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    sixVertexArrowStrandSlotColor omega (v, true) = true ↔
      omega.horizontal v = fkMedialVertexParity v := by
  unfold sixVertexArrowStrandSlotColor
    sixVertexArrowPairStrandSlotColor fkMedialDartIncoming
    fkLoopEastIncoming fkMedialCheckerColor fkMedialSideVertical
  generalize hp : fkMedialVertexParity v = p
  generalize hh : omega.horizontal v = h
  cases p <;> cases h <;> simp_all

end
end StatMech.FrontierD
