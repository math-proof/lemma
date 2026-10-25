/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedCycleFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalDisagreementSwitch.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDirectedCycleFlip.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexTorusFlip_maskXor
    {T : EvenTorus} (first second omega : SixVertexArrows T) :
    sixVertexTorusFlip second (sixVertexTorusFlip first omega) =
      sixVertexTorusFlip (sixVertexTorusMaskXor first second) omega := by
  ext edge
  · cases hfirst : first.horizontal edge <;>
      cases hsecond : second.horizontal edge <;>
      cases harrow : omega.horizontal edge <;>
      simp [sixVertexTorusFlip, sixVertexTorusMaskXor,
        hfirst, hsecond, harrow]
  · cases hfirst : first.vertical edge <;>
      cases hsecond : second.vertical edge <;>
      cases harrow : omega.vertical edge <;>
      simp [sixVertexTorusFlip, sixVertexTorusMaskXor,
        hfirst, hsecond, harrow]


@[simp] theorem sixVertexTorusFlip_self
    {T : EvenTorus} (mask omega : SixVertexArrows T) :
    sixVertexTorusFlip mask (sixVertexTorusFlip mask omega) = omega := by
  ext edge
  · cases h : mask.horizontal edge <;> simp [sixVertexTorusFlip, h]
  · cases h : mask.vertical edge <;> simp [sixVertexTorusFlip, h]

@[simp] theorem sixVertexTorusFlip_horizontal_selected
    {T : EvenTorus} (mask omega : SixVertexArrows T) (edge : T.Vertex)
    (hselected : mask.horizontal edge = true) :
    (sixVertexTorusFlip mask omega).horizontal edge =
      !omega.horizontal edge := by
  simp [sixVertexTorusFlip, hselected]

@[simp] theorem sixVertexTorusFlip_horizontal_unselected
    {T : EvenTorus} (mask omega : SixVertexArrows T) (edge : T.Vertex)
    (hunselected : mask.horizontal edge = false) :
    (sixVertexTorusFlip mask omega).horizontal edge =
      omega.horizontal edge := by
  simp [sixVertexTorusFlip, hunselected]

@[simp] theorem sixVertexTorusFlip_vertical_selected
    {T : EvenTorus} (mask omega : SixVertexArrows T) (edge : T.Vertex)
    (hselected : mask.vertical edge = true) :
    (sixVertexTorusFlip mask omega).vertical edge =
      !omega.vertical edge := by
  simp [sixVertexTorusFlip, hselected]

@[simp] theorem sixVertexTorusFlip_vertical_unselected
    {T : EvenTorus} (mask omega : SixVertexArrows T) (edge : T.Vertex)
    (hunselected : mask.vertical edge = false) :
    (sixVertexTorusFlip mask omega).vertical edge =
      omega.vertical edge := by
  simp [sixVertexTorusFlip, hunselected]


theorem sixVertexLocalIncomingPattern_torusFlip
    {T : EvenTorus} (mask omega : SixVertexArrows T) (v : T.Vertex) :
    sixVertexLocalIncomingPattern (sixVertexTorusFlip mask omega) v =
      sixVertexLocalFlipMask (sixVertexLocalIncomingPattern omega v)
        (sixVertexTorusLocalSwitchMask mask v) := by
  funext side
  fin_cases side <;>
    simp [sixVertexLocalIncomingPattern, sixVertexTorusFlip,
      sixVertexTorusLocalSwitchMask, sixVertexLocalFlipMask,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming] <;>
    split <;> simp_all


end
end StatMech.FrontierD
