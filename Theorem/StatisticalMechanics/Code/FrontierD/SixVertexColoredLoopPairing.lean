/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing


namespace StatMech.FrontierD

noncomputable section

theorem boolXor_eq_of_ne_ne
    {a b c d : Bool} (hab : a ≠ b) (hcd : c ≠ d) :
    (a ^^ c) = (b ^^ d) := by
  decide +revert

theorem sixVertexIsCType_iff_horizontalIncoming_eq
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    omega.IsCType v ↔
      fkLoopWestIncoming omega v = fkLoopEastIncoming omega v := by
  unfold SixVertexArrows.IsCType fkLoopWestIncoming fkLoopEastIncoming
  generalize hw : omega.horizontal
    (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = w
  generalize he : omega.horizontal v = e
  cases w <;> cases e <;> simp


end
end StatMech.FrontierD
