/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamPatternPreservation.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierWindingMass.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierAuxiliary.Part2


namespace StatMech.FrontierD

noncomputable section

def fkRectUnitDualBarrierAuxiliary
    (R : FKRectTorus) (right : Nat)
    (t : Finset
      (FKRectColumnBandVertex R 1 right 1 (R.height - 1) ×
        FKRectColumnBandVertex R 1 right 1 (R.height - 1))) :
    Set R.Configuration :=
  {omega |
    FK.ocd_innerRestrict
        (Subtype.val :
          FKRectColumnBandVertex R 1 right 1 (R.height - 1) -> R.Vertex)
        (fkRectFullGraphConfiguration R omega) ∈
      fkRectInducedConnectionChainEvent R
        (fkRectColumnBand R 1 right 1 (R.height - 1)) t ∧
    omega (fkRectRowZeroAttachmentEdgeAt R
      (fkRectUnitGapColumn R)) = true}


def fkRectUnitAttachmentOpenEvent (R : FKRectTorus) :
    Set R.Configuration :=
  {omega | omega (fkRectRowZeroAttachmentEdgeAt R
    (fkRectUnitGapColumn R)) = true}

end
end StatMech.FrontierD
