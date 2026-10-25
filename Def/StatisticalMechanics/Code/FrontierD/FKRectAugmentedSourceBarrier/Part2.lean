/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedSourceBarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightBandVerticalWitness.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedSourceBarrier


namespace StatMech.FrontierD

noncomputable section

def fkRectAugmentedBarrierConnectionEvent
    (R : FKRectTorus) (leftRight cut : Nat)
    (gap : R.EdgeIndex) (x : Fin R.width)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1))) :
    Set (ConfigSpace (Sym2 R.Vertex)) :=
  (FK.ocd_innerRestrict
      (Subtype.val :
        FKRectRightStripBandVertex R cut 1 (R.height - 1) → R.Vertex) ⁻¹'
        fkRectInducedConnectionChainEvent R
          (fkRectRightStripBand R cut 1 (R.height - 1)) t) ∩
    fkRectFullGraphEvent R
      (fkRectAugmentedSourceBarrier R leftRight gap x)

end
end StatMech.FrontierD
