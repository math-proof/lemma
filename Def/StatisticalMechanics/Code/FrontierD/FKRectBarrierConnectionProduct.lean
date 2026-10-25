/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBarrierConnectionProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBarrierRightStrip.Part4


namespace StatMech.FrontierD

noncomputable section

def fkRectRightBandBarrierConnectionEvent
    (R : FKRectTorus) (leftRight cut lower upper : Nat)
    (I : Finset R.EdgeIndex) (eta : R.Configuration)
    (t : Finset (FKRectRightStripBandVertex R cut lower upper ×
      FKRectRightStripBandVertex R cut lower upper)) :
    Set (ConfigSpace (Sym2 R.Vertex)) :=
  (FK.ocd_innerRestrict
      (Subtype.val :
        FKRectRightStripBandVertex R cut lower upper → R.Vertex) ⁻¹'
        fkRectInducedConnectionChainEvent R
          (fkRectRightStripBand R cut lower upper) t) ∩
    fkRectFullGraphEvent R
      (fkRectLeftBarrierWithSeamPattern R leftRight I eta)


end
end StatMech.FrontierD
