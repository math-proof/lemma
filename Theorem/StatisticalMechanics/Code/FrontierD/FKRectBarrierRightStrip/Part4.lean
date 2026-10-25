/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBarrierRightStrip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectBarrierRightStrip.Part3


namespace StatMech.FrontierD

noncomputable section

theorem fkRectLeftBarrierWithSeamPattern_dependsOnOutsideRightStripBand
    (R : FKRectTorus)
    (leftRight cut lower upper : Nat)
    (hsep : leftRight < cut) (hlower : 1 ≤ lower)
    (I : Finset R.EdgeIndex)
    (hI : ∀ a ∈ I,
      fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a))
    (eta : R.Configuration) :
    FKRectDependsOnOutsideRegion R
      (fkRectRightStripBand R cut lower upper)
      (fkRectLeftBarrierWithSeamPattern R leftRight I eta) := by
  apply FKRectDependsOnOutsideRegion.inter
  · exact fkRectNoLeftStripCrossing_dependsOnOutsideRightStripBand
      R leftRight cut lower upper hsep
  · exact fkRectVerticalSeamPattern_dependsOnOutsideRightStripBand
      R cut lower upper hlower I hI eta

end
end StatMech.FrontierD
