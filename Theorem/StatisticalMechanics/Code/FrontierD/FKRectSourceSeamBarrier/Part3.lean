/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamBarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBarrierConnectionProduct
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier.Part3


namespace StatMech.FrontierD

noncomputable section

theorem fkRectSourceLeftBarrier_eq_generic
    (R : FKRectTorus) (leftRight : Nat) (gap : R.EdgeIndex) :
    fkRectSourceLeftBarrier R leftRight gap =
      fkRectLeftBarrierWithSeamPattern R leftRight
        (fkRectHorizontalCutEdges R)
        (fkRectAllButOneOpenConfiguration R gap) :=
  rfl

theorem fkRectSourceLeftBarrier_dependsOnOutsideRightStripBand
    (R : FKRectTorus)
    (leftRight cut lower upper : Nat)
    (hsep : leftRight < cut) (hlower : 1 ≤ lower)
    (gap : R.EdgeIndex) :
    FKRectDependsOnOutsideRegion R
      (fkRectRightStripBand R cut lower upper)
      (fkRectSourceLeftBarrier R leftRight gap) := by
  exact fkRectLeftBarrierWithSeamPattern_dependsOnOutsideRightStripBand
    R leftRight cut lower upper hsep hlower
      (fkRectHorizontalCutEdges R)
      (fkRectHorizontalCutEdge_crossesVerticalSeam R)
      (fkRectAllButOneOpenConfiguration R gap)


end
end StatMech.FrontierD
