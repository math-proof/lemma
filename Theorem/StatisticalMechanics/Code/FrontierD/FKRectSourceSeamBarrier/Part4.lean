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
import Def.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier.Part4


namespace StatMech.FrontierD

noncomputable section

theorem fkRectSource_barrierConnectionProduct_le
    (R : FKRectTorus)
    (leftRight cut lower upper : Nat)
    (hsep : leftRight < cut) (hlower : 1 ≤ lower)
    {q : Real} (hq : 1 ≤ q)
    (gap : R.EdgeIndex)
    (t : Finset (FKRectRightStripBandVertex R cut lower upper ×
      FKRectRightStripBandVertex R cut lower upper)) :
    (∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut lower upper))
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q
          (fkRectSourceLeftBarrier R leftRight gap) ≤
      ∑ rho,
        (fkRectSourceBarrierConnectionEvent R
          leftRight cut lower upper gap t).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R)
            (fkRectCriticalP q) q rho := by
  exact fkRectRightBand_barrierConnectionProduct_le R
    leftRight cut lower upper hsep hlower hq
    (fkRectHorizontalCutEdges R)
    (fkRectHorizontalCutEdge_crossesVerticalSeam R)
    (fkRectAllButOneOpenConfiguration R gap) t

end
end StatMech.FrontierD
