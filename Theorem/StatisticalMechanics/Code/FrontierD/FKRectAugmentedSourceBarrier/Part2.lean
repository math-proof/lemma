/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectAugmentedSourceBarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightBandVerticalWitness.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectAugmentedSourceBarrier.Part2


namespace StatMech.FrontierD

noncomputable section

theorem fkRectAugmentedSource_barrierConnectionProduct_le
    (R : FKRectTorus) (leftRight cut : Nat) (hsep : leftRight < cut)
    {q : Real} (hq : 1 ≤ q) (gap : R.EdgeIndex) (x : Fin R.width)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1))) :
    (∏ xy ∈ t,
        FK.twoPointFun
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut 1 (R.height - 1)))
          (fkRectCriticalP q) q xy.1 xy.2) *
        fkRectCriticalEventMass R q
          (fkRectAugmentedSourceBarrier R leftRight gap x) ≤
      ∑ rho,
        (fkRectAugmentedBarrierConnectionEvent R
          leftRight cut gap x t).indicator (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R)
            (fkRectCriticalP q) q rho := by
  exact fkRectRightStripBand_connectionProduct_mul_outsideMass_le_genericInter
    R cut 1 (R.height - 1) hq t
      (fkRectAugmentedSourceBarrier_dependsOnOutsideRightBand
        R leftRight cut hsep gap x)

end
end StatMech.FrontierD
