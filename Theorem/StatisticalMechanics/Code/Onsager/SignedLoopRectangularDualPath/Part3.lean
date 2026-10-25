/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularDualPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopDisorderKacWard
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalWeight
import Def.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part5
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

theorem coe_ons_rectDual_X_sq_eq_kwDet
    {M N : Nat}
    (embedding : KWStraightLineEmbedding (ons_rectDualGraph M N))
    (x : Real) :
    (ons_X (ons_rectDualGraph M N) x : Complex) ^ 2 =
      ons_rectDualKWDet embedding x := by
  rw [ons_rectDualKWDet,
    kacWard_straightLine_arbitrary_adaptive]
  congr 1
  unfold ons_X kwEvenPolynomial
  push_cast
  apply Finset.sum_congr rfl
  intro edges _
  simp [Finset.prod_const]


end
end StatMech.Onsager
