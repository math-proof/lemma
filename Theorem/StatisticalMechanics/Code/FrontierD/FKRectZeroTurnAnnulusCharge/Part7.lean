/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part7


namespace StatMech.FrontierD

noncomputable section

theorem fkRectZeroTurnRemainderSide_eq_true_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    fkRectZeroTurnRemainderSide R omega C = true ↔
      0 < (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega
          (fkRectZeroTurnRemainderBlackDart R omega C))).1 := by
  simp [fkRectZeroTurnRemainderSide]

theorem fkRectZeroTurnRemainderSide_eq_false_iff
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    fkRectZeroTurnRemainderSide R omega C = false ↔
      (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega
          (fkRectZeroTurnRemainderBlackDart R omega C))).1 < 0 := by
  rw [fkRectZeroTurnRemainderSide, decide_eq_false_iff_not]
  have hne := fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero
    R omega C
  omega


end
end StatMech.FrontierD
