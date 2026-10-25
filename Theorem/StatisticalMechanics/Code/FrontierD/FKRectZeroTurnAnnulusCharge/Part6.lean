/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge.Part6


namespace StatMech.FrontierD

noncomputable section

theorem fkRectZeroTurnRemainderBlackDart_component
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
        (fkRectZeroTurnRemainderBlackDart R omega C).1 = C.1 := by
  have hC := (mem_fkRectZeroTurnCutRemainderComponents R omega C.1).1 C.2
  exact (Classical.choose_spec
    (exists_horizontal_primalBoundaryWinding_of_zeroTurn_avoidsSeam
      R omega C.1 hC.1 hC.2)).1

theorem fkRectZeroTurnRemainderBlackDart_winding_fst_ne_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega C))).1 ≠ 0 := by
  have hC := (mem_fkRectZeroTurnCutRemainderComponents R omega C.1).1 C.2
  exact (Classical.choose_spec
    (exists_horizontal_primalBoundaryWinding_of_zeroTurn_avoidsSeam
      R omega C.1 hC.1 hC.2)).2.1

theorem fkRectZeroTurnRemainderBlackDart_winding_snd_eq_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega
      (fkRectZeroTurnRemainderBlackDart R omega C))).2 = 0 := by
  have hC := (mem_fkRectZeroTurnCutRemainderComponents R omega C.1).1 C.2
  exact (Classical.choose_spec
    (exists_horizontal_primalBoundaryWinding_of_zeroTurn_avoidsSeam
      R omega C.1 hC.1 hC.2)).2.2


end
end StatMech.FrontierD
