/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
import Structure.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectZeroTurnRemainderBlackDart
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    FKMedialBlackDart R.medialTorus := by
  have hC := (mem_fkRectZeroTurnCutRemainderComponents R omega C.1).1 C.2
  exact Classical.choose
    (exists_horizontal_primalBoundaryWinding_of_zeroTurn_avoidsSeam
      R omega C.1 hC.1 hC.2)

end
end StatMech.FrontierD
