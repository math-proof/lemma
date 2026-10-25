/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAnnulusCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAnnulusCharge


namespace StatMech.FrontierD

noncomputable section

theorem mem_fkRectRawPrimalCrossingLeftRows
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (y : Fin R.height) :
    y ∈ fkRectRawPrimalCrossingLeftRows R omega C ↔
      (fkRectOpenGraph R
        (fkRectForceCutClosed R omega)).connectedComponentMk
          (fkRectLeftColumn R, y) = C.1 := by
  classical
  simp [fkRectRawPrimalCrossingLeftRows]

theorem fkRectRawPrimalCrossingLeftRows_nonempty
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    (fkRectRawPrimalCrossingLeftRows R omega C).Nonempty := by
  obtain ⟨y, hy⟩ := C.2.1
  exact ⟨y, (mem_fkRectRawPrimalCrossingLeftRows R omega C y).2 hy⟩


end
end StatMech.FrontierD
