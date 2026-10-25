/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCount
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourPhysicalBranch
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourRowCycleGradeCount_eq_nat
    (sector : Fin 5) (totalC : Nat) :
    sixVertexMarkedSectorRowCycleGradeCount
        sixVertexFourByFourTorus sector totalC =
      sixVertexFourByFourGradeCountNat sector totalC := by
  by_cases htotal : totalC < 17
  · rw [sixVertexFourByFourGradeCountNat, dif_pos htotal]
    exact sixVertexFourByFourRowCycleGradeCount_certificate
      sector ⟨totalC, htotal⟩
  · rw [sixVertexFourByFourGradeCountNat, dif_neg htotal]
    apply sixVertexMarkedSectorRowCycleGradeCount_eq_zero_of_area_lt
    norm_num [sixVertexFourByFourTorus]
    omega

end
end StatMech.FrontierD
