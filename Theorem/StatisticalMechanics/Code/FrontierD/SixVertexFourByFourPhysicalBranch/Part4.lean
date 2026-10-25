/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCount
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourPhysicalBranch.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourByFourDiagonalGradeCount_eq_nat
    (sector : Fin 5) (totalC : Nat) :
    sixVertexMarkedSectorRowCycleDiagonalGradeCount
        sixVertexFourByFourTorus sector totalC =
      sixVertexFourByFourDiagonalGradeCountNat sector totalC := by
  rw [sixVertexMarkedSectorRowCycleDiagonalGradeCount_eq_nat]
  unfold sixVertexFourByFourDiagonalGradeCountNat
  split
  · rw [sixVertexFourByFourRowCycleGradeCount_eq_nat]
  · rfl

end
end StatMech.FrontierD
