/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCount
import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourPhysicalBranch.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourDiagonalGradeCountNat
    (sector : Fin 5) (totalC : Nat) : Nat :=
  if totalC % 2 = 0 then
    sixVertexFourByFourGradeCountNat sector (totalC / 2)
  else 0

end
end StatMech.FrontierD
