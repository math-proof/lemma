module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourGradeCount
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourPhysicalBranch.Part4
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourPhysicalBranch.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByFourOffDiagonalGradeCountNat
    (sector : Fin 5) (totalC : Nat) : Nat :=
  sixVertexFourByFourPairGradeCountNat sector sector totalC -
    sixVertexFourByFourDiagonalGradeCountNat sector totalC

end
end StatMech.FrontierD
