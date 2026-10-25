/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetBoundarySource.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetFiniteResidual.Part2


namespace StatMech.FrontierD

open Finset

noncomputable section

def sixVertexEvenChargeLeftBoundaryIndex (s k : Nat) (i : Fin s) :
    Fin (((2 * s + k + 1) + (2 * s + k + 1))) :=
  ⟨i, by omega⟩


def sixVertexEvenChargeRightBoundaryIndex (s k : Nat) (i : Fin s) :
    Fin (((2 * s + k + 1) + (2 * s + k + 1))) :=
  ⟨s + sixVertexFixedChargeBetheParticleCount (2 * s) k + i, by
    rw [sixVertexFixedChargeBetheParticleCount_eq]
    omega⟩


end
end StatMech.FrontierD
