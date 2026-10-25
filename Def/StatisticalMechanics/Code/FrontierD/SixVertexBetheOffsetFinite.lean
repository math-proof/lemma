/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexEvenChargeHalfIndex (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    Fin (((2 * s + k + 1) + (2 * s + k + 1))) :=
  ⟨j.val + s, by
    have hj := j.isLt
    have hcount := sixVertexFixedChargeBetheParticleCount_eq (2 * s) k
    omega⟩


def sixVertexOddChargeLowerHalfIndex (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    Fin (((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))) :=
  ⟨j.val + s, by
    have hj := j.isLt
    have hcount := sixVertexFixedChargeBetheParticleCount_eq (2 * s + 1) k
    omega⟩


def sixVertexOddChargeUpperHalfIndex (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    Fin (((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1))) :=
  ⟨j.val + s + 1, by
    have hj := j.isLt
    have hcount := sixVertexFixedChargeBetheParticleCount_eq (2 * s + 1) k
    omega⟩

end
end StatMech.FrontierD
