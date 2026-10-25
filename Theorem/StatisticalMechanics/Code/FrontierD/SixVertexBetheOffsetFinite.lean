/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetFinite
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexEvenChargeHalfIndex_quantum (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) :
    sixVertexCentralQuantumNumber (sixVertexEvenChargeHalfIndex s k j) =
      sixVertexCentralQuantumNumber j := by
  rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq]
  simp only [sixVertexEvenChargeHalfIndex, Fin.val_mk]
  have hcount : (sixVertexFixedChargeBetheParticleCount (2 * s) k : Real) =
      (2 * s + 2 * (k + 1) : Nat) := by
    exact_mod_cast sixVertexFixedChargeBetheParticleCount_eq (2 * s) k
  rw [hcount]
  push_cast
  ring

theorem sixVertexOddChargeHalfIndex_quantum_average (s k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) :
    (sixVertexCentralQuantumNumber (sixVertexOddChargeLowerHalfIndex s k j) +
        sixVertexCentralQuantumNumber
          (sixVertexOddChargeUpperHalfIndex s k j)) / 2 =
      sixVertexCentralQuantumNumber j := by
  rw [sixVertexCentralQuantumNumber_eq, sixVertexCentralQuantumNumber_eq,
    sixVertexCentralQuantumNumber_eq]
  simp only [sixVertexOddChargeLowerHalfIndex,
    sixVertexOddChargeUpperHalfIndex, Fin.val_mk]
  have hcount :
      (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k : Real) =
        (2 * s + 1 + 2 * (k + 1) : Nat) := by
    exact_mod_cast sixVertexFixedChargeBetheParticleCount_eq (2 * s + 1) k
  rw [hcount]
  push_cast
  ring


end
end StatMech.FrontierD
