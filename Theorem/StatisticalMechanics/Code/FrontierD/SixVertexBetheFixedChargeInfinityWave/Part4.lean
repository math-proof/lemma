/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityWave.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeSpectralBranch
import Mathlib.LinearAlgebra.Vandermonde
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityWave.Part4
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedChargeLimitingPhase_eq_geometric
    (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexFixedChargeLimitingPhase r k j =
      sixVertexFixedChargeLimitingPhaseCenter r k *
        sixVertexFixedChargeLimitingPhaseStep r k ^ j.val := by
  unfold sixVertexFixedChargeLimitingPhase sixVertexFixedChargeLimitingRoot
    sixVertexFixedChargeLimitingPhaseCenter
    sixVertexFixedChargeLimitingPhaseStep sixVertexBethePhase
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  rw [sixVertexCentralQuantumNumber_eq]
  push_cast [Nat.cast_sub (by
    exact sixVertexFixedChargeBetheParticleCount_pos r k)]
  have hm : (sixVertexFixedChargeBetheComplementCount r k : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFixedChargeBetheComplementCount_pos r k).ne'
  field_simp [hm]
  ring


end
end StatMech.FrontierD
