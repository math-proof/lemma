/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityWave.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeSpectralBranch
import Mathlib.LinearAlgebra.Vandermonde
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityWave.Part5
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem alternant_sum_eq_center_mul_vandermonde
    {n : Nat} (a b : Complex) (e : Fin n -> Nat) :
    (∑ sigma : Equiv.Perm (Fin n),
      (((Equiv.Perm.sign sigma : Int) : Complex)) *
        ∏ i, (a * b ^ (sigma i).val) ^ e i) =
      (∏ i, a ^ e i) * (Matrix.vandermonde (fun i => b ^ e i)).det := by
  rw [← Matrix.det_transpose, Matrix.det_apply', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  simp only [Matrix.transpose_apply, Matrix.vandermonde_apply]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  have hpows : (∏ i, (b ^ (sigma i).val) ^ e i) =
      ∏ i, (b ^ e i) ^ (sigma i).val := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, ← pow_mul]
    congr 1
    exact Nat.mul_comm _ _
  rw [hpows]
  ring

theorem sixVertexFixedChargeLimitingWave_eq_center_mul_vandermonde
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexFixedChargeLimitingWave r k x =
      (∏ i, sixVertexFixedChargeLimitingPhaseCenter r k ^
        sixVertexFixedChargeAlternantExponent r k x i) *
      (Matrix.vandermonde
        (sixVertexFixedChargeAlternantPoint r k x)).det := by
  rw [sixVertexFixedChargeLimitingWave_eq_alternant]
  simp_rw [sixVertexFixedChargeLimitingPhase_eq_geometric]
  exact alternant_sum_eq_center_mul_vandermonde
    (sixVertexFixedChargeLimitingPhaseCenter r k)
    (sixVertexFixedChargeLimitingPhaseStep r k)
    (sixVertexFixedChargeAlternantExponent r k x)

end
end StatMech.FrontierD
