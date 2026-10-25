/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeVandermonde.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeVandermonde.Part2
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexFixedChargeNormalizedAlternatingWave (r k : Nat) :
    Tendsto (sixVertexFixedChargeNormalizedAlternatingWave r k) atTop
      (nhds (sixVertexFixedChargeVandermondeSum r k)) := by
  unfold sixVertexFixedChargeNormalizedAlternatingWave
    sixVertexFixedChargeVandermondeSum
  apply tendsto_finsetSum Finset.univ
  intro sigma _
  exact (tendsto_sixVertexFixedChargeNormalizedAmplitude r k sigma).mul
    (tendsto_sixVertexFixedChargeAlternatingMonomial r k sigma)

theorem fixedCharge_bethe_vandermonde_permutation_sum {n : Nat}
    (z : Fin n → Complex) :
    (∑ sigma : Equiv.Perm (Fin n),
      (((Equiv.Perm.sign sigma : Int) : Complex)) *
        (∏ i, ∏ _j ∈ Finset.Ioi i, z (sigma i)) *
        ∏ i, z (sigma i) ^ (2 * i.val + 1)) =
      (∏ i, z i ^ n) * (Matrix.vandermonde z).det := by
  have hpairs (sigma : Equiv.Perm (Fin n)) :
      (∏ i, ∏ _j ∈ Finset.Ioi i, z (sigma i)) =
        ∏ i, z (sigma i) ^ (n - 1 - i.val) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [Finset.prod_const, Fin.card_Ioi]
  rw [Matrix.det_apply', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [hpairs]
  have hreindex : (∏ i, z i ^ n) = ∏ i, z (sigma i) ^ n := by
    simpa using (Equiv.prod_comp sigma (fun i => z i ^ n)).symm
  rw [hreindex]
  simp only [Matrix.vandermonde_apply]
  have hcombine :
      (∏ i, z (sigma i) ^ (n - 1 - i.val)) *
          (∏ i, z (sigma i) ^ (2 * i.val + 1)) =
        (∏ i, z (sigma i) ^ n) *
          ∏ i, z (sigma i) ^ i.val := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_add, ← pow_add]
    have hi := i.isLt
    rw [show n - 1 - i.val + (2 * i.val + 1) = n + i.val by omega]
  calc
    (↑↑(Equiv.Perm.sign sigma) *
          ∏ i, z (sigma i) ^ (n - 1 - i.val)) *
        ∏ i, z (sigma i) ^ (2 * i.val + 1) =
      ↑↑(Equiv.Perm.sign sigma) *
        ((∏ i, z (sigma i) ^ (n - 1 - i.val)) *
          ∏ i, z (sigma i) ^ (2 * i.val + 1)) := by ring
    _ = ↑↑(Equiv.Perm.sign sigma) *
        ((∏ i, z (sigma i) ^ n) *
          ∏ i, z (sigma i) ^ i.val) := by rw [hcombine]
    _ = (∏ i, z (sigma i) ^ n) *
        (↑↑(Equiv.Perm.sign sigma) *
          ∏ i, z (sigma i) ^ i.val) := by ring

theorem sixVertexFixedChargeVandermondeSum_eq (r k : Nat) :
    sixVertexFixedChargeVandermondeSum r k =
      (∏ i, sixVertexFixedChargeLimitingPhase r k i ^
        sixVertexFixedChargeBetheParticleCount r k) *
      (Matrix.vandermonde
        (sixVertexFixedChargeLimitingPhase r k)).det :=
  fixedCharge_bethe_vandermonde_permutation_sum
    (sixVertexFixedChargeLimitingPhase r k)

theorem sixVertexFixedChargeVandermondeSum_ne_zero (r k : Nat) :
    sixVertexFixedChargeVandermondeSum r k ≠ 0 := by
  rw [sixVertexFixedChargeVandermondeSum_eq]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact pow_ne_zero _ (Complex.exp_ne_zero _)
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr
      (sixVertexFixedChargeLimitingPhase_injective r k)

end
end StatMech.FrontierD
