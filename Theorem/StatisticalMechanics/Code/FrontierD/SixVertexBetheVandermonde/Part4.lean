/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSpectralIsolation
import Mathlib.LinearAlgebra.Vandermonde
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part3
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexHalfFilledNormalizedOddWave (k : Nat) :
    Tendsto (sixVertexHalfFilledNormalizedOddWave k) atTop
      (nhds (sixVertexHalfFilledVandermondeSum k)) := by
  unfold sixVertexHalfFilledNormalizedOddWave
    sixVertexHalfFilledVandermondeSum
  apply tendsto_finsetSum Finset.univ
  intro sigma _
  exact (tendsto_sixVertexHalfFilledNormalizedAmplitude k sigma).mul
    (tendsto_sixVertexHalfFilledOddMonomial k sigma)

theorem bethe_vandermonde_permutation_sum {n : Nat}
    (z : Fin n -> Complex) :
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
        ((∏ i, z (sigma i) ^ n) * ∏ i, z (sigma i) ^ i.val) := by
      rw [hcombine]
    _ = (∏ i, z (sigma i) ^ n) *
        (↑↑(Equiv.Perm.sign sigma) * ∏ i, z (sigma i) ^ i.val) := by
      ring

theorem sixVertexHalfFilledVandermondeSum_eq (k : Nat) :
    sixVertexHalfFilledVandermondeSum k =
      (∏ i, sixVertexHalfFilledLimitingPhase k i ^
        ((k + 1) + (k + 1))) *
      (Matrix.vandermonde (sixVertexHalfFilledLimitingPhase k)).det := by
  exact bethe_vandermonde_permutation_sum
    (sixVertexHalfFilledLimitingPhase k)

theorem sixVertexHalfFilledVandermondeSum_ne_zero (k : Nat) :
    sixVertexHalfFilledVandermondeSum k ≠ 0 := by
  rw [sixVertexHalfFilledVandermondeSum_eq]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact pow_ne_zero _ (Complex.exp_ne_zero _)
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr
      (sixVertexHalfFilledLimitingPhase_injective k)


end
end StatMech.FrontierD
