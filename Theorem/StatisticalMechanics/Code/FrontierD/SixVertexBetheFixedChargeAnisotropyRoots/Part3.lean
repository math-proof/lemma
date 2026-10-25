/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeAnisotropyRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeAnisotropyRoots.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedChargeLimitingRoot_mem_Ioo (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexFixedChargeLimitingRoot r k j ∈ Set.Ioo (-Real.pi) Real.pi := by
  let n := sixVertexFixedChargeBetheParticleCount r k
  let m := sixVertexFixedChargeBetheComplementCount r k
  have hn : 0 < n := sixVertexFixedChargeBetheParticleCount_pos r k
  have hm : 0 < m := sixVertexFixedChargeBetheComplementCount_pos r k
  have hnm : n <= m := by
    dsimp [n, m]
    rw [sixVertexFixedChargeBetheParticleCount_eq,
      sixVertexFixedChargeBetheComplementCount_eq]
    omega
  have hquantum :
      -(m : Real) < 2 * sixVertexCentralQuantumNumber j ∧
        2 * sixVertexCentralQuantumNumber j < (m : Real) := by
    rw [sixVertexCentralQuantumNumber_eq]
    have hj0 : (0 : Real) <= j.val := by positivity
    have hjlt : (j.val : Real) < n := by exact_mod_cast j.isLt
    have hjstep : (j.val : Real) + 1 <= n := by
      exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
    have hnlem : (n : Real) <= m := by exact_mod_cast hnm
    constructor <;> dsimp [n, m] at hjlt hnlem ⊢ <;> nlinarith
  change -Real.pi <
      (2 * Real.pi * sixVertexCentralQuantumNumber j) / (m : Real) ∧
    (2 * Real.pi * sixVertexCentralQuantumNumber j) / (m : Real) < Real.pi
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  constructor
  · rw [lt_div_iff₀ hmReal]
    have := mul_lt_mul_of_pos_left hquantum.1 Real.pi_pos
    nlinarith
  · rw [div_lt_iff₀ hmReal]
    have := mul_lt_mul_of_pos_left hquantum.2 Real.pi_pos
    nlinarith


theorem sixVertexFixedChargeLimitingPhase_injective (r k : Nat) :
    Function.Injective (sixVertexFixedChargeLimitingPhase r k) := by
  intro i j hij
  have hroot := sixVertexBethePhase_injective_on_Ioo
    (sixVertexFixedChargeLimitingRoot_mem_Ioo r k i)
    (sixVertexFixedChargeLimitingRoot_mem_Ioo r k j) hij
  have hm : (0 : Real) <
      (sixVertexFixedChargeBetheComplementCount r k : Nat) := by
    exact_mod_cast sixVertexFixedChargeBetheComplementCount_pos r k
  have hquantum : sixVertexCentralQuantumNumber i =
      sixVertexCentralQuantumNumber j := by
    unfold sixVertexFixedChargeLimitingRoot at hroot
    field_simp [hm.ne', Real.pi_ne_zero] at hroot
    linarith
  exact (strictMono_sixVertexCentralQuantumNumber
    (sixVertexFixedChargeBetheParticleCount r k)).injective hquantum

theorem sixVertexFixedChargeBetheRootAt_equation
    {c : Real} (hc : 2 < c) (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) :
    (sixVertexFourWidth r k : Real) *
        sixVertexFixedChargeBetheRootAt r k j c =
      2 * Real.pi * sixVertexCentralQuantumNumber j -
        ∑ l, sixVertexTheta c
          (sixVertexFixedChargeBetheRootAt r k j c)
          (sixVertexFixedChargeBetheRootAt r k l c) := by
  simpa only [sixVertexFixedChargeBetheRootAt_eq hc] using
    sixVertexFixedChargeBetheRoots_is_solution hc r k j

theorem sixVertexFixedChargeBetheRootAt_sum_eq_zero
    {c : Real} (hc : 2 < c) (r k : Nat) :
    ∑ l, sixVertexFixedChargeBetheRootAt r k l c = 0 := by
  simpa only [sixVertexFixedChargeBetheRootAt_eq hc] using
    sixVertexFixedChargeBetheRoots_sum_eq_zero hc r k

end
end StatMech.FrontierD
