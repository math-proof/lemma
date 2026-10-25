/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnisotropyRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteRoots.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHalfFilledLimitingRoot_mem_Ioo (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) :
    sixVertexHalfFilledLimitingRoot k j ∈ Set.Ioo (-Real.pi) Real.pi := by
  let n : Nat := (k + 1) + (k + 1)
  have hn : (0 : Real) < n := by positivity
  have hj0 : (0 : Real) <= j.val := by positivity
  have hjlt : (j.val : Real) < n := by exact_mod_cast j.isLt
  have hjstep : (j.val : Real) + 1 <= n := by
    exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
  have hIlower : -(n : Real) < 2 * sixVertexCentralQuantumNumber j := by
    rw [sixVertexCentralQuantumNumber_eq]
    dsimp [n] at hn hjlt hjstep ⊢
    nlinarith
  have hIupper : 2 * sixVertexCentralQuantumNumber j < (n : Real) := by
    rw [sixVertexCentralQuantumNumber_eq]
    dsimp [n] at hn hjlt ⊢
    nlinarith
  change -Real.pi <
      (2 * Real.pi * sixVertexCentralQuantumNumber j) / (n : Real) ∧
    (2 * Real.pi * sixVertexCentralQuantumNumber j) / (n : Real) < Real.pi
  constructor
  · rw [lt_div_iff₀ hn]
    have h := mul_lt_mul_of_pos_left hIlower Real.pi_pos
    nlinarith
  · rw [div_lt_iff₀ hn]
    have h := mul_lt_mul_of_pos_left hIupper Real.pi_pos
    nlinarith


theorem sixVertexHalfFilledLimitingPhase_injective (k : Nat) :
    Function.Injective (sixVertexHalfFilledLimitingPhase k) := by
  intro i j hij
  have hroot := sixVertexBethePhase_injective_on_Ioo
    (sixVertexHalfFilledLimitingRoot_mem_Ioo k i)
    (sixVertexHalfFilledLimitingRoot_mem_Ioo k j)
    hij
  have hn : (0 : Real) < (((k + 1) + (k + 1) : Nat) : Real) := by
    positivity
  have hquantum : sixVertexCentralQuantumNumber i =
      sixVertexCentralQuantumNumber j := by
    unfold sixVertexHalfFilledLimitingRoot at hroot
    field_simp [hn.ne', Real.pi_ne_zero] at hroot
    linarith
  exact (strictMono_sixVertexCentralQuantumNumber
    ((k + 1) + (k + 1))).injective hquantum

theorem sixVertexHalfFilledBetheRootAt_equation
    {c : Real} (hc : 2 < c) (k : Nat)
    (j : Fin ((k + 1) + (k + 1))) :
    (sixVertexFourWidth 0 k : Real) *
        sixVertexHalfFilledBetheRootAt k j c =
      2 * Real.pi * sixVertexCentralQuantumNumber j -
        ∑ l, sixVertexTheta c
          (sixVertexHalfFilledBetheRootAt k j c)
          (sixVertexHalfFilledBetheRootAt k l c) := by
  simpa only [sixVertexHalfFilledBetheRootAt_eq hc] using
    sixVertexHalfFilledBetheRoots_is_solution hc k j

theorem sixVertexHalfFilledBetheRootAt_sum_eq_zero
    {c : Real} (hc : 2 < c) (k : Nat) :
    ∑ l, sixVertexHalfFilledBetheRootAt k l c = 0 := by
  simpa only [sixVertexHalfFilledBetheRootAt_eq hc] using
    (sixVertexHalfFilledBetheRoots_is_solution hc k).sum_eq_zero
      (sixVertexFourWidth_pos 0 k)

end
end StatMech.FrontierD
