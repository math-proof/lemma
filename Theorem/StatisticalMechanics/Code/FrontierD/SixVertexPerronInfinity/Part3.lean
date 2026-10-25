/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronInfinity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part7
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPerronInfinity.Part2
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFulmekPerronBound_pos
    {n r : Nat} (hn : 0 < n) :
    0 < sixVertexFulmekPerronBound n r := by
  unfold sixVertexFulmekPerronBound
  apply mul_pos (by positivity)
  apply Finset.prod_pos
  intro j _
  let x : Real := Real.pi * (2 * (j : Real) + 1) / (n + 2 * r)
  have hden : (0 : Real) < n + 2 * r := by positivity
  have hx0 : 0 < x := by
    dsimp [x]
    positivity
  have hj : (j : Nat) < r := j.isLt
  have hxpi : x < Real.pi := by
    dsimp [x]
    rw [div_lt_iff₀ hden]
    have hnumNat : 2 * (j : Nat) + 1 < n + 2 * r := by omega
    have hnumReal : 2 * (j : Real) + 1 < (n : Real) + 2 * (r : Real) := by
      exact_mod_cast hnumNat
    exact mul_lt_mul_of_pos_left hnumReal Real.pi_pos
  have hhalf : x / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hcos : 0 < Real.cos (x / 2) := Real.cos_pos_of_mem_Ioo hhalf
  have hid := Real.cos_two_mul (x / 2)
  have htwo : 2 * (x / 2) = x := by ring
  rw [htwo] at hid
  nlinarith [sq_pos_of_pos hcos]


theorem sixVertexNoAdjacentInfinityTop_le_of_positive_supersolution
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N)
    {R : Real} (q : SixVertexNoAdjacentSector N n → Real)
    (hqpos : ∀ i, 0 < q i)
    (hq : ∀ i, (sixVertexNoAdjacentTransferInfinity N n *ᵥ q) i ≤
      R * q i) :
    sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf ≤ R := by
  obtain ⟨v, hvpos, hveig⟩ :=
    sixVertexNoAdjacentInfinityTop_exists_positive_eigenvector hn hhalf
  let S : Real := ∑ i, v i * q i
  have hS : 0 < S := by
    let p := sixVertexNoAdjacentAlternatingEven N n hn hhalf
    apply Finset.sum_pos'
    · intro i _
      exact (mul_pos (hvpos i) (hqpos i)).le
    · exact ⟨p, Finset.mem_univ p, mul_pos (hvpos p) (hqpos p)⟩
  have hweighted :
      ∑ i, v i * (sixVertexNoAdjacentTransferInfinity N n *ᵥ q) i ≤
        ∑ i, v i * (R * q i) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hq i) (hvpos i).le
  have hleft :
      (∑ i, v i * (sixVertexNoAdjacentTransferInfinity N n *ᵥ q) i) =
        sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf * S := by
    simp only [Matrix.mulVec, dotProduct]
    calc
      (∑ i, v i * ∑ j,
          sixVertexNoAdjacentTransferInfinity N n i j * q j) =
          ∑ j, q j * ∑ i,
            sixVertexNoAdjacentTransferInfinity N n j i * v i := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        rw [sixVertexNoAdjacentTransferInfinity_symmetric N n]
        ring
      _ = ∑ j, q j *
          (sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf * v j) := by
        apply Finset.sum_congr rfl
        intro j _
        have hj := congrFun hveig j
        simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
          using congrArg (fun z : Real => q j * z) hj
      _ = sixVertexNoAdjacentInfinityTopEigenvalue N n hn hhalf * S := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hright : (∑ i, v i * (R * q i)) = R * S := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hleft, hright] at hweighted
  nlinarith


end
end StatMech.FrontierD
