/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/NonnegativeCurrentConditionalPMF.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousCurrentConditionalPMF.Part5
import Def.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentConditionalPMF
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising


theorem nonnegativeParityEdgeKernel_nonneg
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (odd : Bool) (k : ℕ) :
    0 ≤ nonnegativeParityEdgeKernel lambda odd k := by
  by_cases hzero : lambda = 0
  · rw [nonnegativeParityEdgeKernel, if_pos hzero]
    by_cases hk : k = (if odd then 1 else 0) <;> simp [hk]
  · rw [nonnegativeParityEdgeKernel, if_neg hzero]
    exact parityEdgeKernel_nonneg lambda
      (lt_of_le_of_ne hlambda (Ne.symm hzero)) odd k

theorem summable_nonnegativeParityEdgeKernel
    {lambda : ℝ} (_hlambda : 0 ≤ lambda) (odd : Bool) :
    Summable (nonnegativeParityEdgeKernel lambda odd) := by
  change Summable (fun k : ℕ =>
    if lambda = 0 then
      if k = (if odd then 1 else 0) then 1 else 0
    else parityEdgeKernel lambda odd k)
  by_cases hzero : lambda = 0
  · simp only [hzero, if_true]
    exact (hasSum_ite_eq (if odd then 1 else 0) (1 : ℝ)).summable
  · simp only [hzero, if_false]
    exact summable_parityEdgeKernel lambda odd

theorem tsum_nonnegativeParityEdgeKernel
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (odd : Bool) :
    ∑' k : ℕ, nonnegativeParityEdgeKernel lambda odd k = 1 := by
  change (∑' k : ℕ, if lambda = 0 then
    if k = (if odd then 1 else 0) then 1 else 0
    else parityEdgeKernel lambda odd k) = 1
  by_cases hzero : lambda = 0
  · simp only [hzero, if_true, tsum_ite_eq]
  · simp only [hzero, if_false]
    exact tsum_parityEdgeKernel lambda
      (lt_of_le_of_ne hlambda (Ne.symm hzero)) odd

theorem nonnegativeParityEdgeKernel_eq_zero_of_parity_ne
    (lambda : ℝ) (odd : Bool) (k : ℕ)
    (hpar : ¬(if odd then Odd k else Even k)) :
    nonnegativeParityEdgeKernel lambda odd k = 0 := by
  by_cases hzero : lambda = 0
  · subst lambda
    cases odd
    · have hk : k ≠ 0 := by
        intro hk
        subst k
        exact hpar (by simp)
      simp [nonnegativeParityEdgeKernel, hk]
    · have hk : k ≠ 1 := by
        intro hk
        subst k
        exact hpar (by simp)
      simp [nonnegativeParityEdgeKernel, hk]
  · cases odd <;> simp_all [nonnegativeParityEdgeKernel,
      parityEdgeKernel]


theorem parityFiberMass_mul_nonnegativeParityEdgeKernel
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (odd : Bool) (k : ℕ)
    (hpar : if odd then Odd k else Even k) :
    (if odd then Real.sinh lambda else Real.cosh lambda) *
        nonnegativeParityEdgeKernel lambda odd k =
      lambda ^ k / k.factorial := by
  by_cases hzero : lambda = 0
  · subst lambda
    cases odd
    · by_cases hk : k = 0
      · subst k
        norm_num [nonnegativeParityEdgeKernel]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        rw [zero_pow (Nat.ne_of_gt hkpos)]
        simp [nonnegativeParityEdgeKernel, hk]
    · have hkpos : 0 < k := Odd.pos hpar
      rw [zero_pow (Nat.ne_of_gt hkpos)]
      simp [nonnegativeParityEdgeKernel]
  · have hlambdaPos : 0 < lambda :=
      lt_of_le_of_ne hlambda (Ne.symm hzero)
    cases odd
    · have heven : Even k := hpar
      have hcosh : Real.cosh lambda ≠ 0 := (Real.cosh_pos lambda).ne'
      simp [nonnegativeParityEdgeKernel, hzero, parityEdgeKernel,
        heven, conditionalCurrentTerm]
      field_simp [hcosh]
    · have hodd : Odd k := hpar
      have hsinh : Real.sinh lambda ≠ 0 :=
        (Real.sinh_pos_iff.2 hlambdaPos).ne'
      simp [nonnegativeParityEdgeKernel, hzero, parityEdgeKernel,
        hodd, conditionalCurrentTerm]
      field_simp [hsinh]


end StatMech.FrontierB
