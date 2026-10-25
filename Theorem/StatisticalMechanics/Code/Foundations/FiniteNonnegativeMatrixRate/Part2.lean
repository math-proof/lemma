/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part3
open Finset Matrix Filter Topology
open scoped Matrix.Norms.Operator NNReal


namespace StatMech

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma MatrixPositiveReachable.trans_pow
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j) (start x y : α)
    (hx : MatrixPositiveReachable A start x) {n : ℕ}
    (hxy : 0 < (A ^ n) x y) : MatrixPositiveReachable A start y := by
  obtain ⟨m, hm⟩ := hx
  refine ⟨m + n, ?_⟩
  rw [pow_add, Matrix.mul_apply]
  apply lt_of_lt_of_le (mul_pos hm hxy)
  exact Finset.single_le_sum
    (fun z _ => mul_nonneg (Matrix.pow_apply_nonneg hA m start z)
      (Matrix.pow_apply_nonneg hA n z y))
    (Finset.mem_univ x)

lemma matrixPositiveReachableRestriction_pow_apply
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j) (start : α)
    (n : ℕ) (x y : MatrixPositiveReachableState A start) :
    (matrixPositiveReachableRestriction A start ^ n) x y =
      (A ^ n) x.1 y.1 := by
  induction n generalizing x y with
  | zero =>
      simp only [pow_zero, Matrix.one_apply]
      by_cases hxy : x = y
      · have hval : x.1 = y.1 := congrArg Subtype.val hxy
        simp [hxy, hval]
      · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
        simp [hxy, hval]
  | succ n ih =>
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      change (∑ z : MatrixPositiveReachableState A start,
        (matrixPositiveReachableRestriction A start ^ n) x z * A z.1 y.1) = _
      simp_rw [ih]
      let s := Finset.univ.filter (MatrixPositiveReachable A start)
      calc
        (∑ z : MatrixPositiveReachableState A start,
            (A ^ n) x.1 z.1 * A z.1 y.1) =
            (∑ z ∈ s, (A ^ n) x.1 z * A z y.1) := by
              symm
              apply Finset.sum_subtype s
              intro z
              simp [s]
        _ = ∑ z, (A ^ n) x.1 z * A z y.1 := by
              apply Finset.sum_subset (Finset.filter_subset _ _)
              intro z hz hznot
              have hznotreach : ¬MatrixPositiveReachable A start z := by
                simpa [s] using hznot
              have hpowzero : (A ^ n) x.1 z = 0 := by
                apply le_antisymm
                · apply le_of_not_gt
                  intro hpos
                  exact hznotreach (MatrixPositiveReachable.trans_pow
                    A hA start x.1 z x.2 hpos)
                · exact Matrix.pow_apply_nonneg hA n x.1 z
              simp [hpowzero]

lemma matrixPositiveReachableRestriction_nonneg
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j) (start : α)
    (i j : MatrixPositiveReachableState A start) :
    0 ≤ matrixPositiveReachableRestriction A start i j := hA i.1 j.1

lemma matrixPositiveReachableRestriction_diag_pos
    (A : Matrix α α ℝ) (hdiag : ∀ i, 0 < A i i) (start : α)
    (i : MatrixPositiveReachableState A start) :
    0 < matrixPositiveReachableRestriction A start i i := hdiag i.1

lemma matrixPositiveReachableRestriction_accessible
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j) (start : α)
    (i : MatrixPositiveReachableState A start) :
    ∃ n : ℕ, 0 <
      (matrixPositiveReachableRestriction A start ^ n)
        (matrixPositiveReachableStart A start) i := by
  obtain ⟨n, hn⟩ := i.2
  refine ⟨n, ?_⟩
  rw [matrixPositiveReachableRestriction_pow_apply A hA]
  exact hn

end

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

lemma exists_common_access_time
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hdiag : ∀ i, 0 < A i i) (start : α)
    (haccess : ∀ i, ∃ n : ℕ, 0 < (A ^ n) start i) :
    ∃ K : ℕ, ∀ i, 0 < (A ^ K) start i := by
  let steps : α → ℕ := fun i => Classical.choose (haccess i)
  have hsteps (i : α) : 0 < (A ^ steps i) start i :=
    Classical.choose_spec (haccess i)
  let K := ∑ i, steps i
  refine ⟨K, fun i => ?_⟩
  have hle : steps i ≤ K := by
    exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hsplit : K = steps i + (K - steps i) := by omega
  rw [hsplit, pow_add, Matrix.mul_apply]
  apply lt_of_lt_of_le
    (mul_pos (hsteps i) (pow_self_pos A hA hdiag (K - steps i) i))
  exact Finset.single_le_sum
    (fun j _ => mul_nonneg (Matrix.pow_apply_nonneg hA (steps i) start j)
      (Matrix.pow_apply_nonneg hA (K - steps i) j i))
    (Finset.mem_univ i)

lemma matrixPositiveReachableRestriction_coefficient
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (f : α → ℝ) (start : α) (n : ℕ) :
    ((matrixPositiveReachableRestriction A start ^ n) *ᵥ
        (fun i : MatrixPositiveReachableState A start => f i.1))
        (matrixPositiveReachableStart A start) =
      ((A ^ n) *ᵥ f) start := by
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
  simp_rw [matrixPositiveReachableRestriction_pow_apply A hA]
  let s := Finset.univ.filter (MatrixPositiveReachable A start)
  calc
    (∑ i : MatrixPositiveReachableState A start, (A ^ n) start i.1 * f i.1) =
        ∑ i ∈ s, (A ^ n) start i * f i := by
          symm
          apply Finset.sum_subtype s
          intro i
          simp [s]
    _ = ∑ i, (A ^ n) start i * f i := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i hi hinot
      have hinotreach : ¬MatrixPositiveReachable A start i := by
        simpa [s] using hinot
      have hzero : (A ^ n) start i = 0 := by
        apply le_antisymm
        · exact le_of_not_gt (fun hpos => hinotreach ⟨n, hpos⟩)
        · exact Matrix.pow_apply_nonneg hA n start i
      simp [hzero]


theorem exists_matrixCoefficient_log_div_tendsto_of_nonnegative
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hdiag : ∀ i, 0 < A i i) (f : α → ℝ) (hf : ∀ i, 0 < f i)
    (start : α) :
    ∃ rate : ℝ, Tendsto (fun n : ℕ =>
      Real.log (((A ^ n) *ᵥ f) start) / (n : ℝ)) atTop (nhds rate) := by
  let Ar := matrixPositiveReachableRestriction A start
  let sr := matrixPositiveReachableStart A start
  let fr : MatrixPositiveReachableState A start → ℝ := fun i => f i.1
  have hAr : ∀ i j, 0 ≤ Ar i j :=
    matrixPositiveReachableRestriction_nonneg A hA start
  have hArdiag : ∀ i, 0 < Ar i i :=
    matrixPositiveReachableRestriction_diag_pos A hdiag start
  have hreach : ∀ i, ∃ n : ℕ, 0 < (Ar ^ n) sr i := by
    intro i
    exact matrixPositiveReachableRestriction_accessible A hA start i
  obtain ⟨K, hK⟩ := exists_common_access_time Ar hAr hArdiag sr hreach
  obtain ⟨rate, hrate⟩ := exists_matrixCoefficient_log_div_tendsto
    Ar hAr hArdiag fr (fun i => hf i.1) sr K hK
  refine ⟨rate, hrate.congr' ?_⟩
  filter_upwards [] with n
  rw [matrixPositiveReachableRestriction_coefficient A hA]

end

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]


theorem exists_matrixCoefficient_log_div_tendsto_of_reachable_diag
    (A : Matrix α α ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (start : α)
    (hdiag : ∀ i, MatrixPositiveReachable A start i → 0 < A i i)
    (f : α → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ rate : ℝ, Tendsto (fun n : ℕ =>
      Real.log (((A ^ n) *ᵥ f) start) / (n : ℝ)) atTop (nhds rate) := by
  let Ar := matrixPositiveReachableRestriction A start
  let sr := matrixPositiveReachableStart A start
  let fr : MatrixPositiveReachableState A start → ℝ := fun i => f i.1
  have hAr : ∀ i j, 0 ≤ Ar i j :=
    matrixPositiveReachableRestriction_nonneg A hA start
  have hArdiag : ∀ i, 0 < Ar i i := fun i => hdiag i.1 i.2
  have hreach : ∀ i, ∃ n : ℕ, 0 < (Ar ^ n) sr i := by
    intro i
    exact matrixPositiveReachableRestriction_accessible A hA start i
  obtain ⟨K, hK⟩ := exists_common_access_time Ar hAr hArdiag sr hreach
  obtain ⟨rate, hrate⟩ := exists_matrixCoefficient_log_div_tendsto
    Ar hAr hArdiag fr (fun i => hf i.1) sr K hK
  refine ⟨rate, hrate.congr' ?_⟩
  filter_upwards [] with n
  rw [matrixPositiveReachableRestriction_coefficient A hA]

end
end StatMech
