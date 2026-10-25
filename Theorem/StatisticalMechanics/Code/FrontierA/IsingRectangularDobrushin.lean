/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Theorem.StatisticalMechanics.Code.Ising.MonomialDisorder
import Def.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushin.Part2
open scoped BigOperators
open Finset


namespace StatMech.Ising

noncomputable section

theorem rectangularPrismInteractionMonomial_isSpinMonomial
    {m n h : Nat} (q : RectangularPrismInteraction m n h) :
    IsSpinMonomial (rectangularPrismInteractionMonomial q) := by
  rcases q with q | q
  · exact (isSpinMonomial_spin _).mul (isSpinMonomial_spin _)
  · rcases q with q | q
    · exact (isSpinMonomial_spin _).mul (isSpinMonomial_spin _)
    · rcases q with q | v
      · exact (isSpinMonomial_spin _).mul (isSpinMonomial_spin _)
      · exact isSpinMonomial_spin v

theorem rectangularPrismInteractionMonomial_eq_one_or_neg_one
    {m n h : Nat} (q : RectangularPrismInteraction m n h)
    (sigma : RectangularPrismConfig m n h) :
    rectangularPrismInteractionMonomial q sigma = 1 ∨
      rectangularPrismInteractionMonomial q sigma = -1 := by
  have mul_pm {a b : Real} (ha : a = 1 ∨ a = -1)
      (hb : b = 1 ∨ b = -1) : a * b = 1 ∨ a * b = -1 := by
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
      rw [ha, hb] <;> norm_num
  rcases q with q | q
  · simp only [rectangularPrismInteractionMonomial, rectangularPrismSpin]
    exact mul_pm (spin_eq_pm sigma _) (spin_eq_pm sigma _)
  · rcases q with q | q
    · simp only [rectangularPrismInteractionMonomial, rectangularPrismSpin]
      exact mul_pm (spin_eq_pm sigma _) (spin_eq_pm sigma _)
    · rcases q with q | v
      · simp only [rectangularPrismInteractionMonomial, rectangularPrismSpin]
        exact mul_pm (spin_eq_pm sigma _) (spin_eq_pm sigma _)
      · exact spin_eq_pm sigma v

theorem rectangularPrismInteractionCoupling_nonneg
    {J beta : Real} (hJ : 0 <= J) (hbeta : 0 <= beta)
    {m n h : Nat} (q : RectangularPrismInteraction m n h) :
    0 <= rectangularPrismInteractionCoupling J beta q := by
  rcases q with q | q
  · exact mul_nonneg hbeta hJ
  · rcases q with q | q
    · exact mul_nonneg hbeta hJ
    · rcases q with q | v
      · exact mul_nonneg hbeta hJ
      · exact mul_nonneg (mul_nonneg hbeta hJ) (Nat.cast_nonneg _)

theorem sum_rectangularPrismInteraction_eq
    (J beta : Real) {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) :
    (∑ q : RectangularPrismInteraction m n h,
        rectangularPrismInteractionCoupling J beta q *
          rectangularPrismInteractionMonomial q sigma) =
      beta * J * (rectangularPrismInternalInteraction sigma +
        rectangularPrismPlusBoundaryInteraction sigma) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [rectangularPrismInteractionCoupling,
    rectangularPrismInteractionMonomial]
  simp_rw [Fintype.sum_prod_type]
  unfold rectangularPrismInternalInteraction
    rectangularPrismPlusBoundaryInteraction rectangularPrismSpin
  simp_rw [← Finset.mul_sum]
  have hboundary :
      (∑ v : RectangularPrismSite m n h,
          beta * J * (rectangularPrismBoundaryDegree v : Real) * spin sigma v) =
        beta * J * ∑ v : RectangularPrismSite m n h,
          (rectangularPrismBoundaryDegree v : Real) * spin sigma v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hboundary]
  ring

theorem sum_rectangularPrismDisorderSheet_eq
    (J beta : Real) {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) :
    (∑ q ∈ rectangularPrismDisorderSheet m n h,
        rectangularPrismInteractionCoupling J beta q *
          rectangularPrismInteractionMonomial q sigma) =
      beta * J * rectangularPrismInterfaceInteraction sigma := by
  classical
  rw [rectangularPrismDisorderSheet, Finset.sum_filter]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [rectangularPrismInteractionCoupling,
    rectangularPrismInteractionMonomial, Bool.false_eq_true, ↓reduceIte]
  rw [rectangularPrismInterfaceInteraction]
  split_ifs with hh
  · simp_rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const_zero, add_zero, zero_add]
    have hz (x : Fin m) (y : Fin n) :
        (∑ z : Fin (2 * h),
          if z.val = h then
            beta * J * (rectangularPrismSpin sigma x y ⟨z.val, by omega⟩ *
              rectangularPrismSpin sigma x y ⟨z.val + 1, by omega⟩)
          else 0) =
        beta * J * (rectangularPrismSpin sigma x y ⟨h, by omega⟩ *
          rectangularPrismSpin sigma x y ⟨h + 1, by omega⟩) := by
      change (∑ z ∈ (Finset.univ : Finset (Fin (2 * h))),
          if z.val = h then
            beta * J * (rectangularPrismSpin sigma x y ⟨z.val, by omega⟩ *
              rectangularPrismSpin sigma x y ⟨z.val + 1, by omega⟩)
          else 0) = _
      let z0 : Fin (2 * h) := ⟨h, by omega⟩
      have hiff (z : Fin (2 * h)) : z.val = h ↔ z = z0 := by
        constructor
        · intro hz_eq
          apply Fin.ext
          simpa [z0] using hz_eq
        · intro hz_eq
          subst z
          rfl
      simp_rw [hiff]
      simp [z0]
    simp_rw [hz]
    simp_rw [← Finset.mul_sum]
  · have hh0 : h = 0 := Nat.eq_zero_of_not_pos hh
    subst h
    simp_rw [Fintype.sum_prod_type]
    simp


theorem rectangularPrismPlusPartition_eq_monomialInteractionPartition
    (J beta : Real) (m n h : Nat) :
    rectangularPrismPlusPartition J beta m n h =
      monomialInteractionPartition
        (rectangularPrismInteractionCoupling J beta :
          RectangularPrismInteraction m n h -> Real)
        (rectangularPrismInteractionMonomial :
          RectangularPrismInteraction m n h ->
            RectangularPrismConfig m n h -> Real) := by
  unfold rectangularPrismPlusPartition monomialInteractionPartition Z
  apply Finset.sum_congr rfl
  intro sigma _
  congr 1
  rw [sum_rectangularPrismInteraction_eq]
  unfold rectangularPrismPlusEnergy
  ring


theorem rectangularPrismTwistedPartition_eq_monomialInteractionPartition
    (J beta : Real) (m n h : Nat) :
    rectangularPrismTwistedPartition J beta m n h =
      monomialInteractionPartition
        (reverseInteractionCoupling
          (rectangularPrismInteractionCoupling J beta :
            RectangularPrismInteraction m n h -> Real)
          (rectangularPrismDisorderSheet m n h))
        (rectangularPrismInteractionMonomial :
          RectangularPrismInteraction m n h ->
            RectangularPrismConfig m n h -> Real) := by
  unfold rectangularPrismTwistedPartition monomialInteractionPartition Z
  apply Finset.sum_congr rfl
  intro sigma _
  congr 1
  rw [sum_reverseInteractionCoupling,
    sum_rectangularPrismInteraction_eq,
    sum_rectangularPrismDisorderSheet_eq]
  unfold rectangularPrismTwistedEnergy rectangularPrismPlusEnergy
  ring


theorem rectangularPrismTwistedPartition_le_plusPartition
    {J beta : Real} (hJ : 0 <= J) (hbeta : 0 <= beta)
    (m n h : Nat) :
    rectangularPrismTwistedPartition J beta m n h <=
      rectangularPrismPlusPartition J beta m n h := by
  rw [rectangularPrismTwistedPartition_eq_monomialInteractionPartition,
    rectangularPrismPlusPartition_eq_monomialInteractionPartition]
  exact monomialInteractionPartition_reverse_le
    (V := RectangularPrismSite m n h)
    (P := RectangularPrismInteraction m n h)
    (rectangularPrismInteractionCoupling J beta)
    rectangularPrismInteractionMonomial
    (rectangularPrismInteractionCoupling_nonneg hJ hbeta)
    rectangularPrismInteractionMonomial_isSpinMonomial
    rectangularPrismInteractionMonomial_eq_one_or_neg_one
    (rectangularPrismDisorderSheet m n h)


theorem rectangularDobrushinFreeEnergy_nonneg
    {J beta : Real} (hJ : 0 <= J) (hbeta : 0 <= beta)
    (m n h : Nat) :
    0 <= rectangularDobrushinFreeEnergy J beta m n h := by
  unfold rectangularDobrushinFreeEnergy
  have htwist_pos : 0 < rectangularPrismTwistedPartition J beta m n h :=
    Z_pos _ _
  have hle := Real.log_le_log htwist_pos
    (rectangularPrismTwistedPartition_le_plusPartition hJ hbeta m n h)
  linarith

theorem rectangularDobrushinArray_nonneg
    {J beta : Real} (hJ : 0 <= J) (hbeta : 0 <= beta)
    (m n : Nat) :
    0 <= rectangularDobrushinArray J beta m n :=
  rectangularDobrushinFreeEnergy_nonneg hJ hbeta m n (max m n)


theorem rectangularPrismInterfaceSummand_abs_le_one
    {m n h : Nat} (sigma : RectangularPrismConfig m n h)
    (hh : 0 < h) (x : Fin m) (y : Fin n) :
    |rectangularPrismSpin sigma x y ⟨h, by omega⟩ *
        rectangularPrismSpin sigma x y ⟨h + 1, by omega⟩| <= 1 := by
  rw [abs_mul]
  exact mul_le_one₀ (abs_spin_le_one _ _) (abs_nonneg _)
    (abs_spin_le_one _ _)


theorem rectangularPrismInterfaceInteraction_abs_le
    {m n h : Nat} (sigma : RectangularPrismConfig m n h) :
    |rectangularPrismInterfaceInteraction sigma| <= (m : Real) * n := by
  rw [rectangularPrismInterfaceInteraction]
  split_ifs with hh
  · calc
      |∑ x : Fin m, ∑ y : Fin n,
          rectangularPrismSpin sigma x y ⟨h, by omega⟩ *
            rectangularPrismSpin sigma x y ⟨h + 1, by omega⟩| <=
          ∑ x : Fin m, |∑ y : Fin n,
            rectangularPrismSpin sigma x y ⟨h, by omega⟩ *
              rectangularPrismSpin sigma x y ⟨h + 1, by omega⟩| := by
        simpa using Finset.abs_sum_le_sum_abs
          (fun x : Fin m => ∑ y : Fin n,
            rectangularPrismSpin sigma x y ⟨h, by omega⟩ *
              rectangularPrismSpin sigma x y ⟨h + 1, by omega⟩)
          Finset.univ
      _ <= ∑ x : Fin m, ∑ y : Fin n,
          |rectangularPrismSpin sigma x y ⟨h, by omega⟩ *
            rectangularPrismSpin sigma x y ⟨h + 1, by omega⟩| := by
        apply Finset.sum_le_sum
        intro x _
        simpa using Finset.abs_sum_le_sum_abs
          (fun y : Fin n =>
            rectangularPrismSpin sigma x y ⟨h, by omega⟩ *
              rectangularPrismSpin sigma x y ⟨h + 1, by omega⟩)
          Finset.univ
      _ <= ∑ _x : Fin m, ∑ _y : Fin n, (1 : Real) := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro y _
        exact rectangularPrismInterfaceSummand_abs_le_one sigma hh x y
      _ = (m : Real) * n := by simp
  · simpa only [abs_zero] using
      mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)


theorem rectangularPrism_energy_sub_abs_le
    (J : Real) {m n h : Nat} (sigma : RectangularPrismConfig m n h) :
    |rectangularPrismPlusEnergy J sigma -
        rectangularPrismTwistedEnergy J sigma| <=
      2 * |J| * ((m : Real) * n) := by
  rw [rectangularPrismTwistedEnergy]
  have hI := rectangularPrismInterfaceInteraction_abs_le sigma
  calc
    |rectangularPrismPlusEnergy J sigma -
        (rectangularPrismPlusEnergy J sigma +
          2 * J * rectangularPrismInterfaceInteraction sigma)| =
        2 * |J| * |rectangularPrismInterfaceInteraction sigma| := by
      rw [show rectangularPrismPlusEnergy J sigma -
          (rectangularPrismPlusEnergy J sigma +
            2 * J * rectangularPrismInterfaceInteraction sigma) =
          -(2 * J * rectangularPrismInterfaceInteraction sigma) by ring,
        abs_neg, abs_mul, abs_mul]
      norm_num
    _ <= 2 * |J| * ((m : Real) * n) := by gcongr


theorem rectangularDobrushinFreeEnergy_abs_le
    (J beta : Real) (m n h : Nat) :
    |rectangularDobrushinFreeEnergy J beta m n h| <=
      2 * |beta| * |J| * ((m : Real) * n) := by
  have hdist := logZ_dist_le beta
    (rectangularPrismPlusEnergy J : RectangularPrismConfig m n h -> Real)
    (rectangularPrismTwistedEnergy J : RectangularPrismConfig m n h -> Real)
    (2 * |J| * ((m : Real) * n))
    (rectangularPrism_energy_sub_abs_le J)
  simp only [rectangularDobrushinFreeEnergy, rectangularPrismPlusPartition,
    rectangularPrismTwistedPartition]
  convert hdist using 1
  ring


theorem rectangularDobrushinArray_le_area
    (J beta : Real) (m n : Nat) :
    rectangularDobrushinArray J beta m n <=
      (2 * |beta| * |J|) * (m : Real) * n := by
  exact le_trans (le_abs_self _) (by
    simpa [rectangularDobrushinArray, mul_assoc] using
      rectangularDobrushinFreeEnergy_abs_le J beta m n (max m n))

end
end StatMech.Ising
