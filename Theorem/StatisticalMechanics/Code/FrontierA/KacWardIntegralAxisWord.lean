/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part3
import Def.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisWord


namespace StatMech.FrontierA

open StatMech.Onsager.BaseCase


@[simp] theorem stepOf_kwHorizontalIntDirection_nonneg
    {x : ℤ} (hx : 0 ≤ x) :
    stepOf (kwHorizontalIntDirection x) = (1, 0) := by
  simp [kwHorizontalIntDirection, hx, stepOf]

@[simp] theorem stepOf_kwHorizontalIntDirection_neg
    {x : ℤ} (hx : x < 0) :
    stepOf (kwHorizontalIntDirection x) = (-1, 0) := by
  simp [kwHorizontalIntDirection, not_le.mpr hx, stepOf]

@[simp] theorem stepOf_kwVerticalIntDirection_nonneg
    {y : ℤ} (hy : 0 ≤ y) :
    stepOf (kwVerticalIntDirection y) = (0, 1) := by
  simp [kwVerticalIntDirection, hy, stepOf]

@[simp] theorem stepOf_kwVerticalIntDirection_neg
    {y : ℤ} (hy : y < 0) :
    stepOf (kwVerticalIntDirection y) = (0, -1) := by
  simp [kwVerticalIntDirection, not_le.mpr hy, stepOf]

theorem sum_replicate_horizontalDirection (x : ℤ) :
    (List.replicate x.natAbs
      (stepOf (kwHorizontalIntDirection x))).sum = (x, 0) := by
  by_cases hx : 0 ≤ x
  · rw [stepOf_kwHorizontalIntDirection_nonneg hx]
    simp only [List.sum_replicate, nsmul_eq_mul]
    apply Prod.ext
    · simp only [Prod.fst_mul]
      simp [abs_of_nonneg hx]
    · simp
  · have hxneg : x < 0 := lt_of_not_ge hx
    rw [stepOf_kwHorizontalIntDirection_neg hxneg]
    simp only [List.sum_replicate]
    apply Prod.ext
    · simp only [Prod.smul_fst]
      simp [abs_of_neg hxneg]
    · simp

theorem sum_replicate_verticalDirection (y : ℤ) :
    (List.replicate y.natAbs
      (stepOf (kwVerticalIntDirection y))).sum = (0, y) := by
  by_cases hy : 0 ≤ y
  · rw [stepOf_kwVerticalIntDirection_nonneg hy]
    simp only [List.sum_replicate]
    apply Prod.ext
    · simp
    · simp [abs_of_nonneg hy]
  · have hyneg : y < 0 := lt_of_not_ge hy
    rw [stepOf_kwVerticalIntDirection_neg hyneg]
    simp only [List.sum_replicate]
    apply Prod.ext
    · simp
    · simp [abs_of_neg hyneg]


theorem kwIntegralAxisWord_step_sum (v : ℤ × ℤ) :
    ((kwIntegralAxisWord v).map stepOf).sum = v := by
  rw [kwIntegralAxisWord, List.map_append, List.sum_append,
    List.map_replicate, List.map_replicate,
    sum_replicate_horizontalDirection, sum_replicate_verticalDirection]
  apply Prod.ext <;> simp

theorem kwIntegralAxisWord_length (v : ℤ × ℤ) :
    (kwIntegralAxisWord v).length = v.1.natAbs + v.2.natAbs := by
  simp [kwIntegralAxisWord]


theorem kwIntegralAxisWord_ne_nil {v : ℤ × ℤ} (hv : v ≠ 0) :
    kwIntegralAxisWord v ≠ [] := by
  intro hnil
  have hsum := kwIntegralAxisWord_step_sum v
  rw [hnil] at hsum
  simpa using hv hsum.symm


end StatMech.FrontierA
