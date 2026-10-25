/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalPhaseReduction.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization


namespace StatMech.FrontierA

open scoped BigOperators


theorem kwRatCommonDenominator_pos {n : ℕ} (q : Fin n → ℚ × ℚ) :
    0 < kwRatCommonDenominator q := by
  unfold kwRatCommonDenominator
  exact Finset.prod_pos fun i _ ↦ Nat.mul_pos (q i).1.den_pos (q i).2.den_pos

theorem kwRatCommonDenominator_first_den_dvd
    {n : ℕ} (q : Fin n → ℚ × ℚ) (i : Fin n) :
    (q i).1.den ∣ kwRatCommonDenominator q := by
  apply dvd_trans (dvd_mul_right _ _)
  exact Finset.dvd_prod_of_mem
    (fun j : Fin n ↦ (q j).1.den * (q j).2.den) (Finset.mem_univ i)

theorem kwRatCommonDenominator_second_den_dvd
    {n : ℕ} (q : Fin n → ℚ × ℚ) (i : Fin n) :
    (q i).2.den ∣ kwRatCommonDenominator q := by
  apply dvd_trans (dvd_mul_left _ _)
  exact Finset.dvd_prod_of_mem
    (fun j : Fin n ↦ (q j).1.den * (q j).2.den) (Finset.mem_univ i)


theorem exists_int_eq_nat_mul_ratCast (q : ℚ) (D : ℕ) (hD : q.den ∣ D) :
    ∃ z : ℤ, (D : ℝ) * (q : ℝ) = (z : ℝ) := by
  obtain ⟨k, rfl⟩ := hD
  refine ⟨(k : ℤ) * q.num, ?_⟩
  rw [Rat.cast_def]
  push_cast
  field_simp


end StatMech.FrontierA
