/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalPhaseReduction.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part2


namespace StatMech.FrontierA

open scoped BigOperators


theorem kwRatVertex_clear_denominators
    {n : ℕ} (q : Fin n → ℚ × ℚ) :
    ∃ p : Fin n → ℤ × ℤ, ∀ i : Fin n,
      (kwRatCommonDenominator q : ℝ) * kwRatVertex q i =
        kwIntComplex (p i) := by
  choose x hx using fun i ↦ exists_int_eq_nat_mul_ratCast
    (q i).1 (kwRatCommonDenominator q)
      (kwRatCommonDenominator_first_den_dvd q i)
  choose y hy using fun i ↦ exists_int_eq_nat_mul_ratCast
    (q i).2 (kwRatCommonDenominator q)
      (kwRatCommonDenominator_second_den_dvd q i)
  refine ⟨fun i ↦ (x i, y i), ?_⟩
  intro i
  apply Complex.ext
  · simpa [kwRatVertex, kwRatComplex, kwIntComplex] using hx i
  · simpa [kwRatVertex, kwRatComplex, kwIntComplex] using hy i


end StatMech.FrontierA
