/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Structure.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part2


namespace StatMech

namespace Exact3D

namespace StableBlockWithRemainder

noncomputable def ofLinearRowSum {n : ℕ}
    (linear : Fin n → Fin n → ℝ) {enclosure : RatInterval.IntervalMatrix n n}
    (enclosure_sound : RatInterval.MatrixMem linear enclosure)
    (linear_contraction : RatInterval.RowSumContraction enclosure) :
    StableBlockWithRemainder n where
  linear := linear
  enclosure := enclosure
  enclosure_sound := enclosure_sound
  linear_contraction := linear_contraction
  remainder := fun _ _ => 0
  remainder_lipschitz := IntervalLipschitzConstant.zero
  remainder_bound := by
    intro x i
    have h :
        0 ≤ ((IntervalLipschitzConstant.zero.upper : ℚ) : ℝ) *
          RatInterval.supNormVec x := by
      exact mul_nonneg
        (by norm_num [IntervalLipschitzConstant.zero,
          IntervalLipschitzConstant.upper, RatInterval.point])
        (RatInterval.supNormVec_nonneg x)
    simpa [IntervalLipschitzConstant.upper] using h
  total_lt_one := by
    simpa [IntervalLipschitzConstant.zero, IntervalLipschitzConstant.upper,
      RatInterval.point] using linear_contraction.c_lt_one


noncomputable def step {n : ℕ} (S : StableBlockWithRemainder n)
    (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  RatInterval.matVec S.linear x i + S.remainder x i


end StableBlockWithRemainder
end Exact3D
end StatMech
