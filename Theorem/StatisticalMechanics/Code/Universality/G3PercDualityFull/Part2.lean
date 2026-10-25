/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/G3PercDualityFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Universality.STT.Part4
import Instance.StatisticalMechanics.Code.Universality.G3PercDualityFull
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice


theorem selfDual_density_iff (p : ℝ≥0) (hp : p ≤ 1) : 1 - p = p ↔ p = 2⁻¹ := by
  constructor
  · intro h
    apply NNReal.coe_injective
    have hr : (1 : ℝ) - (p : ℝ) = (p : ℝ) := by
      have := congrArg NNReal.toReal h
      rwa [NNReal.coe_sub hp, NNReal.coe_one] at this
    push_cast
    linarith
  · intro h
    subst h
    apply NNReal.coe_injective
    rw [NNReal.coe_sub (by norm_num)]
    push_cast
    norm_num


theorem selfDual_density_iff_real (p : ℝ) : 1 - p = p ↔ p = 1 / 2 := by
  constructor <;> intro h <;> linarith


theorem one_sub_half_eq : (1 : ℝ≥0) - 2⁻¹ = 2⁻¹ :=
  (selfDual_density_iff 2⁻¹ half_le_one).2 rfl


theorem bernoulliProductMeasure_selfDual_half :
    Measure.map dualConfig (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one)
      = bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one := by
  rw [map_dualConfig (2⁻¹ : ℝ≥0) half_le_one]
  congr 1
  exact one_sub_half_eq


theorem selfDual_point_unique (p : ℝ≥0) (hp : p ≤ 1) :
    (1 - p = p ↔ p = 2⁻¹) ∧
      Measure.map dualConfig (bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one)
        = bernoulliProductMeasure (2⁻¹ : ℝ≥0) half_le_one :=
  ⟨selfDual_density_iff p hp, bernoulliProductMeasure_selfDual_half⟩


theorem map_dualConfig_dualConfig (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map dualConfig (Measure.map dualConfig (bernoulliProductMeasure p hp))
      = bernoulliProductMeasure p hp := by
  rw [map_dualConfig p hp, map_dualConfig (1 - p) tsub_le_self]
  congr 1
  apply NNReal.coe_injective
  rw [NNReal.coe_sub tsub_le_self, NNReal.coe_sub hp, NNReal.coe_one]
  ring


end Universality
end StatMech
