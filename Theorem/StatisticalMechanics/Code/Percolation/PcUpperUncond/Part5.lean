/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PcUpper.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Def.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part4
open MeasureTheory Filter Topology Finset Set SimpleGraph
open scoped NNReal ENNReal BigOperators


namespace StatMech

namespace Percolation

open StatMech.Lattice


theorem pcSummandTwo_eq (p : ℝ) (ℓ : ℕ) :
    pcSummandTwo p ℓ = 2 * ((ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ) := by
  unfold pcSummandTwo; push_cast; ring

theorem pcSummandTwo_nonneg {p : ℝ} (hp : p ≤ 1) (ℓ : ℕ) : 0 ≤ pcSummandTwo p ℓ := by
  unfold pcSummandTwo
  have : (0 : ℝ) ≤ 1 - p := by linarith
  positivity


theorem summable_pcSummandTwo (p : ℝ) (hx : ‖pcRatio p‖ < 1) : Summable (pcSummandTwo p) := by
  have hbase : Summable (fun ℓ : ℕ => (ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ) := by
    have heq : (fun ℓ : ℕ => (ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ)
        = (fun ℓ : ℕ => (ℓ : ℝ) * (pcRatio p) ^ ℓ) := funext (pcSummand_eq p)
    rw [heq]
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hx
    simpa using this
  have h2 : Summable (fun ℓ : ℕ => 2 * ((ℓ : ℝ) * (4 : ℝ) ^ ℓ * (1 - p) ^ ℓ)) := hbase.mul_left 2
  exact h2.congr (fun ℓ => (pcSummandTwo_eq p ℓ).symm)


theorem tsum_pcSummandTwo (p : ℝ) : ∑' ℓ : ℕ, pcSummandTwo p ℓ = 2 * pcUpperBound p := by
  unfold pcUpperBound
  rw [← tsum_mul_left]
  exact tsum_congr (fun ℓ => pcSummandTwo_eq p ℓ)


theorem ennSummand_eq_ofReal (p : ℝ≥0) (hp : p ≤ 1) (ℓ : ℕ) :
    ((2 * ℓ * 4 ^ ℓ : ℕ) : ℝ≥0∞) * ((1 - p : ℝ≥0) : ℝ≥0∞) ^ ℓ
      = ENNReal.ofReal (pcSummandTwo (p : ℝ) ℓ) := by
  have hpr : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hpow : ((1 - p : ℝ≥0) : ℝ≥0∞) ^ ℓ = ENNReal.ofReal ((1 - (p : ℝ)) ^ ℓ) := by
    rw [show ((1 - p : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((1 - p : ℝ≥0) : ℝ) from
          (ENNReal.ofReal_coe_nnreal).symm]
    rw [← ENNReal.ofReal_pow (by positivity)]
    congr 2
    rw [NNReal.coe_sub hp, NNReal.coe_one]
  unfold pcSummandTwo
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, hpow]


end Percolation
end StatMech
