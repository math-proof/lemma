/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Theta.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Def.StatisticalMechanics.Code.Percolation.Theta
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice


@[simp]
theorem mem_percolationEvent {d : ℕ} {ω : ConfigSpace (Sym2 (Site d))} :
    ω ∈ percolationEvent d ↔ (StatMech.Lattice.cluster d ω (origin d)).Infinite :=
  Iff.rfl

@[simp]
theorem mem_subcriticalSet {d : ℕ} {p : ℝ≥0} :
    p ∈ subcriticalSet d ↔ ∃ hp : p ≤ 1, theta d p hp = 0 :=
  Iff.rfl


theorem theta_nonneg (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : 0 ≤ theta d p hp :=
  ENNReal.toReal_nonneg


theorem theta_le_one (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) : theta d p hp ≤ 1 := by
  unfold theta
  rw [Measure.real]
  refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
  rw [ENNReal.ofReal_one]
  exact prob_le_one

end Percolation
end StatMech
