/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Magnetization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Ising.Magnetization
open MeasureTheory


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


theorem abs_magnetization_le_one (d : ℕ) (β : ℝ) : |magnetization d β| ≤ 1 := by
  rw [magnetization, ← Real.norm_eq_abs]
  haveI : IsProbabilityMeasure (plusState d β 0 : Measure (ConfigSpace (Site d))) :=
    (plusState d β 0).2
  calc ‖∫ ω, spin ω (origin d) ∂(plusState d β 0 : Measure (ConfigSpace (Site d)))‖
      ≤ 1 * (plusState d β 0 : Measure (ConfigSpace (Site d))).real Set.univ := by
        refine norm_integral_le_of_norm_le_const ?_
        filter_upwards with ω
        simpa using abs_spin_le_one ω (origin d)
    _ = 1 := by simp


theorem magnetization_le_one (d : ℕ) (β : ℝ) : magnetization d β ≤ 1 :=
  (abs_le.mp (abs_magnetization_le_one d β)).2


theorem neg_one_le_magnetization (d : ℕ) (β : ℝ) : -1 ≤ magnetization d β :=
  (abs_le.mp (abs_magnetization_le_one d β)).1


end Ising
end StatMech
