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
open MeasureTheory


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


theorem measurable_spin (x : Site d) :
    Measurable (fun ω : ConfigSpace (Site d) => spin ω x) := by
  have hmeas : Measurable (fun ω : ConfigSpace (Site d) => ω x) := measurable_pi_apply x
  simp only [spin]
  exact Measurable.ite (hmeas (measurableSet_singleton true)) measurable_const measurable_const


theorem integrable_spin (x : Site d) (μ : Measure (ConfigSpace (Site d)))
    [IsFiniteMeasure μ] :
    Integrable (fun ω : ConfigSpace (Site d) => spin ω x) μ := by
  refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const 1)
    (measurable_spin x).aestronglyMeasurable ?_
  filter_upwards with ω
  simpa using abs_spin_le_one ω x


end Ising
end StatMech
