/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTI.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Theorem.StatisticalMechanics.Code.Ising.AeTailInvariantClose.Part2
import Theorem.StatisticalMechanics.Code.FK.FKErgodicFull.Part2
import Def.StatisticalMechanics.Code.Ising.PlusStateTI
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


theorem pst_integral_plusShifted (β h : ℝ) (g : Multiplicative (Site d)) (n : ℕ)
    (f : ConfigSpace (Site d) →ᵇ ℝ) :
    (∫ x, f x ∂((pst_plusShiftedFinite β h g n : ProbabilityMeasure _) : Measure _))
      = ∫ x, f (shift g x)
          ∂((plusMeasure d n β h : ProbabilityMeasure _) : Measure _) := by
  unfold pst_plusShiftedFinite
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_shift g).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]


theorem pst_integral_minusShifted (β h : ℝ) (g : Multiplicative (Site d)) (n : ℕ)
    (f : ConfigSpace (Site d) →ᵇ ℝ) :
    (∫ x, f x ∂((pst_minusShiftedFinite β h g n : ProbabilityMeasure _) : Measure _))
      = ∫ x, f (shift g x)
          ∂((minusMeasure d n β h : ProbabilityMeasure _) : Measure _) := by
  unfold pst_minusShiftedFinite
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_shift g).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]


end Ising
end StatMech
