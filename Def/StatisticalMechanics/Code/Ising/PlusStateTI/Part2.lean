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
import Theorem.StatisticalMechanics.Code.Ising.PlusStateTI
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


def pst_PlusIntegralShiftDecay (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f : ConfigSpace (Site d) →ᵇ ℝ,
    Tendsto (fun n =>
        (∫ x, f x ∂((plusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _))
          - (∫ x, f (shift g x)
              ∂((plusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _)))
      atTop (𝓝 0)


def pst_MinusIntegralShiftDecay (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ) : Prop :=
  ∀ f : ConfigSpace (Site d) →ᵇ ℝ,
    Tendsto (fun n =>
        (∫ x, f x ∂((minusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _))
          - (∫ x, f (shift g x)
              ∂((minusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _)))
      atTop (𝓝 0)


end Ising
end StatMech
