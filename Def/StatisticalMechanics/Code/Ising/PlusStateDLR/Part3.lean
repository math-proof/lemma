/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplex.Part3
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtreme
import Theorem.StatisticalMechanics.Code.Ising.PlusStateDLR.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


def FVConsistency (d : ℕ) (β h : ℝ) : Prop :=
  ∀ (n m : ℕ), n ≤ m → ∀ f : ConfigSpace (Site d) →ᵇ ℝ,
    ∫ ω, specApply n (bondFinsetTouch d n) β h (f : ConfigSpace (Site d) → ℝ) ω
        ∂(plusMeasure d m β h : Measure (ConfigSpace (Site d)))
      = ∫ ω, f ω ∂(plusMeasure d m β h : Measure (ConfigSpace (Site d)))


end Ising
end StatMech
