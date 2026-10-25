/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/AeTailInvariantProve2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.AeTailInvariantClose.Part2
import Theorem.StatisticalMechanics.Code.Ising.GibbsExtremeClose
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Ising.AeTailInvariantProve2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


def IsDLRExtremePoint (β h : ℝ) (μ : Measure (ConfigSpace (Site d))) : Prop :=
  ∀ (ν₁ ν₂ : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂],
    IsDLRState d β h ν₁ → IsDLRState d β h ν₂ →
    ∀ (a b : ℝ≥0∞), 0 < a → 0 < b → a + b = 1 → a ≠ ⊤ → b ≠ ⊤ →
      μ = a • ν₁ + b • ν₂ → ν₁ = ν₂


end Ising
end StatMech
