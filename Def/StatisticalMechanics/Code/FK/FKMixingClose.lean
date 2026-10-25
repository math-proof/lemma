/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.Ergodicity
import Theorem.StatisticalMechanics.Code.FK.IvPropertiesFull
import Theorem.StatisticalMechanics.Code.FK.FKLimitsClose.Part3
import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped ENNReal symmDiff

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]


def fmc_SelfMixing [Countable E] (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ A ∈ measurableCylinders (fun _ : E => Bool), ∀ ε : ℝ, 0 < ε →
    ∃ g : G, |μ.real (A ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' A)
      - (μ.real A) ^ 2| < ε


end FK
end StatMech
