/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKMixingClose
import Theorem.StatisticalMechanics.Code.FK.CylinderDecayClose.Part6
import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part2
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]


variable {μ : Measure (ConfigSpace E)} [IsProbabilityMeasure μ]

def fmu_PairMixing (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ (P : Finset (Finset E)) (δ : ℝ), 0 < δ →
    ∃ g : G, ∀ T ∈ P, ∀ T' ∈ P,
      |μ.real (fmu_multiOpen T ∩
          (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T')
        - μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T')| < δ


end FK
end StatMech
