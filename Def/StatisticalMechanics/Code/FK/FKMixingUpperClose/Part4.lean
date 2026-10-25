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
import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part3
open MeasureTheory Filter Topology Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]


variable {μ : Measure (ConfigSpace E)} [IsProbabilityMeasure μ]

def fmu_GenMixing (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ (𝒜 : Finset (Set (ConfigSpace E))),
    (∀ A ∈ 𝒜, A ∈ measurableCylinders (fun _ : E => Bool)) →
    ∀ δ : ℝ, 0 < δ →
    ∃ g : G, ∀ A ∈ 𝒜, ∀ B ∈ 𝒜,
      |μ.real (A ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' B)
        - μ.real A * μ.real B| < δ


end FK
end StatMech
