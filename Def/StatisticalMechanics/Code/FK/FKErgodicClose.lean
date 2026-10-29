/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKErgodicClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FKLimitsClose.Part3
import Theorem.StatisticalMechanics.Code.FK.MonotoneVolumeLimit
import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKErgodicClose
open MeasureTheory ProbabilityTheory Filter Topology
open StatMech.ConfigSpace StatMech.Lattice
open scoped ENNReal

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {E : Type*} {G : Type*} [Group G] [MulAction G E]


def IsInvariantExtremePoint (μ : Measure (ConfigSpace E)) : Prop :=
  IsTranslationInvariant (G := G) μ ∧ IsProbabilityMeasure μ ∧
    ∀ (ν₁ ν₂ : Measure (ConfigSpace E)) (a b : ENNReal),
      IsTranslationInvariant (G := G) ν₁ → IsTranslationInvariant (G := G) ν₂ →
        IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
          0 < a → 0 < b → a + b = 1 → μ = a • ν₁ + b • ν₂ → ν₁ = ν₂


end FK
end StatMech
