/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Ergodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity
open MeasureTheory


namespace StatMech

namespace ConfigSpace

variable {E : Type*} {G : Type*}

section Group

variable [Group G] [MulAction G E]


def IsTranslationInvariant (μ : Measure (ConfigSpace E)) : Prop :=
  ∀ g : G, MeasureTheory.MeasurePreserving (shift g : ConfigSpace E → ConfigSpace E) μ μ


def IsErgodic (μ : Measure (ConfigSpace E)) : Prop :=
  IsTranslationInvariant (G := G) μ ∧
    ∀ s : Set (ConfigSpace E), MeasurableSet s →
      (∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) →
        μ s = 0 ∨ μ s = μ Set.univ

end Group
end ConfigSpace
end StatMech
