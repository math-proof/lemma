/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/TailSpecification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.AeTailInvariant.Part4
import Theorem.StatisticalMechanics.Code.Foundations.TailSpecification.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set
open scoped ENNReal

set_option linter.unusedSectionVars false


namespace StatMech

open ConfigSpace

variable {E : Type*} [Countable E]


def IsTailSpecificationMeasure (window : ℕ → Set E)
    (K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E)
      (outsideSigma (window n)) inferInstance)
    (mu : Measure (ConfigSpace E)) : Prop :=
  ∃ _ : IsFiniteMeasure mu, IsTailSpecificationState window K mu


end StatMech
