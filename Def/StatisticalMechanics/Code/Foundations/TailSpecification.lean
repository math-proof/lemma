/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/TailSpecification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.AeTailInvariant.Part4
import Theorem.StatisticalMechanics.Code.Foundations.TailSpecification
open MeasureTheory ProbabilityTheory MeasurableSpace Set
open scoped ENNReal

set_option linter.unusedSectionVars false


namespace StatMech

open ConfigSpace

variable {E : Type*} [Countable E]


def IsTailSpecificationState (window : ℕ → Set E)
    (K : ∀ n, @Kernel (ConfigSpace E) (ConfigSpace E)
      (outsideSigma (window n)) inferInstance)
    (mu : Measure (ConfigSpace E)) [IsFiniteMeasure mu] : Prop :=
  ∀ n, (mu.trim (outsideSigma_le (window n))) ⊗ₘ K n =
    @Measure.map (ConfigSpace E) (ConfigSpace E × ConfigSpace E) _
      ((outsideSigma (window n)).prod inferInstance)
      (fun omega => (id omega, id omega)) mu

end StatMech
