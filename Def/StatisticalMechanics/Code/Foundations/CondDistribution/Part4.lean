/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Foundations.CondDistribution.Part3
open MeasureTheory ProbabilityTheory MeasurableSpace


namespace StatMech

section ConfigSpace

variable {E : Type*} [Countable E]


noncomputable def gibbsConditional (μ : Measure (ConfigSpace E)) [IsFiniteMeasure μ]
    (Λ : Set E) : @Kernel (ConfigSpace E) (ConfigSpace E) (outsideSigma Λ) _ :=
  regularCondDistrib μ (outsideSigma Λ)


end ConfigSpace
end StatMech
