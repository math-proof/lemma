/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Foundations.CondDistribution.Part4
open MeasureTheory ProbabilityTheory MeasurableSpace


namespace StatMech

section ConfigSpace

variable {E : Type*} [Countable E]


instance isMarkovKernel_gibbsConditional
    (μ : Measure (ConfigSpace E)) [IsFiniteMeasure μ] (Λ : Set E) :
    @IsMarkovKernel (ConfigSpace E) (ConfigSpace E) (outsideSigma Λ) _ (gibbsConditional μ Λ) := by
  unfold gibbsConditional
  exact isMarkovKernel_regularCondDistrib μ (outsideSigma Λ)


end ConfigSpace
end StatMech
