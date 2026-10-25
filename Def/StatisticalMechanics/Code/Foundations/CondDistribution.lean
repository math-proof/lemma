/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
open MeasureTheory ProbabilityTheory MeasurableSpace


namespace StatMech

section SubSigma

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ] (m : MeasurableSpace Ω)


noncomputable def regularCondDistrib : @Kernel Ω Ω m mΩ :=
  condExpKernel (mΩ := mΩ) μ m


end SubSigma
end StatMech
