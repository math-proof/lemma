/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Foundations.CondDistribution
open MeasureTheory ProbabilityTheory MeasurableSpace


namespace StatMech

section SubSigma

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ] (m : MeasurableSpace Ω)


instance isMarkovKernel_regularCondDistrib :
    @IsMarkovKernel Ω Ω m mΩ (regularCondDistrib (mΩ := mΩ) μ m) := by
  unfold regularCondDistrib; infer_instance


end SubSigma
end StatMech
