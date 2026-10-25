/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Foundations.CondDistribution
open MeasureTheory ProbabilityTheory MeasurableSpace


namespace StatMech

section Map

variable {Ω β : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [mβ : MeasurableSpace β] (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → β)


noncomputable def condDistribGiven : Kernel β Ω := condDistrib id X μ


end Map
end StatMech
