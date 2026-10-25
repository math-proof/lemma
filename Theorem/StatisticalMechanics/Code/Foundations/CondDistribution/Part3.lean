/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CondDistribution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Foundations.CondDistribution.Part3
open MeasureTheory ProbabilityTheory MeasurableSpace


namespace StatMech

section ConfigSpace

variable {E : Type*} [Countable E]


omit [Countable E] in

theorem outsideSigma_le (Λ : Set E) :
    outsideSigma Λ ≤ (inferInstance : MeasurableSpace (ConfigSpace E)) :=
  iSup₂_le fun e _ => (ConfigSpace.measurable_eval e).comap_le


end ConfigSpace
end StatMech
