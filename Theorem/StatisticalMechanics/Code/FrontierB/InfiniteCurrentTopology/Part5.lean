/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Def.StatisticalMechanics.Code.FrontierB.InfiniteCurrentTopology.Part5
open Filter MeasureTheory Topology


namespace StatMech

namespace FrontierB

theorem superposedCurrentTrace_apply {E : Type*}
    (n : InfiniteCurrentConfig E × InfiniteCurrentConfig E) (e : E) :
    superposedCurrentTrace n e = true ↔ 0 < n.1 e + n.2 e := by
  simp [superposedCurrentTrace]

theorem continuous_superposedCurrentTrace {E : Type*} :
    Continuous
      (superposedCurrentTrace :
        InfiniteCurrentConfig E × InfiniteCurrentConfig E → ConfigSpace E) := by
  refine continuous_pi fun e => ?_
  exact (continuous_of_discreteTopology
    (f := fun k : ℕ => decide (0 < k))).comp
      (((continuous_apply e).comp continuous_fst).add
        ((continuous_apply e).comp continuous_snd))


end FrontierB
end StatMech
