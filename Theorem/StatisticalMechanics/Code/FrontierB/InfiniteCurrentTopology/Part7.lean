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
import Def.StatisticalMechanics.Code.FrontierB.InfiniteCurrentTopology.Part7
open Filter MeasureTheory Topology


namespace StatMech

namespace FrontierB

theorem measurable_currentShift {E H : Type*} [Group H] [MulAction H E]
    (g : H) : Measurable (currentShift g : InfiniteCurrentConfig E → InfiniteCurrentConfig E) :=
  measurable_pi_lambda _ fun e => measurable_pi_apply (g⁻¹ • e)

theorem continuous_currentShift {E H : Type*} [Group H] [MulAction H E]
    (g : H) : Continuous (currentShift g : InfiniteCurrentConfig E → InfiniteCurrentConfig E) :=
  continuous_pi fun e => continuous_apply (g⁻¹ • e)


end FrontierB
end StatMech
