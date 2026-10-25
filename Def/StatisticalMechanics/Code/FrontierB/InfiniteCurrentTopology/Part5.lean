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
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentTopology.Part4
open Filter MeasureTheory Topology


namespace StatMech

namespace FrontierB

def superposedCurrentTrace {E : Type*}
    (n : InfiniteCurrentConfig E × InfiniteCurrentConfig E) : ConfigSpace E :=
  fun e => decide (0 < n.1 e + n.2 e)

end FrontierB
end StatMech
