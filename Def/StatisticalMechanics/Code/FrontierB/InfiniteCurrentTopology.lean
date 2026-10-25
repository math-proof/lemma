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
import Abbrev.StatisticalMechanics.Code.FrontierB.InfiniteCurrentTopology
open Filter MeasureTheory Topology


namespace StatMech

namespace FrontierB

def WeakCurrentConverges {E : Type*} [Countable E]
    (mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E))
    (nu : ProbabilityMeasure (InfiniteCurrentConfig E)) : Prop :=
  Tendsto mu atTop (nhds nu)


def restrictCurrent {E : Type*} (S : Finset E) (n : InfiniteCurrentConfig E) :
    ↑S → ℕ := fun e => n e.1

end FrontierB
end StatMech
