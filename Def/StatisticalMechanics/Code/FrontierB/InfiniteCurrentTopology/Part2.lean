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
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentTopology
open Filter MeasureTheory Topology


namespace StatMech

namespace FrontierB

noncomputable def currentMarginal {E : Type*} [Countable E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E)) (S : Finset E) :
    ProbabilityMeasure (↑S → ℕ) :=
  mu.map (continuous_restrictCurrent S).measurable.aemeasurable


end FrontierB
end StatMech
