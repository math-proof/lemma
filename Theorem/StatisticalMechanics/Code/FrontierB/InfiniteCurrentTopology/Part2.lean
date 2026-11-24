module
public import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Def.StatisticalMechanics.Code.FrontierB.InfiniteCurrentTopology.Part2
open Filter MeasureTheory Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FrontierB

theorem WeakCurrentConverges.marginal {E : Type*} [Countable E]
    {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
    {nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (h : WeakCurrentConverges mu nu) (S : Finset E) :
    Tendsto (fun k => currentMarginal (mu k) S) atTop
      (nhds (currentMarginal nu S)) := by
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    mu nu h (continuous_restrictCurrent S)


end FrontierB
end StatMech
