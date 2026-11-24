module
public import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Def.StatisticalMechanics.Code.FrontierB.InfiniteCurrentTopology.Part4
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

theorem WeakCurrentConverges.trace {E : Type*} [Countable E]
    {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
    {nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (h : WeakCurrentConverges mu nu) :
    Tendsto (fun k => currentTraceLaw (mu k)) atTop
      (nhds (currentTraceLaw nu)) := by
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    mu nu h continuous_currentTrace


end FrontierB
end StatMech
