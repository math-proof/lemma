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
import Def.StatisticalMechanics.Code.FrontierB.InfiniteCurrentTopology.Part6
open Filter MeasureTheory Topology


namespace StatMech

namespace FrontierB

theorem independentSuperposedTraceLaw_comm {E : Type*} [Countable E]
    (mu nu : ProbabilityMeasure (InfiniteCurrentConfig E)) :
    independentSuperposedTraceLaw mu nu =
      independentSuperposedTraceLaw nu mu := by
  unfold independentSuperposedTraceLaw
  apply Subtype.ext
  change Measure.map (@superposedCurrentTrace E)
      ((mu : Measure _).prod (nu : Measure _)) =
    Measure.map (@superposedCurrentTrace E)
      ((nu : Measure _).prod (mu : Measure _))
  rw [← Measure.prod_swap]
  rw [Measure.map_map continuous_superposedCurrentTrace.measurable measurable_swap]
  congr 1
  funext z e
  rcases z with ⟨a, b⟩
  simp [Function.comp_apply, superposedCurrentTrace, Nat.add_comm]


theorem independentSuperposedTraceLaw_tendsto {E : Type*} [Countable E]
    {mu nu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
    {muLim nuLim : ProbabilityMeasure (InfiniteCurrentConfig E)}
    (hmu : WeakCurrentConverges mu muLim)
    (hnu : WeakCurrentConverges nu nuLim) :
    Tendsto (fun k => independentSuperposedTraceLaw (mu k) (nu k)) atTop
      (nhds (independentSuperposedTraceLaw muLim nuLim)) := by
  have hpair : Tendsto (fun k => (mu k, nu k)) atTop (nhds (muLim, nuLim)) :=
    hmu.prodMk_nhds hnu
  have hprod : Tendsto (fun k => (mu k).prod (nu k)) atTop
      (nhds (muLim.prod nuLim)) :=
    ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp hpair
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun k => (mu k).prod (nu k)) (muLim.prod nuLim) hprod
      continuous_superposedCurrentTrace


end FrontierB
end StatMech
