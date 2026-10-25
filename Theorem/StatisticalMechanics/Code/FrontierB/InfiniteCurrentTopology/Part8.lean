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
import Def.StatisticalMechanics.Code.FrontierB.InfiniteCurrentTopology.Part8
open Filter MeasureTheory Topology


namespace StatMech

namespace FrontierB

theorem currentTrace_semiconj {E H : Type*} [Group H] [MulAction H E]
    (g : H) : Function.Semiconj
      (currentTrace : InfiniteCurrentConfig E → ConfigSpace E)
      (currentShift g) (ConfigSpace.shift g) := by
  intro n
  rfl


theorem currentTrace_measurePreserving {E : Type*} [Countable E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E)) :
    MeasurePreserving currentTrace (mu : Measure (InfiniteCurrentConfig E))
      (currentTraceLaw mu : Measure (ConfigSpace E)) := by
  change MeasurePreserving currentTrace (mu : Measure (InfiniteCurrentConfig E))
    (Measure.map currentTrace (mu : Measure (InfiniteCurrentConfig E)))
  exact continuous_currentTrace.measurable.measurePreserving _


theorem CurrentIsTranslationInvariant.trace {E H : Type*} [Countable E]
    [Group H] [MulAction H E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (h : CurrentIsTranslationInvariant (H := H)
      (mu : Measure (InfiniteCurrentConfig E))) :
    ConfigSpace.IsTranslationInvariant (G := H)
      (currentTraceLaw mu : Measure (ConfigSpace E)) := by
  intro g
  exact (currentTrace_measurePreserving mu).of_semiconj (h g)
    (currentTrace_semiconj g) (ConfigSpace.measurable_shift g)


theorem CurrentIsErgodic.trace {E H : Type*} [Countable E]
    [Group H] [MulAction H E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (h : CurrentIsErgodic (H := H)
      (mu : Measure (InfiniteCurrentConfig E))) :
    ConfigSpace.IsErgodic (G := H)
      (currentTraceLaw mu : Measure (ConfigSpace E)) := by
  refine ⟨h.1.trace mu, ?_⟩
  intro s hs hinv
  have hfactor := currentTrace_measurePreserving mu
  have hpre : MeasurableSet (currentTrace ⁻¹' s) :=
    continuous_currentTrace.measurable hs
  have hpreInv : ∀ g : H, (currentShift g) ⁻¹' (currentTrace ⁻¹' s) =
      currentTrace ⁻¹' s := by
    intro g
    ext n
    change ConfigSpace.shift g (currentTrace n) ∈ s ↔ currentTrace n ∈ s
    exact Set.ext_iff.mp (hinv g) (currentTrace n)
  rcases h.2 (currentTrace ⁻¹' s) hpre hpreInv with hzero | hfull
  · left
    rw [← hfactor.measure_preimage hs.nullMeasurableSet]
    exact hzero
  · right
    rw [← hfactor.measure_preimage hs.nullMeasurableSet,
      ← hfactor.measure_preimage MeasurableSet.univ.nullMeasurableSet]
    exact hfull

end FrontierB
end StatMech
