/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentMixingErgodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentFiniteMarginals
import Def.StatisticalMechanics.Code.FrontierB.CurrentMixingErgodicity.Part2
open MeasureTheory Set
open scoped ENNReal symmDiff


namespace StatMech.FrontierB

variable {E H : Type*} [Group H] [MulAction H E]


theorem current_selfMixing_of_cylinderPairMixing [Countable E]
    {mu : Measure (InfiniteCurrentConfig E)}
    (hmix : CurrentCylinderPairMixing (H := H) mu) :
    CurrentSelfMixing (H := H) mu := by
  intro A hA epsilon hepsilon
  obtain ⟨g, hg⟩ := hmix {A} (by
    intro B hB
    simpa only [Finset.mem_singleton.mp hB] using hA) epsilon hepsilon
  refine ⟨g, ?_⟩
  simpa [pow_two] using hg A (by simp) A (by simp)


theorem current_isErgodic_of_cylinderPairMixing [Countable E]
    {mu : Measure (InfiniteCurrentConfig E)} [IsProbabilityMeasure mu]
    (hmu : CurrentIsTranslationInvariant (H := H) mu)
    (hmix : CurrentCylinderPairMixing (H := H) mu) :
    CurrentIsErgodic (H := H) mu :=
  current_isErgodic_of_selfMixing hmu
    (current_selfMixing_of_cylinderPairMixing hmix)

end StatMech.FrontierB
