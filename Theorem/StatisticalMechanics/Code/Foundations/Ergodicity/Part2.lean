/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Ergodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
open MeasureTheory


namespace StatMech

namespace ConfigSpace

variable {E : Type*} {G : Type*}

section Group

variable [Group G] [MulAction G E]


variable {μ : Measure (ConfigSpace E)}


lemma IsErgodic.isTranslationInvariant (h : IsErgodic (G := G) μ) :
    IsTranslationInvariant (G := G) μ := h.1


lemma IsTranslationInvariant.map_eq (h : IsTranslationInvariant (G := G) μ) (g : G) :
    Measure.map (shift g : ConfigSpace E → ConfigSpace E) μ = μ := (h g).map_eq


lemma IsTranslationInvariant.measure_preimage (h : IsTranslationInvariant (G := G) μ)
    (g : G) {s : Set (ConfigSpace E)} (hs : MeasurableSet s) :
    μ ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s) = μ s :=
  (h g).measure_preimage hs.nullMeasurableSet

end Group
end ConfigSpace
end StatMech
