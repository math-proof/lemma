/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part6
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleTranslationClosure
open MeasureTheory SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem bdcTorusThinCrossing_subset_translationClosure
    (L alpha n : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L)
    (h : bdcTorusThinCrossing L alpha n omega) :
    bdcTorusThinCrossingTranslationClosure L alpha n omega := by
  refine ⟨0, ?_⟩
  simpa using h


theorem bdcTorusThinCrossingTranslationClosure_translate_iff
    (L alpha n : ℕ) [Fact (2 < L)]
    (s : Site 2) (omega : TorusAmbientConfig L) :
    bdcTorusThinCrossingTranslationClosure L alpha n
        (torusAmbientTranslateConfig L s omega) ↔
      bdcTorusThinCrossingTranslationClosure L alpha n omega := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t + s, ?_⟩
    rw [torusAmbientTranslateConfig_add] at ht
    exact ht
  · rintro ⟨t, ht⟩
    refine ⟨t - s, ?_⟩
    rw [torusAmbientTranslateConfig_add]
    convert ht using 1
    congr 2
    ext i
    simp


end StatMech.BeffaraDC
