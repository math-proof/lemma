/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part6
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleTranslationClosure.Part7
open MeasureTheory SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem bdcTorusThinCrossingTranslationClosure_iff_pullback_mem_expanded
    (L alpha n : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) :
    bdcTorusThinCrossingTranslationClosure L alpha n omega ↔
      torusPlanarPullback L omega ∈
        bdcLongRectangleTranslationExpandedUnion alpha n := by
  constructor
  · rintro ⟨t, ht⟩
    rw [bdcTorusThinCrossing_iff_pullback_mem_union,
      torusPlanarPullback_translate] at ht
    exact Set.mem_iUnion.2 ⟨t, ht⟩
  · intro h
    obtain ⟨t, ht⟩ := Set.mem_iUnion.1 h
    refine ⟨t, ?_⟩
    rw [bdcTorusThinCrossing_iff_pullback_mem_union,
      torusPlanarPullback_translate]
    exact ht


theorem bdcTorusThinCrossingTranslationClosure_iff_pullback_mem_finiteExpanded
    (L alpha n : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) :
    bdcTorusThinCrossingTranslationClosure L alpha n omega ↔
      torusPlanarPullback L omega ∈
        bdcLongRectangleTorusTranslationExpandedUnion L alpha n := by
  constructor
  · rintro ⟨t, ht⟩
    let u := torusReduceSite L t
    let s := bdcTorusCanonicalShift u
    have htranslate : torusAmbientTranslateConfig L t omega =
        torusAmbientTranslateConfig L s omega := by
      simpa [u, s] using
        torusAmbientTranslateConfig_eq_canonical L t omega
    rw [htranslate] at ht
    obtain ⟨k, hk⟩ := ht
    refine Set.mem_iUnion.2 ⟨(u, k), ?_⟩
    change translateConfig s (torusPlanarPullback L omega) ∈
      bdcLongRectangleEvent alpha n k
    rw [← torusPlanarPullback_translate]
    exact hk
  · intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h
    refine ⟨bdcTorusCanonicalShift j.1, ⟨j.2, ?_⟩⟩
    change translateConfig (bdcTorusCanonicalShift j.1)
      (torusPlanarPullback L omega) ∈
        bdcLongRectangleEvent alpha n j.2 at hj
    rw [torusPlanarPullback_translate]
    exact hj


end StatMech.BeffaraDC
