/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Def.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


theorem crf_vertical_to_horizontal (a b c d : ℤ) (ω : ConfigSpace (Sym2 (Site 2)))
    (h : VerticalCrossing ω a b c d) :
    HorizontalCrossing (crf_swapConfig ω) c d a b := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨⟨crf_swap (x : Site 2), (crf_mem_bottomSide_swap a b c d x).1 x.2⟩,
          ⟨crf_swap (y : Site 2), (crf_mem_topSide_swap a b c d y).1 y.2⟩, ?_⟩
  exact (hxy : (openSubgraphInduce 2 ω (rect a b c d)).Reachable _ _).map
    (crf_inducedHom a b c d ω)


theorem crf_horizontal_to_vertical (a b c d : ℤ) (ω : ConfigSpace (Sym2 (Site 2)))
    (h : HorizontalCrossing (crf_swapConfig ω) c d a b) :
    VerticalCrossing ω a b c d := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨⟨crf_swap (x : Site 2), by
            have := crf_mem_bottomSide_swap a b c d (crf_swap (x : Site 2))
            simp only [crf_swap_involutive] at this; exact this.2 x.2⟩,
          ⟨crf_swap (y : Site 2), by
            have := crf_mem_topSide_swap a b c d (crf_swap (y : Site 2))
            simp only [crf_swap_involutive] at this; exact this.2 y.2⟩, ?_⟩
  exact (hxy : (openSubgraphInduce 2 (crf_swapConfig ω) (rect c d a b)).Reachable _ _).map
    (crf_inducedHomInv a b c d ω)


theorem crf_verticalCrossingEvent_swap (a b c d : ℤ) :
    verticalCrossingEvent a b c d = crf_swapConfig ⁻¹' horizontalCrossingEvent c d a b := by
  ext ω
  simp only [Set.mem_preimage, mem_verticalCrossingEvent, mem_horizontalCrossingEvent]
  exact ⟨crf_vertical_to_horizontal a b c d ω, crf_horizontal_to_vertical a b c d ω⟩


theorem crf_verticalCrossing_eq_horizontal_swap (a b c d : ℤ)
    (hmeas : MeasurableSet (horizontalCrossingEvent c d a b)) :
    rba_selfDualMeasure.real (verticalCrossingEvent a b c d)
      = rba_selfDualMeasure.real (horizontalCrossingEvent c d a b) := by
  rw [crf_verticalCrossingEvent_swap a b c d,
    crf_swap_invariant.measureReal_preimage hmeas.nullMeasurableSet]


theorem crf_hrefl
    (hmeas : ∀ (k0 : ℕ), 2 ≤ k0 → ∀ n : ℤ, 0 < n →
      MeasurableSet (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n)) :
    ∀ (k0 : ℕ), 2 ≤ k0 → ∀ n : ℤ, 0 < n →
      rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n))
        = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n) :=
  fun k0 hk0 n hn =>
    crf_verticalCrossing_eq_horizontal_swap 0 n 0 ((k0 : ℤ) * n) (hmeas k0 hk0 n hn)


theorem crf_hrefl_fixed {k0 : ℕ}
    (hmeas : ∀ n : ℤ, 0 < n → MeasurableSet (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n)) :
    ∀ n : ℤ, 0 < n →
      rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 ((k0 : ℤ) * n))
        = rba_selfDualMeasure.real (horizontalCrossingEvent 0 ((k0 : ℤ) * n) 0 n) :=
  fun n hn =>
    crf_verticalCrossing_eq_horizontal_swap 0 n 0 ((k0 : ℤ) * n) (hmeas n hn)

end Universality
end StatMech
