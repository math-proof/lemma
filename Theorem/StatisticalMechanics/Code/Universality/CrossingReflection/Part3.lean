/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Def.StatisticalMechanics.Code.Universality.CrossingReflection.Part3
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


theorem crf_swapConfig_apply (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    crf_swapConfig ω e = ω (e.map crf_swap) := by
  rw [crf_swapConfig, Equiv.piCongrLeft_apply]; simp [crf_edgeEquiv_symm_apply]


theorem crf_measurable_swapConfig : Measurable crf_swapConfig :=
  (MeasurableEquiv.piCongrLeft (fun _ => Bool) crf_edgeEquiv).measurable


theorem crf_map_swapConfig :
    Measure.map crf_swapConfig rba_selfDualMeasure = rba_selfDualMeasure := by
  rw [crf_swapConfig, rba_selfDualMeasure]
  unfold bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) => bernoulliMeasure (2⁻¹ : NNReal) half_le_one) crf_edgeEquiv


theorem crf_swap_invariant :
    MeasurePreserving crf_swapConfig rba_selfDualMeasure rba_selfDualMeasure :=
  ⟨crf_measurable_swapConfig, crf_map_swapConfig⟩


theorem crf_isOpenEdge_swap (ω : ConfigSpace (Sym2 (Site 2))) (x y : Site 2) :
    IsOpenEdge 2 (crf_swapConfig ω) x y ↔ IsOpenEdge 2 ω (crf_swap x) (crf_swap y) := by
  unfold IsOpenEdge
  rw [crf_adj_swap x y]
  have hopen : (crf_swapConfig ω) s(x, y) = true ↔ ω s(crf_swap x, crf_swap y) = true := by
    rw [crf_swapConfig_apply,
      show (s(x, y) : Sym2 (Site 2)).map crf_swap = s(crf_swap x, crf_swap y) from
      Sym2.map_mk _ _ _]
  rw [hopen]


theorem crf_mem_rect_swap (a b c d : ℤ) (x : Site 2) :
    x ∈ rect a b c d ↔ (crf_swap x) ∈ rect c d a b := by
  simp only [mem_rect, crf_swap_zero, crf_swap_one]
  constructor <;> intro h <;> exact ⟨by omega, by omega, by omega, by omega⟩


theorem crf_mem_bottomSide_swap (a b c d : ℤ) (x : Site 2) :
    x ∈ bottomSide a b c d ↔ (crf_swap x) ∈ leftSide c d a b := by
  simp only [mem_bottomSide, mem_leftSide, mem_rect, crf_swap_zero, crf_swap_one]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩


theorem crf_mem_topSide_swap (a b c d : ℤ) (x : Site 2) :
    x ∈ topSide a b c d ↔ (crf_swap x) ∈ rightSide c d a b := by
  simp only [mem_topSide, mem_rightSide, mem_rect, crf_swap_zero, crf_swap_one]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩


end Universality
end StatMech
