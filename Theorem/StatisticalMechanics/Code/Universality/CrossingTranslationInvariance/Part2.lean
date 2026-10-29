/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWAspectInduction
import Theorem.StatisticalMechanics.Code.Universality.RSWBxpAssembly.Part2
import Def.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part2
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


theorem cti_edgeEquiv_symm_apply (v : Site 2) (e : Sym2 (Site 2)) :
    (cti_edgeEquiv v).symm e = e.map (· + v) := by
  simp [cti_edgeEquiv, sym2Congr]


theorem cti_translateConfig_eq (v : Site 2) :
    translateConfig v = (Equiv.piCongrLeft (fun _ => Bool) (cti_edgeEquiv v)) := by
  funext ω e
  rw [translateConfig, Equiv.piCongrLeft_apply]
  simp [cti_edgeEquiv_symm_apply]


theorem cti_measurable_translateConfig (v : Site 2) :
    Measurable (translateConfig v) := by
  rw [cti_translateConfig_eq]
  exact (MeasurableEquiv.piCongrLeft (fun _ => Bool) (cti_edgeEquiv v)).measurable


theorem cti_map_translateConfig (v : Site 2) :
    Measure.map (translateConfig v) rba_selfDualMeasure = rba_selfDualMeasure := by
  rw [cti_translateConfig_eq, rba_selfDualMeasure]
  unfold bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) => bernoulliMeasure (2⁻¹ : NNReal) half_le_one) (cti_edgeEquiv v)


theorem cti_selfDual_shift_invariant (v : Site 2) :
    MeasurePreserving (translateConfig v) rba_selfDualMeasure rba_selfDualMeasure :=
  ⟨cti_measurable_translateConfig v, cti_map_translateConfig v⟩


theorem cti_isOpenEdge_translate (t : Site 2) (ω : ConfigSpace (Sym2 (Site 2)))
    (x y : Site 2) :
    IsOpenEdge 2 (translateConfig t ω) x y ↔ IsOpenEdge 2 ω (x + t) (y + t) := by
  unfold IsOpenEdge
  have hadjiff : (hypercubicLattice 2).Adj x y ↔ (hypercubicLattice 2).Adj (x + t) (y + t) := by
    rw [hypercubicLattice_adj, hypercubicLattice_adj]
    constructor <;> intro h <;> rw [← h] <;>
      refine Finset.sum_congr rfl (fun i _ => ?_) <;> simp [Pi.add_apply]
  have hopeniff : (translateConfig t ω) s(x, y) = true ↔ ω s(x + t, y + t) = true := by
    rw [translateConfig_apply]
    rw [show (s(x, y) : Sym2 (Site 2)).map (· + t) = s(x + t, y + t) from Sym2.map_mk _ _ _]
  rw [hadjiff, hopeniff]


theorem cti_mem_rect_translate (a b c d : ℤ) (t : Site 2) (x : Site 2) :
    x ∈ rect a b c d ↔ (x + t) ∈ rect (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
  simp only [mem_rect, Pi.add_apply]
  constructor <;> intro h <;> exact ⟨by omega, by omega, by omega, by omega⟩


theorem cti_mem_leftSide_translate (a b c d : ℤ) (t : Site 2) (x : Site 2) :
    x ∈ leftSide a b c d ↔ (x + t) ∈ leftSide (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
  simp only [mem_leftSide, mem_rect, Pi.add_apply]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩


theorem cti_mem_rightSide_translate (a b c d : ℤ) (t : Site 2) (x : Site 2) :
    x ∈ rightSide a b c d ↔ (x + t) ∈ rightSide (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
  simp only [mem_rightSide, mem_rect, Pi.add_apply]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩


theorem cti_mem_bottomSide_translate (a b c d : ℤ) (t : Site 2) (x : Site 2) :
    x ∈ bottomSide a b c d ↔ (x + t) ∈ bottomSide (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
  simp only [mem_bottomSide, mem_rect, Pi.add_apply]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩


theorem cti_mem_topSide_translate (a b c d : ℤ) (t : Site 2) (x : Site 2) :
    x ∈ topSide a b c d ↔ (x + t) ∈ topSide (a + t 0) (b + t 0) (c + t 1) (d + t 1) := by
  simp only [mem_topSide, mem_rect, Pi.add_apply]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩


end Universality
end StatMech
