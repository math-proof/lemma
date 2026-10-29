/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Def.StatisticalMechanics.Code.Percolation.PcUpper.Part2
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped NNReal ENNReal BigOperators


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


theorem theta_pos_of_contourBound {p : NNReal} (hp : p ≤ 1)
    (hContour : PcContourBound p hp) (hBound : pcUpperBound (p : ℝ) < 1) :
    0 < theta 2 p hp := by
  have h : 1 - theta 2 p hp ≤ pcUpperBound (p : ℝ) := hContour
  linarith


theorem not_mem_subcriticalSet_of_theta_pos {p : NNReal} (hp : p ≤ 1)
    (hθ : 0 < theta 2 p hp) : p ∉ subcriticalSet 2 := by
  intro hmem
  obtain ⟨hp', hzero⟩ := hmem
  
  rw [show hp' = hp from rfl] at hzero
  exact (ne_of_gt hθ) hzero


theorem pc_lt_one
    (hGeom : ∃ p₀ : ℝ, p₀ < 1 ∧
      ∀ (p : NNReal) (hp : p ≤ 1), (p₀ : ℝ) < (p : ℝ) → PcContourBound p hp) :
    pc 2 < 1 := by
  obtain ⟨p₁, hp₁lt, hp₁bound⟩ := exists_p_lt_one_pcUpperBound_lt_one
  obtain ⟨p₂, hp₂lt, hp₂geom⟩ := hGeom
  
  set t : ℝ := max (max p₁ p₂) 0 with ht
  have htlt : t < 1 := max_lt (max_lt hp₁lt hp₂lt) (by norm_num)
  have ht0 : (0 : ℝ) ≤ t := le_max_right _ _
  have hp₁t : p₁ ≤ t := le_trans (le_max_left _ _) (le_max_left _ _)
  have hp₂t : p₂ ≤ t := le_trans (le_max_right _ _) (le_max_left _ _)
  
  set s : ℝ := (t + 1) / 2 with hs
  have hts : t < s := by rw [hs]; linarith
  have hslt : s < 1 := by rw [hs]; linarith
  have hs0 : (0 : ℝ) ≤ s := by rw [hs]; linarith
  
  set sN : NNReal := s.toNNReal with hsN
  have hsNcoe : (sN : ℝ) = s := by rw [hsN]; exact Real.coe_toNNReal s hs0
  have hsN1 : sN ≤ 1 := by
    rw [hsN, ← Real.toNNReal_one]; exact Real.toNNReal_le_toNNReal hslt.le
  have hsNlt1 : sN < 1 := by
    rw [hsN, ← Real.toNNReal_one, Real.toNNReal_lt_toNNReal_iff_of_nonneg hs0]
    exact hslt
  
  have hub : ∀ q ∈ subcriticalSet 2, q ≤ sN := by
    intro q hq
    by_contra hcon
    push Not at hcon
    
    have hqreal : s < (q : ℝ) := by
      have hsq : (sN : ℝ) < (q : ℝ) := by exact_mod_cast hcon
      rwa [hsNcoe] at hsq
    have hq1 : q ≤ 1 := hq.1
    
    have hp₁q : p₁ < (q : ℝ) := lt_of_le_of_lt (le_trans hp₁t hts.le) hqreal
    have hp₂q : (p₂ : ℝ) < (q : ℝ) := lt_of_le_of_lt (le_trans hp₂t hts.le) hqreal
    have hbnd : pcUpperBound (q : ℝ) < 1 := hp₁bound (q : ℝ) hp₁q hq1
    have hcb : PcContourBound q hq1 := hp₂geom q hq1 hp₂q
    have hθ : 0 < theta 2 q hq1 := theta_pos_of_contourBound hq1 hcb hbnd
    exact not_mem_subcriticalSet_of_theta_pos hq1 hθ hq
  
  calc pc 2 = sSup (subcriticalSet 2) := rfl
    _ ≤ sN := csSup_le' hub
    _ < 1 := hsNlt1


theorem pc_pos_and_lt_one
    (hGeom : ∃ p₀ : ℝ, p₀ < 1 ∧
      ∀ (p : NNReal) (hp : p ≤ 1), (p₀ : ℝ) < (p : ℝ) → PcContourBound p hp) :
    0 < pc 2 ∧ pc 2 < 1 :=
  ⟨pc_pos (by norm_num), pc_lt_one hGeom⟩

end Percolation
end StatMech
