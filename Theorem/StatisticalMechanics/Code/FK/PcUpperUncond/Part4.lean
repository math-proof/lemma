/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.FK.PcUpperUncond.Part4
open MeasureTheory Filter Topology Finset Set SimpleGraph
open scoped NNReal ENNReal BigOperators Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation


theorem fkTheta_pos_of_nonPercolationBound {q : ℝ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hBound : FkNonPercolationBound q hp hp1 hq)
    (hsum : fkPcUpperBound 2 p < 1) :
    0 < fkTheta 2 hp hp1 hq (q := q) := by
  have h : 1 - fkTheta 2 hp hp1 hq (q := q) ≤ fkPcUpperBound 2 p := hBound
  linarith


theorem fkSubcriticalSet_bddAbove' (d : ℕ) (q : ℝ) : BddAbove (fkSubcriticalSet d q) := by
  refine ⟨1, fun x hx => ?_⟩
  obtain ⟨hp, hp1, hq, _⟩ := hx
  exact hp1.le


theorem fkSubcriticalSet_nonempty {q : ℝ} (hq : 1 ≤ q) : (fkSubcriticalSet 2 q).Nonempty := by
  set p : ℝ := 1 / (4 * 2) with hp_def
  have hp_pos : 0 < p := by rw [hp_def]; norm_num
  have hp1 : p < 1 := by rw [hp_def]; norm_num
  have hsmall : (2 * (2 : ℕ) : ℝ) * p < 1 := by rw [hp_def]; norm_num
  exact ⟨p, hp_pos, hp1, zero_lt_one.trans_le hq,
    fkTheta_eq_zero_of_lt (by norm_num) hp_pos hp1 hq hsmall⟩


theorem not_mem_fkSubcriticalSet_of_fkTheta_pos {q : ℝ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hθ : 0 < fkTheta 2 hp hp1 hq (q := q)) : p ∉ fkSubcriticalSet 2 q := by
  intro hmem
  obtain ⟨hp', hp1', hq', hzero⟩ := hmem
  
  rw [show hp' = hp from rfl, show hp1' = hp1 from rfl, show hq' = hq from rfl] at hzero
  exact (ne_of_gt hθ) hzero


theorem fkPc_lt_one {q : ℝ} (hq : 1 ≤ q)
    (hGeom : ∃ p₀ : ℝ, p₀ < 1 ∧
      ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p₀ < p →
        FkNonPercolationBound q hp hp1 (zero_lt_one.trans_le hq)) :
    fkPc 2 q < 1 := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  obtain ⟨p₁, hp₁lt, hp₁bound⟩ := exists_p_lt_one_fkPcUpperBound_lt_one 2
  obtain ⟨p₂, hp₂lt, hp₂geom⟩ := hGeom
  
  set t : ℝ := max (max p₁ p₂) 0 with ht
  have htlt : t < 1 := max_lt (max_lt hp₁lt hp₂lt) (by norm_num)
  have ht0 : (0 : ℝ) ≤ t := le_max_right _ _
  have hp₁t : p₁ ≤ t := le_trans (le_max_left _ _) (le_max_left _ _)
  have hp₂t : p₂ ≤ t := le_trans (le_max_right _ _) (le_max_left _ _)
  
  set s : ℝ := (t + 1) / 2 with hs
  have hts : t < s := by rw [hs]; linarith
  have hslt : s < 1 := by rw [hs]; linarith
  have hs0 : (0 : ℝ) < s := by rw [hs]; linarith
  
  have hub : ∀ r ∈ fkSubcriticalSet 2 q, r ≤ s := by
    intro r hr
    by_contra hcon
    push Not at hcon
    obtain ⟨hr0, hr1, _, hzero⟩ := hr
    
    have hp₁r : p₁ < r := lt_of_le_of_lt (le_trans hp₁t hts.le) hcon
    have hp₂r : p₂ < r := lt_of_le_of_lt (le_trans hp₂t hts.le) hcon
    have hbnd : fkPcUpperBound 2 r < 1 := hp₁bound r hp₁r hr1.le
    have hcb : FkNonPercolationBound q hr0 hr1 hq0 := hp₂geom r hr0 hr1 hp₂r
    have hθ : 0 < fkTheta 2 hr0 hr1 hq0 (q := q) :=
      fkTheta_pos_of_nonPercolationBound hr0 hr1 hq0 hcb hbnd
    exact not_mem_fkSubcriticalSet_of_fkTheta_pos hr0 hr1 hq0 hθ
      ⟨hr0, hr1, hq0, hzero⟩
  
  calc fkPc 2 q = sSup (fkSubcriticalSet 2 q) := rfl
    _ ≤ s := csSup_le (fkSubcriticalSet_nonempty hq) hub
    _ < 1 := hslt


theorem fkPc_pos_and_lt_one {q : ℝ} (hq : 1 ≤ q)
    (hGeom : ∃ p₀ : ℝ, p₀ < 1 ∧
      ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p₀ < p →
        FkNonPercolationBound q hp hp1 (zero_lt_one.trans_le hq)) :
    0 < fkPc 2 q ∧ fkPc 2 q < 1 :=
  ⟨fkPc_pos_of_two_le (le_refl 2) hq, fkPc_lt_one hq hGeom⟩

end FK
end StatMech
