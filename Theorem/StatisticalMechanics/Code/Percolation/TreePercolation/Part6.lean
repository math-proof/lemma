/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Percolation.TreePercolation.Part6
open Set Finset
open scoped NNReal


namespace StatMech

namespace Percolation

lemma survivalProb_zero_eq_zero (b : ℕ) : survivalProb b 0 = 0 := by
  refine survivalProb_eq_zero_of_subcritical b (le_refl 0) (by norm_num) ?_
  simp


theorem treePc_eq (b : ℕ) (hb : 1 ≤ b) : treePc b = 1 / (b : ℝ) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hbinv_le_one : 1 / (b : ℝ) ≤ 1 := by
    rw [div_le_one hbpos]; exact_mod_cast hb
  have hbinv_pos : (0 : ℝ) < 1 / b := by positivity
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ⟨0, ⟨by norm_num, survivalProb_zero_eq_zero b⟩⟩ ?_ ?_
  · 
    intro p hp
    by_contra hcon
    have hcon' : 1 / (b : ℝ) < p := lt_of_not_ge hcon
    have hmean : 1 < (b : ℝ) * p := by
      have hmul : (b : ℝ) * (1 / b) < (b : ℝ) * p := mul_lt_mul_of_pos_left hcon' hbpos
      rwa [mul_one_div, div_self (ne_of_gt hbpos)] at hmul
    have hsurv := survivalProb_pos_of_supercritical b hp.1.2 hmean
    rw [hp.2] at hsurv; exact lt_irrefl 0 hsurv
  · 
    intro w hw
    rcases le_or_gt 0 w with hw0 | hw0
    · refine ⟨(w + 1 / b) / 2, ⟨⟨by linarith, by linarith⟩, ?_⟩, by linarith⟩
      refine survivalProb_eq_zero_of_subcritical b (by linarith) (by linarith) ?_
      have hlt : (w + 1 / b) / 2 < 1 / b := by linarith
      have hmul : (b : ℝ) * ((w + 1 / b) / 2) < (b : ℝ) * (1 / b) :=
        mul_lt_mul_of_pos_left hlt hbpos
      rwa [mul_one_div, div_self (ne_of_gt hbpos)] at hmul
    · exact ⟨0, ⟨⟨le_refl 0, zero_le_one⟩, survivalProb_zero_eq_zero b⟩, hw0⟩


theorem survivalProb_pos_of_gt_treePc (b : ℕ) {p : ℝ} (hb : 1 ≤ b)
    (hp1 : p ≤ 1) (hlt : 1 / (b : ℝ) < p) : 0 < survivalProb b p := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hmean : 1 < (b : ℝ) * p := by
    have hmul : (b : ℝ) * (1 / b) < (b : ℝ) * p := mul_lt_mul_of_pos_left hlt hbpos
    rwa [mul_one_div, div_self (ne_of_gt hbpos)] at hmul
  exact survivalProb_pos_of_supercritical b hp1 hmean


theorem survivalProb_eq_zero_of_lt_treePc (b : ℕ) {p : ℝ} (hb : 1 ≤ b)
    (hp0 : 0 ≤ p) (hlt : p < 1 / (b : ℝ)) : survivalProb b p = 0 := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hbinv_le_one : 1 / (b : ℝ) ≤ 1 := by rw [div_le_one hbpos]; exact_mod_cast hb
  have hmean : (b : ℝ) * p < 1 := by
    have hmul : (b : ℝ) * p < (b : ℝ) * (1 / b) := mul_lt_mul_of_pos_left hlt hbpos
    rwa [mul_one_div, div_self (ne_of_gt hbpos)] at hmul
  exact survivalProb_eq_zero_of_subcritical b hp0 (le_of_lt (lt_of_lt_of_le hlt hbinv_le_one)) hmean

end Percolation
end StatMech
