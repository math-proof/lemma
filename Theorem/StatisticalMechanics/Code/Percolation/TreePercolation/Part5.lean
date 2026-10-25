/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TreePercolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Percolation.TreePercolation.Part5
open Set Finset
open scoped NNReal


namespace StatMech

namespace Percolation

lemma survivalProb_nonneg (b : ℕ) (p : ℝ) : 0 ≤ survivalProb b p := by
  unfold survivalProb; linarith [extinctionProb_le_one b p]

lemma survivalProb_pos_iff (b : ℕ) (p : ℝ) :
    0 < survivalProb b p ↔ extinctionProb b p < 1 := by
  unfold survivalProb; constructor <;> intro h <;> linarith


lemma treeGF_zero_nonneg (b : ℕ) {p : ℝ} (hp1 : p ≤ 1) : 0 ≤ treeGF b p 0 := by
  unfold treeGF
  have : (0 : ℝ) ≤ 1 - p + p * 0 := by simp; linarith
  positivity


lemma supercritical_fixed (b : ℕ) {p : ℝ} (hp1 : p ≤ 1) (hmean : 1 < (b : ℝ) * p) :
    ∃ q ∈ Ico (0 : ℝ) 1, treeGF b p q = q := by
  set g : ℝ → ℝ := fun s => treeGF b p s - s with hg
  have hg1 : g 1 = 0 := by simp [hg]
  have hgder : HasDerivAt g ((b : ℝ) * p - 1) 1 := by
    convert (treeGF_hasDerivAt_one b p).sub (hasDerivAt_id 1) using 1
    ext s
    simp [hg, Pi.sub_apply, id]
  have hslope : Filter.Tendsto (slope g 1) (nhdsWithin 1 {1}ᶜ) (nhds ((b : ℝ) * p - 1)) :=
    hasDerivAt_iff_tendsto_slope.mp hgder
  have hpos : (0 : ℝ) < (b : ℝ) * p - 1 := by linarith
  have hev : ∀ᶠ y in nhdsWithin 1 {1}ᶜ, 0 < slope g 1 y := hslope.eventually_const_lt hpos
  have hsub : nhdsWithin 1 (Ioo (0 : ℝ) 1) ≤ nhdsWithin 1 {1}ᶜ := by
    refine nhdsWithin_mono _ (fun x hx => ?_)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_lt hx.2
  have hev2 : ∀ᶠ y in nhdsWithin 1 (Ioo (0 : ℝ) 1), 0 < slope g 1 y := hev.filter_mono hsub
  haveI : (nhdsWithin (1 : ℝ) (Ioo 0 1)).NeBot := right_nhdsWithin_Ioo_neBot (by norm_num)
  obtain ⟨y, hyslope, hymem⟩ := (hev2.and self_mem_nhdsWithin).exists
  have hy01 : y ∈ Ioo (0 : ℝ) 1 := hymem
  have hylt1 : y < 1 := hy01.2
  have hy0 : 0 < y := hy01.1
  have hyne : y - 1 ≠ 0 := by intro h; nlinarith
  have hslope_eq : slope g 1 y = (g y - g 1) / (y - 1) := slope_def_field g 1 y
  have hgy_neg : g y < 0 := by
    rw [hslope_eq, hg1, sub_zero] at hyslope
    have hyneg : y - 1 < 0 := by linarith
    by_contra hcon
    have hge : 0 ≤ g y := le_of_not_gt hcon
    have : g y / (y - 1) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hge (le_of_lt hyneg)
    linarith
  have hg0 : 0 ≤ g 0 := by
    have hval : g 0 = treeGF b p 0 - 0 := rfl
    rw [hval, sub_zero]; exact treeGF_zero_nonneg b hp1
  have hgcont : ContinuousOn g (Icc 0 y) :=
    ((treeGF_continuous b p).sub continuous_id).continuousOn
  have hmem0 : (0 : ℝ) ∈ Icc (g y) (g 0) := ⟨le_of_lt hgy_neg, hg0⟩
  obtain ⟨q, hqmem, hqval⟩ := intermediate_value_Icc' (le_of_lt hy0) hgcont hmem0
  refine ⟨q, ⟨hqmem.1, lt_of_le_of_lt hqmem.2 hylt1⟩, ?_⟩
  have hval : g q = treeGF b p q - q := rfl
  rw [hval] at hqval; linarith


lemma subcritical_no_fixed (b : ℕ) {p s : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmean : (b : ℝ) * p < 1) (hs0 : 0 ≤ s) (hs1 : s < 1) : s < treeGF b p s := by
  have hps : 0 ≤ p * (1 - s) := mul_nonneg hp0 (by linarith)
  have hbern : 1 - (b : ℝ) * (p * (1 - s)) ≤ treeGF b p s := by
    have hbase : (-1 : ℝ) ≤ 1 - p * (1 - s) := by
      have hub : p * (1 - s) ≤ 1 :=
        mul_le_one₀ hp1 (by linarith : (0 : ℝ) ≤ 1 - s) (by linarith : (1 : ℝ) - s ≤ 1)
      linarith
    have hb := one_add_mul_sub_le_pow hbase b
    have heq1 : (1 : ℝ) + (b : ℝ) * ((1 - p * (1 - s)) - 1) = 1 - (b : ℝ) * (p * (1 - s)) := by
      ring
    have hgeq : treeGF b p s = (1 - p * (1 - s)) ^ b := by unfold treeGF; ring_nf
    rw [hgeq]; linarith [heq1 ▸ hb]
  have h1s : (0 : ℝ) < 1 - s := by linarith
  have hkey : (b : ℝ) * (p * (1 - s)) < 1 - s := by
    have hlt : (b : ℝ) * p * (1 - s) < 1 * (1 - s) := mul_lt_mul_of_pos_right hmean h1s
    rw [one_mul] at hlt; nlinarith [hlt]
  linarith


lemma survivalProb_eq_zero_of_subcritical (b : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmean : (b : ℝ) * p < 1) : survivalProb b p = 0 := by
  have hext : extinctionProb b p = 1 := by
    rcases lt_or_eq_of_le (extinctionProb_le_one b p) with hlt | heq
    · exact absurd (extinctionProb_isFixed b p)
        (ne_of_gt (subcritical_no_fixed b hp0 hp1 hmean (extinctionProb_nonneg b p) hlt))
    · exact heq
  unfold survivalProb; rw [hext]; ring


lemma survivalProb_pos_of_supercritical (b : ℕ) {p : ℝ} (hp1 : p ≤ 1)
    (hmean : 1 < (b : ℝ) * p) : 0 < survivalProb b p := by
  rw [survivalProb_pos_iff]
  obtain ⟨q, hq_mem, hq_fix⟩ := supercritical_fixed b hp1 hmean
  have hqmem : q ∈ fixedSet b p := ⟨⟨hq_mem.1, le_of_lt hq_mem.2⟩, hq_fix⟩
  have : extinctionProb b p ≤ q := csInf_le (fixedSet_bddBelow b p) hqmem
  linarith [hq_mem.2]


end Percolation
end StatMech
