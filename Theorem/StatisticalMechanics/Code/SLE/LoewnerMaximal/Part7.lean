/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Def.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part6
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

theorem ofReal_le_loewnerLifetime {W : ℝ → ℝ} {z : ℂ} {T : ℝ}
    (hT : IsLoewnerAdmissibleDuration W z T) :
    ENNReal.ofReal T ≤ loewnerLifetime W z := by
  exact le_iSup (fun U : {U : ℝ // IsLoewnerAdmissibleDuration W z U} ↦
    ENNReal.ofReal U.1) ⟨T, hT⟩


theorem loewnerLifetime_pos {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ}
    (hz : 0 < z.im) : 0 < loewnerLifetime W z := by
  obtain ⟨T, hT⟩ := exists_isLoewnerAdmissibleDuration hW hz
  exact (ENNReal.ofReal_pos.mpr hT.1).trans_le (ofReal_le_loewnerLifetime hT)


theorem ofReal_im_sq_div_eight_le_loewnerLifetime
    {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} (hz : 0 < z.im) :
    ENNReal.ofReal (z.im ^ 2 / 8) ≤ loewnerLifetime W z := by
  obtain ⟨g, hg0, hgd, hgstrip⟩ := loewner_local_existence_strip_explicit hW hz
  have hE : 0 < z.im ^ 2 / 8 := by positivity
  have hδ : 0 < z.im / 2 := by positivity
  apply ofReal_le_loewnerLifetime
  refine ⟨hE, ⟨⟨g, hg0, hgd, ?_⟩⟩⟩
  intro t ht
  exact loewnerStrip_subset_upperHalfPlane hδ (hgstrip t ht)


theorem exists_admissibleDuration_gt_of_ofReal_lt_lifetime
    {W : ℝ → ℝ} {z : ℂ} {t : ℝ}
    (hlt : ENNReal.ofReal t < loewnerLifetime W z) :
    ∃ T, IsLoewnerAdmissibleDuration W z T ∧ t < T := by
  rw [loewnerLifetime, lt_iSup_iff] at hlt
  obtain ⟨T, hT⟩ := hlt
  refine ⟨T.1, T.2, ?_⟩
  exact ENNReal.ofReal_lt_ofReal_iff T.2.1 |>.mp hT


end StatMech.SLE
