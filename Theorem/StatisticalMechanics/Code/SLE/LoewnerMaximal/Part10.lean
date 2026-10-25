/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Def.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part9
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

theorem loewnerMaximalCurve_eq_forwardSolution
    {W : ℝ → ℝ} {z : ℂ} {T t : ℝ} (hT : 0 < T)
    (g : LoewnerForwardSolution W z T) (ht : t ∈ Ico (0 : ℝ) T) :
    loewnerMaximalCurve W z t = g.curve t := by
  have htLife : ENNReal.ofReal t < loewnerLifetime W z :=
    (ENNReal.ofReal_lt_ofReal_iff hT).2 ht.2 |>.trans_le
      (ofReal_le_loewnerLifetime ⟨hT, ⟨g⟩⟩)
  have htBefore : IsBeforeLoewnerLifetime W z t := ⟨ht.1, htLife⟩
  rw [loewnerMaximalCurve, dif_pos htBefore]
  have hselectedPos : 0 < selectedLoewnerDuration htBefore :=
    (selectedLoewnerDuration_spec htBefore).1.1
  have htCommon : t ∈ Icc (0 : ℝ) (min T (selectedLoewnerDuration htBefore)) :=
    ⟨ht.1, le_min ht.2.le (selectedLoewnerDuration_spec htBefore).2.le⟩
  exact (g.eqOn_overlap hT hselectedPos (selectedLoewnerSolution htBefore) htCommon).symm


theorem loewnerMaximalCurve_flow_of_forwardSolution
    {W : ℝ → ℝ} {z : ℂ} {T s u : ℝ} (hT : 0 < T)
    (g : LoewnerForwardSolution W z T) (hs0 : 0 ≤ s) (hu0 : 0 ≤ u)
    (hsuT : s + u < T) :
    loewnerMaximalCurve W z (s + u) =
      loewnerMaximalCurve (fun r ↦ W (s + r))
        (loewnerMaximalCurve W z s) u := by
  have hsT : s < T := lt_of_le_of_lt (le_add_of_nonneg_right hu0) hsuT
  let h := g.timeShift s hs0
  have hshiftT : 0 < T - s := sub_pos.mpr hsT
  rw [loewnerMaximalCurve_eq_forwardSolution hT g ⟨add_nonneg hs0 hu0, hsuT⟩,
    loewnerMaximalCurve_eq_forwardSolution hT g ⟨hs0, hsT⟩,
    loewnerMaximalCurve_eq_forwardSolution hshiftT h
      ⟨hu0, by linarith⟩]
  rfl


theorem loewnerMaximalCurve_zero {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ}
    (hz : 0 < z.im) : loewnerMaximalCurve W z 0 = z := by
  obtain ⟨T, hT, g, hg0, hgd, hgu⟩ := loewner_local_existence hW hz
  let G : LoewnerForwardSolution W z T := ⟨g, hg0, hgd, hgu⟩
  rw [loewnerMaximalCurve_eq_forwardSolution hT G ⟨le_rfl, hT⟩]
  exact G.initial


theorem loewnerMaximalCurve_mem_upperHalfPlane
    {W : ℝ → ℝ} {z : ℂ} {t : ℝ} (ht : IsBeforeLoewnerLifetime W z t) :
    loewnerMaximalCurve W z t ∈ upperHalfPlane := by
  let g := selectedLoewnerSolution ht
  have hT : 0 < selectedLoewnerDuration ht := (selectedLoewnerDuration_spec ht).1.1
  rw [loewnerMaximalCurve_eq_forwardSolution hT g
    ⟨ht.1, (selectedLoewnerDuration_spec ht).2⟩]
  exact g.upper t ⟨ht.1, (selectedLoewnerDuration_spec ht).2.le⟩


theorem loewnerMaximalCurve_im_antitoneOn {W : ℝ → ℝ} {z : ℂ} :
    AntitoneOn (fun t ↦ (loewnerMaximalCurve W z t).im)
      {t | IsBeforeLoewnerLifetime W z t} := by
  intro s hs t ht hst
  let g := selectedLoewnerSolution ht
  let T := selectedLoewnerDuration ht
  have hT : 0 < T := (selectedLoewnerDuration_spec ht).1.1
  have htT : t < T := (selectedLoewnerDuration_spec ht).2
  have hant : AntitoneOn (fun u ↦ (g.curve u).im) (Icc (0 : ℝ) T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · exact Complex.continuous_im.comp_continuousOn g.continuousOn
    · rw [interior_Icc]
      intro u hu
      exact ((hasDerivAt_im_of ((g.deriv u ⟨hu.1.le, hu.2.le⟩).hasDerivAt
        (Icc_mem_nhds hu.1 hu.2))).differentiableAt).differentiableWithinAt
    · rw [interior_Icc]
      intro u hu
      rw [(hasDerivAt_im_of ((g.deriv u ⟨hu.1.le, hu.2.le⟩).hasDerivAt
        (Icc_mem_nhds hu.1 hu.2))).deriv]
      exact im_loewnerField_nonpos
        (mem_upperHalfPlane.mp (g.upper u ⟨hu.1.le, hu.2.le⟩)).le
  have hsT : s < T := hst.trans_lt htT
  change (loewnerMaximalCurve W z t).im ≤ (loewnerMaximalCurve W z s).im
  rw [loewnerMaximalCurve_eq_forwardSolution hT g ⟨hs.1, hsT⟩,
    loewnerMaximalCurve_eq_forwardSolution hT g ⟨ht.1, htT⟩]
  exact hant ⟨hs.1, hsT.le⟩ ⟨ht.1, htT.le⟩ hst


theorem loewnerMaximalCurve_hasDerivAt
    {W : ℝ → ℝ} {z : ℂ} {t : ℝ} (ht0 : 0 < t)
    (htLife : ENNReal.ofReal t < loewnerLifetime W z) :
    HasDerivAt (loewnerMaximalCurve W z)
      (loewnerField W t (loewnerMaximalCurve W z t)) t := by
  have ht : IsBeforeLoewnerLifetime W z t := ⟨ht0.le, htLife⟩
  let g := selectedLoewnerSolution ht
  let T := selectedLoewnerDuration ht
  have hT : 0 < T := (selectedLoewnerDuration_spec ht).1.1
  have htT : t < T := (selectedLoewnerDuration_spec ht).2
  have heq : loewnerMaximalCurve W z =ᶠ[nhds t] g.curve := by
    filter_upwards [Ioo_mem_nhds ht0 htT] with s hs
    exact loewnerMaximalCurve_eq_forwardSolution hT g ⟨hs.1.le, hs.2⟩
  have hg : HasDerivAt g.curve (loewnerField W t (g.curve t)) t :=
    (g.deriv t ⟨ht0.le, htT.le⟩).hasDerivAt (Icc_mem_nhds ht0 htT)
  have hvalue : loewnerMaximalCurve W z t = g.curve t := heq.self_of_nhds
  rw [hvalue]
  exact hg.congr_of_eventuallyEq heq


theorem loewnerMaximalCurve_hasDerivWithinAt_zero
    {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} (hz : 0 < z.im) :
    HasDerivWithinAt (loewnerMaximalCurve W z)
      (loewnerField W 0 (loewnerMaximalCurve W z 0)) (Ici (0 : ℝ)) 0 := by
  obtain ⟨T, hT, g, hg0, hgd, hgu⟩ := loewner_local_existence hW hz
  let G : LoewnerForwardSolution W z T := ⟨g, hg0, hgd, hgu⟩
  have heq : loewnerMaximalCurve W z =ᶠ[nhdsWithin 0 (Ici (0 : ℝ))] G.curve := by
    filter_upwards [Ico_mem_nhdsGE_of_mem (⟨le_rfl, hT⟩ : (0 : ℝ) ∈ Ico 0 T)] with s hs
    exact loewnerMaximalCurve_eq_forwardSolution hT G hs
  have hG : HasDerivWithinAt G.curve (loewnerField W 0 (G.curve 0)) (Ici (0 : ℝ)) 0 :=
    (G.deriv 0 ⟨le_rfl, hT.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem (⟨le_rfl, hT⟩ : (0 : ℝ) ∈ Ico 0 T))
  have hvalue : loewnerMaximalCurve W z 0 = G.curve 0 :=
    heq.self_of_nhdsWithin (mem_Ici.mpr le_rfl)
  rw [hvalue]
  exact hG.congr_of_eventuallyEq heq hvalue


theorem loewner_maximal_forward_exists {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ}
    (hz : 0 < z.im) :
    0 < loewnerLifetime W z ∧
      loewnerMaximalCurve W z 0 = z ∧
      (∀ t, IsBeforeLoewnerLifetime W z t →
        loewnerMaximalCurve W z t ∈ upperHalfPlane) ∧
      HasDerivWithinAt (loewnerMaximalCurve W z)
        (loewnerField W 0 (loewnerMaximalCurve W z 0)) (Ici (0 : ℝ)) 0 ∧
      ∀ t, 0 < t → ENNReal.ofReal t < loewnerLifetime W z →
        HasDerivAt (loewnerMaximalCurve W z)
          (loewnerField W t (loewnerMaximalCurve W z t)) t := by
  exact ⟨loewnerLifetime_pos hW hz, loewnerMaximalCurve_zero hW hz,
    fun _ ht ↦ loewnerMaximalCurve_mem_upperHalfPlane ht,
    loewnerMaximalCurve_hasDerivWithinAt_zero hW hz,
    fun _ ht htLife ↦ loewnerMaximalCurve_hasDerivAt ht htLife⟩


end StatMech.SLE
