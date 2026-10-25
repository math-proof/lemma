/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Def.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part2
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

theorem LoewnerForwardSolution.re_gt_driverBarrier
    {W : ℝ → ℝ} {z : ℂ} {T M d : ℝ}
    (g : LoewnerForwardSolution W z T) (hd : 0 < d)
    (hW : ∀ s ∈ Icc (0 : ℝ) T, W s ≤ M)
    (hz : M + d ≤ z.re) :
    ∀ s ∈ Icc (0 : ℝ) T, M + d / 2 < (g.curve s).re := by
  let f : ℝ → ℝ := fun s ↦ (g.curve s).re - (M + d / 2)
  have hfcont : ContinuousOn f (Icc (0 : ℝ) T) :=
    (Complex.continuous_re.comp_continuousOn g.continuousOn).sub continuousOn_const
  have hfzero : 0 < f 0 := by
    dsimp [f]
    rw [g.initial]
    linarith
  have hfderiv : ∀ s ∈ Ioo (0 : ℝ) T, 0 < f s →
      ∃ v : ℝ, HasDerivAt f v s ∧ 0 ≤ v := by
    intro s hs hfs
    have hsIcc : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
    have hcurve := (g.deriv s hsIcc).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have hreDeriv : HasDerivAt f (loewnerField W s (g.curve s)).re s := by
      simpa [f] using (hasDerivAt_re_of hcurve).sub_const (M + d / 2)
    have hnum : 0 < (g.curve s).re - W s := by
      have hWs := hW s hsIcc
      dsimp [f] at hfs
      linarith
    have hsubne : g.curve s - (W s : ℂ) ≠ 0 := by
      intro heq
      have himzero : (g.curve s).im = 0 := by
        simpa using congrArg Complex.im heq
      exact (mem_upperHalfPlane.mp (g.upper s hsIcc)).ne' himzero
    have hden : 0 < Complex.normSq (g.curve s - (W s : ℂ)) :=
      Complex.normSq_pos.mpr hsubne
    refine ⟨(loewnerField W s (g.curve s)).re, hreDeriv, ?_⟩
    rw [re_loewnerField]
    exact (div_pos (mul_pos (by norm_num) hnum) hden).le
  have hpos := positiveOn_Icc_of_deriv_nonneg_while_pos hfcont hfzero hfderiv
  intro s hs
  exact sub_pos.mp (hpos s hs)


theorem LoewnerForwardSolution.im_ge_exp_of_driverBarrier
    {W : ℝ → ℝ} {z : ℂ} {T M d : ℝ}
    (g : LoewnerForwardSolution W z T) (hd : 0 < d)
    (hW : ∀ s ∈ Icc (0 : ℝ) T, W s ≤ M)
    (hz : M + d ≤ z.re) :
    ∀ s ∈ Icc (0 : ℝ) T,
      z.im * Real.exp (-(2 / (d / 2) ^ 2) * s) ≤ (g.curve s).im := by
  have hre := g.re_gt_driverBarrier hd hW hz
  have hδ : 0 < d / 2 := by positivity
  have hden : ∀ s ∈ Ico (0 : ℝ) T,
      (d / 2) ^ 2 ≤ Complex.normSq (g.curve s - (W s : ℂ)) := by
    intro s hs
    have hsIcc : s ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self hs
    have hWs := hW s hsIcc
    have hgap : d / 2 < (g.curve s).re - W s := by
      linarith [hre s hsIcc]
    rw [Complex.normSq_apply]
    simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]
    nlinarith [sq_nonneg ((g.curve s).im - 0)]
  have him := im_ge_exp_mul_of_normSq_ge hδ
    (Complex.continuous_im.comp_continuousOn g.continuousOn)
    (fun s hs ↦ (g.deriv s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs))
    (fun s hs ↦ (mem_upperHalfPlane.mp (g.upper s
      (Ico_subset_Icc_self hs))).le)
    hden
  intro s hs
  have := him s hs
  rw [g.initial, sub_zero] at this
  exact this


theorem LoewnerForwardSolution.im_antitoneOn
    {W : ℝ → ℝ} {z : ℂ} {T : ℝ}
    (g : LoewnerForwardSolution W z T) :
    AntitoneOn (fun t ↦ (g.curve t).im) (Icc (0 : ℝ) T) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
  · exact Complex.continuous_im.comp_continuousOn g.continuousOn
  · rw [interior_Icc]
    intro t ht
    exact ((hasDerivAt_im_of ((g.deriv t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2))).differentiableAt).differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [(hasDerivAt_im_of ((g.deriv t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2))).deriv]
    exact im_loewnerField_nonpos
      (mem_upperHalfPlane.mp (g.upper t ⟨ht.1.le, ht.2.le⟩)).le


theorem LoewnerForwardSolution.hasDerivWithinAt_Ici {W : ℝ → ℝ} {z : ℂ}
    {T : ℝ} (g : LoewnerForwardSolution W z T) :
    ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt g.curve (loewnerField W t (g.curve t)) (Ici t) t := by
  intro t ht
  exact (g.deriv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem ht)


theorem LoewnerForwardSolution.eqOn_overlap {W : ℝ → ℝ} {z : ℂ} {S T : ℝ}
    (hS : 0 < S) (hT : 0 < T)
    (g : LoewnerForwardSolution W z S) (h : LoewnerForwardSolution W z T) :
    EqOn g.curve h.curve (Icc (0 : ℝ) (min S T)) := by
  have hmin : 0 < min S T := lt_min hS hT
  let g' := g.restrict (min_le_left S T)
  let h' := h.restrict (min_le_right S T)
  exact loewner_solution_unique hmin g'.initial h'.initial
    g'.continuousOn g'.hasDerivWithinAt_Ici
    (fun t ht ↦ mem_upperHalfPlane.mp (g'.upper t ht))
    h'.continuousOn h'.hasDerivWithinAt_Ici
    (fun t ht ↦ mem_upperHalfPlane.mp (h'.upper t ht))


theorem LoewnerForwardSolution.initial_eq_of_eq_at
    {W : ℝ → ℝ} {z w : ℂ} {S T t : ℝ}
    (hS : 0 < S) (hT : 0 < T)
    (g : LoewnerForwardSolution W z S) (h : LoewnerForwardSolution W w T)
    (ht0 : 0 < t) (htS : t < S) (htT : t < T)
    (heq : g.curve t = h.curve t) : z = w := by
  let U := min S T
  have hU : 0 < U := lt_min hS hT
  let g' := g.restrict (min_le_left S T)
  let h' := h.restrict (min_le_right S T)
  have hcomp : IsCompact (Icc (0 : ℝ) U) := isCompact_Icc
  have hne : (Icc (0 : ℝ) U).Nonempty := ⟨0, le_rfl, hU.le⟩
  have himcg : ContinuousOn (fun u ↦ (g'.curve u).im) (Icc 0 U) :=
    Complex.continuous_im.comp_continuousOn g'.continuousOn
  have himch : ContinuousOn (fun u ↦ (h'.curve u).im) (Icc 0 U) :=
    Complex.continuous_im.comp_continuousOn h'.continuousOn
  obtain ⟨ug, hugmem, hugmin⟩ := hcomp.exists_isMinOn hne himcg
  obtain ⟨uh, huhmem, huhmin⟩ := hcomp.exists_isMinOn hne himch
  let δ : ℝ := min (g'.curve ug).im (h'.curve uh).im
  have hδ : 0 < δ := lt_min
    (mem_upperHalfPlane.mp (g'.upper ug hugmem))
    (mem_upperHalfPlane.mp (h'.upper uh huhmem))
  have hg : ∀ u ∈ Ioo (0 : ℝ) U,
      HasDerivAt g'.curve (loewnerField W u (g'.curve u)) u ∧
        g'.curve u ∈ loewnerStrip δ := by
    intro u hu
    refine ⟨(g'.deriv u ⟨hu.1.le, hu.2.le⟩).hasDerivAt
      (Icc_mem_nhds hu.1 hu.2), ?_⟩
    rw [mem_loewnerStrip]
    exact (min_le_left _ _).trans (hugmin (Ioo_subset_Icc_self hu))
  have hh : ∀ u ∈ Ioo (0 : ℝ) U,
      HasDerivAt h'.curve (loewnerField W u (h'.curve u)) u ∧
        h'.curve u ∈ loewnerStrip δ := by
    intro u hu
    refine ⟨(h'.deriv u ⟨hu.1.le, hu.2.le⟩).hasDerivAt
      (Icc_mem_nhds hu.1 hu.2), ?_⟩
    rw [mem_loewnerStrip]
    exact (min_le_right _ _).trans (huhmin (Ioo_subset_Icc_self hu))
  have htU : t ∈ Ioo (0 : ℝ) U := ⟨ht0, lt_min htS htT⟩
  have heqOpen : EqOn g'.curve h'.curve (Ioo (0 : ℝ) U) :=
    loewnerSolution_unique_Ioo hδ htU hg hh heq
  have heqClosed : EqOn g'.curve h'.curve (Icc (0 : ℝ) U) :=
    heqOpen.of_subset_closure g'.continuousOn h'.continuousOn
      Ioo_subset_Icc_self (by rw [closure_Ioo hU.ne])
  calc
    z = g'.curve 0 := g'.initial.symm
    _ = h'.curve 0 := heqClosed ⟨le_rfl, hU.le⟩
    _ = w := h'.initial


end StatMech.SLE
