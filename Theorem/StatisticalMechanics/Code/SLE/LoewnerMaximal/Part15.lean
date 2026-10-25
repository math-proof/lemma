/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Def.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part14
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

theorem loewnerSwallowedSet_subset_upperHalfPlane
    (W : ℝ → ℝ) (t : ℝ) :
    loewnerSwallowedSet W t ⊆ upperHalfPlane :=
  fun _ hz ↦ hz.1


theorem loewnerSwallowedSet_relClosed
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    ∃ C : Set ℂ, IsClosed C ∧
      loewnerSwallowedSet W t = C ∩ upperHalfPlane := by
  refine ⟨(loewnerUnswallowedDomain W t)ᶜ,
    (isOpen_loewnerUnswallowedDomain hW ht).isClosed_compl, ?_⟩
  ext z
  simp only [loewnerSwallowedSet, mem_diff, mem_compl_iff, mem_inter_iff]
  tauto


theorem upperHalfPlane_diff_loewnerSwallowedSet
    (W : ℝ → ℝ) (t : ℝ) :
    upperHalfPlane \ loewnerSwallowedSet W t =
      loewnerUnswallowedDomain W t := by
  ext z
  simp only [loewnerSwallowedSet, mem_diff]
  constructor
  · rintro ⟨hzH, hz⟩
    by_contra hnot
    exact hz ⟨hzH, hnot⟩
  · intro hz
    exact ⟨hz.1, fun hswallowed ↦ hswallowed.2 hz⟩


theorem isOpen_upperHalfPlane_diff_loewnerSwallowedSet
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    IsOpen (upperHalfPlane \ loewnerSwallowedSet W t) := by
  rw [upperHalfPlane_diff_loewnerSwallowedSet]
  exact isOpen_loewnerUnswallowedDomain hW ht


theorem isConnected_upperHalfPlane_diff_loewnerSwallowedSet
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    IsConnected (upperHalfPlane \ loewnerSwallowedSet W t) := by
  rw [upperHalfPlane_diff_loewnerSwallowedSet]
  exact isConnected_loewnerUnswallowedDomain hW ht


theorem loewnerSwallowedSet_im_sq_le
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : z ∈ loewnerSwallowedSet W t) :
    z.im ^ 2 ≤ 8 * t := by
  by_contra hnot
  have hlt : t < z.im ^ 2 / 8 := by
    have : 8 * t < z.im ^ 2 := lt_of_not_ge hnot
    linarith
  exact hz.2 (mem_loewnerUnswallowedDomain_of_lt_im_sq_div_eight
    hW ht hz.1 hlt)


theorem exists_loewnerSwallowedSet_re_bound
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    ∃ R : ℝ, ∀ z ∈ loewnerSwallowedSet W t, |z.re| ≤ R := by
  have hcompact : IsCompact (W '' Icc (0 : ℝ) t) :=
    isCompact_Icc.image_of_continuousOn hW.continuousOn
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hcompact.isBounded
  refine ⟨R + 1, ?_⟩
  intro z hz
  apply abs_le.mpr
  constructor
  · by_contra hnot
    have hzleft : z.re ≤ -R - 1 := by linarith
    have hWlower : ∀ s ∈ Icc (0 : ℝ) t, -R ≤ W s := by
      intro s hs
      have hnorm := hR (W s) ⟨s, hs, rfl⟩
      rw [Real.norm_eq_abs] at hnorm
      linarith [neg_abs_le (W s)]
    exact hz.2 (mem_loewnerUnswallowedDomain_of_driverLowerBarrier
      hW ht (by norm_num) hz.1 hzleft hWlower)
  · by_contra hnot
    have hzright : R + 1 ≤ z.re := by linarith
    have hWupper : ∀ s ∈ Icc (0 : ℝ) t, W s ≤ R := by
      intro s hs
      have hnorm := hR (W s) ⟨s, hs, rfl⟩
      rw [Real.norm_eq_abs] at hnorm
      exact (le_abs_self (W s)).trans hnorm
    exact hz.2 (mem_loewnerUnswallowedDomain_of_driverBarrier
      hW ht (by norm_num) hz.1 hzright hWupper)


theorem loewnerSwallowedSet_isBounded_of_re_bound
    {W : ℝ → ℝ} (hW : Continuous W) {t R : ℝ} (ht : 0 ≤ t)
    (hre : ∀ z ∈ loewnerSwallowedSet W t, |z.re| ≤ R) :
    Bornology.IsBounded (loewnerSwallowedSet W t) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨Real.sqrt (R ^ 2 + 8 * t), ?_⟩
  intro z hz
  have him := loewnerSwallowedSet_im_sq_le hW ht hz
  have hre' := abs_le.mp (hre z hz)
  have hrad : 0 ≤ R ^ 2 + 8 * t := by positivity
  have hsq : ‖z‖ ^ 2 ≤ R ^ 2 + 8 * t := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  have hsqrt : Real.sqrt (R ^ 2 + 8 * t) ^ 2 = R ^ 2 + 8 * t :=
    Real.sq_sqrt hrad
  have hnorm : 0 ≤ ‖z‖ := norm_nonneg z
  have hsqrtNonneg : 0 ≤ Real.sqrt (R ^ 2 + 8 * t) := Real.sqrt_nonneg _
  nlinarith


theorem loewnerSwallowedSet_isBounded
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    Bornology.IsBounded (loewnerSwallowedSet W t) := by
  obtain ⟨R, hR⟩ := exists_loewnerSwallowedSet_re_bound hW ht
  exact loewnerSwallowedSet_isBounded_of_re_bound hW ht hR


theorem loewnerSwallowedSet_isCompactHull_of_bounded
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    (hbounded : Bornology.IsBounded (loewnerSwallowedSet W t)) :
    IsCompactHull (loewnerSwallowedSet W t) where
  subset := loewnerSwallowedSet_subset_upperHalfPlane W t
  bounded := hbounded
  relClosed := loewnerSwallowedSet_relClosed hW ht
  complement_open := isOpen_upperHalfPlane_diff_loewnerSwallowedSet hW ht
  complement_connected :=
    isConnected_upperHalfPlane_diff_loewnerSwallowedSet hW ht


theorem loewnerSwallowedSet_isCompactHull_of_re_bound
    {W : ℝ → ℝ} (hW : Continuous W) {t R : ℝ} (ht : 0 ≤ t)
    (hre : ∀ z ∈ loewnerSwallowedSet W t, |z.re| ≤ R) :
    IsCompactHull (loewnerSwallowedSet W t) :=
  loewnerSwallowedSet_isCompactHull_of_bounded hW ht
    (loewnerSwallowedSet_isBounded_of_re_bound hW ht hre)


theorem loewnerSwallowedSet_isCompactHull
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    IsCompactHull (loewnerSwallowedSet W t) :=
  loewnerSwallowedSet_isCompactHull_of_bounded hW ht
    (loewnerSwallowedSet_isBounded hW ht)


theorem loewnerSwallowedSet_zero {W : ℝ → ℝ} (hW : Continuous W) :
    loewnerSwallowedSet W 0 = ∅ := by
  ext z
  constructor
  · intro hz
    exact False.elim (hz.2 (mem_loewnerUnswallowedDomain_zero hW hz.1))
  · simp


theorem loewnerSwallowedSet_monotoneOn (W : ℝ → ℝ) :
    MonotoneOn (loewnerSwallowedSet W) (Ici (0 : ℝ)) := by
  intro s hs t ht hst z hz
  refine ⟨hz.1, ?_⟩
  intro hzt
  exact hz.2 (loewnerUnswallowedDomain_antitoneOn W hs ht hst hzt)

end StatMech.SLE
