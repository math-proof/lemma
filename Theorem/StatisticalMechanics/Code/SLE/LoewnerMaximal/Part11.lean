/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Def.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part10
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

theorem mem_loewnerUnswallowedDomain_of_lt_im_sq_div_eight
    {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : z ∈ upperHalfPlane) (hlt : t < z.im ^ 2 / 8) :
    z ∈ loewnerUnswallowedDomain W t := by
  have hzpos : 0 < z.im := mem_upperHalfPlane.mp hz
  have hE : 0 < z.im ^ 2 / 8 := by positivity
  refine ⟨hz, ht, ?_⟩
  exact ((ENNReal.ofReal_lt_ofReal_iff hE).2 hlt).trans_le
    (ofReal_im_sq_div_eight_le_loewnerLifetime hW hzpos)


theorem mem_loewnerUnswallowedDomain_of_forwardSolution
    {W : ℝ → ℝ} (hWcont : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : z ∈ upperHalfPlane) (g : LoewnerForwardSolution W z t) :
    z ∈ loewnerUnswallowedDomain W t := by
  let y : ℂ := g.curve t
  have hy : 0 < y.im :=
    mem_upperHalfPlane.mp (g.upper t ⟨ht, le_rfl⟩)
  have hWshift : Continuous (fun r ↦ W (t + r)) :=
    hWcont.comp (continuous_const.add continuous_id)
  obtain ⟨E, hE, curve, hcurve0, hcurveDeriv, hcurveUpper⟩ :=
    loewner_local_existence hWshift hy
  let hseg : LoewnerForwardSolution (fun r ↦ W (t + r)) y E :=
    { curve := curve
      initial := hcurve0
      deriv := hcurveDeriv
      upper := hcurveUpper }
  let gh : LoewnerForwardSolution W z (t + E) :=
    g.append hseg ht hE.le
  have htotal : 0 < t + E := by linarith
  have hbefore : IsBeforeLoewnerLifetime W z t :=
    (isBeforeLoewnerLifetime_iff_exists_admissible ht).2
      ⟨t + E, ⟨htotal, ⟨gh⟩⟩, by linarith⟩
  exact ⟨hz, hbefore⟩


theorem mem_loewnerUnswallowedDomain_of_driverBarrier
    {W : ℝ → ℝ} (hWcont : Continuous W) {t M d : ℝ}
    (ht : 0 ≤ t) (hd : 0 < d) {z : ℂ} (hz : z ∈ upperHalfPlane)
    (hzre : M + d ≤ z.re)
    (hW : ∀ s ∈ Icc (0 : ℝ) t, W s ≤ M) :
    z ∈ loewnerUnswallowedDomain W t := by
  obtain ⟨g⟩ := exists_loewnerForwardSolution_of_driverBarrier
    hWcont ht hd (mem_upperHalfPlane.mp hz) hzre hW
  exact mem_loewnerUnswallowedDomain_of_forwardSolution hWcont ht hz g


theorem mem_loewnerUnswallowedDomain_of_driverLowerBarrier
    {W : ℝ → ℝ} (hWcont : Continuous W) {t m d : ℝ}
    (ht : 0 ≤ t) (hd : 0 < d) {z : ℂ} (hz : z ∈ upperHalfPlane)
    (hzre : z.re ≤ m - d)
    (hW : ∀ s ∈ Icc (0 : ℝ) t, m ≤ W s) :
    z ∈ loewnerUnswallowedDomain W t := by
  obtain ⟨g⟩ := exists_loewnerForwardSolution_of_driverLowerBarrier
    hWcont ht hd (mem_upperHalfPlane.mp hz) hzre hW
  exact mem_loewnerUnswallowedDomain_of_forwardSolution hWcont ht hz g


theorem loewnerUnswallowedDomain_nonempty {W : ℝ → ℝ} (hW : Continuous W)
    {t : ℝ} (ht : 0 ≤ t) : (loewnerUnswallowedDomain W t).Nonempty := by
  let z : ℂ := ((4 * (t + 1) : ℝ) : ℂ) * Complex.I
  have hzim : z.im = 4 * (t + 1) := by simp [z]
  have hzpos : 0 < z.im := by rw [hzim]; positivity
  have hlt : t < z.im ^ 2 / 8 := by
    rw [hzim]
    nlinarith [sq_nonneg t]
  exact ⟨z, mem_loewnerUnswallowedDomain_of_lt_im_sq_div_eight
    hW ht (mem_upperHalfPlane.mpr hzpos) hlt⟩


end StatMech.SLE
