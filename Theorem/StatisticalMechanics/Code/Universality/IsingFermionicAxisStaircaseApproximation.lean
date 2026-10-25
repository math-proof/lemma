/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAxisStaircaseApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

theorem eventually_norm_sub_lt_on_compact_of_tendstoLocallyUniformlyOn
    {ι : Type*} {p : Filter ι} {F : ι -> Complex -> Complex}
    {f : Complex -> Complex} (h : TendstoLocallyUniformlyOn F f p Set.univ)
    (K : Set Complex) (hK : IsCompact K) (epsilon : Real)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n in p, forall z, z ∈ K -> norm (F n z - f z) < epsilon := by
  have hu : TendstoUniformlyOn F f p K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
      (h.mono (Set.subset_univ K))
  rw [Metric.uniformity_basis_dist.tendstoUniformlyOn_iff_of_uniformity] at hu
  simpa only [Prod.fst, Prod.snd, Set.mem_setOf_eq, dist_eq_norm, norm_sub_rev] using
    hu epsilon hepsilon


theorem isConservativeOn_univ_of_ordered_wedgeContour_eq_zero
    (f : Complex -> Complex)
    (hordered : forall z w : Complex, z.re <= w.re -> z.im <= w.im ->
      Complex.wedgeIntegral z w f + Complex.wedgeIntegral w z f = 0) :
    Complex.IsConservativeOn f Set.univ := by
  intro z w _hrect
  rw [← add_eq_zero_iff_eq_neg]
  by_cases hre : z.re <= w.re
  · by_cases him : z.im <= w.im
    · exact hordered z w hre him
    · have him' : w.im <= z.im := le_of_not_ge him
      let southwest : Complex := (z.re : Complex) + w.im * Complex.I
      let northeast : Complex := (w.re : Complex) + z.im * Complex.I
      have h := hordered southwest northeast (by simp [southwest, northeast, hre])
        (by simp [southwest, northeast, him'])
      rw [Complex.wedgeIntegral_add_wedgeIntegral_eq] at h ⊢
      simp only [southwest, northeast, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add,
        add_zero, sub_zero] at h
      rw [intervalIntegral.integral_symm w.im z.im,
        intervalIntegral.integral_symm w.im z.im]
      linear_combination -h
  · have hre' : w.re <= z.re := le_of_not_ge hre
    by_cases him : z.im <= w.im
    · let southwest : Complex := (w.re : Complex) + z.im * Complex.I
      let northeast : Complex := (z.re : Complex) + w.im * Complex.I
      have h := hordered southwest northeast (by simp [southwest, northeast, hre'])
        (by simp [southwest, northeast, him])
      rw [Complex.wedgeIntegral_add_wedgeIntegral_eq] at h ⊢
      simp only [southwest, northeast, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add,
        add_zero, sub_zero] at h
      rw [intervalIntegral.integral_symm w.re z.re,
        intervalIntegral.integral_symm w.re z.re]
      linear_combination -h
    · have him' : w.im <= z.im := le_of_not_ge him
      simpa [add_comm] using hordered w z hre' him'


end
end StatMech.Universality
