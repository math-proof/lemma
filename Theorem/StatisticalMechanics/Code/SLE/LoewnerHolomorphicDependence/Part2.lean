/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerHolomorphicDependence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part15
import Mathlib.Analysis.Complex.Conformal
import Def.StatisticalMechanics.Code.SLE.LoewnerHolomorphicDependence
open Complex Set Metric Filter Topology
open scoped Interval


namespace StatMech.SLE

noncomputable section

theorem loewnerInitialJacobian_ne_zero
    (W : Real -> Real) (t : Real) (z : Complex) :
    loewnerInitialJacobian W t z ≠ 0 := by
  exact Complex.exp_ne_zero _

@[simp] theorem loewnerInitialJacobian_zero
    (W : Real -> Real) (z : Complex) :
    loewnerInitialJacobian W 0 z = 1 := by
  simp [loewnerInitialJacobian]


theorem loewnerMaximalMaps_hasDerivAt_of_lt_im_sq_div_sixteen
    {W : Real -> Real} (hW : Continuous W) {u : Real} (hu : 0 <= u)
    {z : Complex} (hz : z ∈ upperHalfPlane) (hshort : u < z.im ^ 2 / 16) :
    HasDerivAt (loewnerMaximalMaps W u) (loewnerInitialJacobian W u z) z := by
  have hzpos : 0 < z.im := mem_upperHalfPlane.mp hz
  let E : Real := z.im ^ 2 / 16
  let delta : Real := z.im / 2
  have hE : 0 < E := by dsimp [E]; positivity
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hradius : 0 < z.im / 4 := by positivity
  obtain ⟨alpha, halpha, C, hC⟩ := loewner_local_flow_chart hW hzpos 0
  have halpha' : ∀ w ∈ closedBall z (z.im / 4),
      alpha w 0 = w ∧
        (∀ t ∈ Icc (-E) E,
          HasDerivWithinAt (alpha w) (loewnerField W t (alpha w t))
            (Icc (-E) E) t) ∧
        ∀ t, alpha w t ∈ loewnerStrip delta := by
    simpa [E, delta] using halpha
  have hC' : ∀ t ∈ Icc (-E) E,
      LipschitzOnWith C (fun w => alpha w t) (closedBall z (z.im / 4)) := by
    simpa [E] using hC
  have htimeSubset : Icc (0 : Real) E ⊆ Icc (-E) E := by
    intro t ht
    exact ⟨(neg_nonpos.mpr hE.le).trans ht.1, ht.2⟩
  let g : ∀ w : Complex, w ∈ closedBall z (z.im / 4) ->
      LoewnerForwardSolution W w E := fun w hw =>
    { curve := alpha w
      initial := (halpha' w hw).1
      deriv := by
        intro t ht
        exact ((halpha' w hw).2.1 t (htimeSubset ht)).mono htimeSubset
      upper := by
        intro t _ht
        exact loewnerStrip_subset_upperHalfPlane hdelta ((halpha' w hw).2.2 t) }
  have hzball : z ∈ closedBall z (z.im / 4) := mem_closedBall_self hradius.le
  have hmaximal (w : Complex) (hw : w ∈ closedBall z (z.im / 4))
      (t : Real) (ht0 : 0 <= t) (htE : t < E) :
      loewnerMaximalMaps W t w = alpha w t := by
    simpa [loewnerMaximalMaps] using
      loewnerMaximalCurve_eq_forwardSolution hE (g w hw) ⟨ht0, htE⟩
  have hden (w : Complex) (hw : w ∈ closedBall z (z.im / 4)) (t : Real) :
      alpha w t - (W t : Complex) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    have himzero : (alpha w t).im = 0 := by
      simpa using congrArg Complex.im heq
    have him := mem_loewnerStrip.mp ((halpha' w hw).2.2 t)
    linarith
  let coeff : Complex -> Real -> Complex := fun w t =>
    -2 / ((alpha w t - (W t : Complex)) * (alpha z t - (W t : Complex)))
  have hfield (w : Complex) (hw : w ∈ closedBall z (z.im / 4)) (t : Real) :
      loewnerField W t (alpha w t) - loewnerField W t (alpha z t) =
        coeff w t * (alpha w t - alpha z t) := by
    have h1 := hden w hw t
    have h2 := hden z hzball t
    dsimp only [coeff]
    simp only [loewnerField_apply]
    field_simp [h1, h2]
    ring
  have hcoeffContinuous (w : Complex) (hw : w ∈ closedBall z (z.im / 4)) :
      ContinuousOn (coeff w) (Icc (0 : Real) u) := by
    have hsubE : Icc (0 : Real) u ⊆ Icc (0 : Real) E :=
      Icc_subset_Icc_right hshort.le
    have haw := (g w hw).continuousOn.mono hsubE
    have haz := (g z hzball).continuousOn.mono hsubE
    have hWcomplex : Continuous (fun t => (W t : Complex)) :=
      Complex.continuous_ofReal.comp hW
    dsimp only [coeff]
    exact continuousOn_const.div
      ((haw.sub hWcomplex.continuousOn).mul (haz.sub hWcomplex.continuousOn))
      (fun t _ht => mul_ne_zero (hden w hw t) (hden z hzball t))
  have hnormDen (w : Complex) (hw : w ∈ closedBall z (z.im / 4)) (t : Real) :
      delta <= ‖alpha w t - (W t : Complex)‖ := by
    calc
      delta <= (alpha w t).im := mem_loewnerStrip.mp ((halpha' w hw).2.2 t)
      _ = (alpha w t - (W t : Complex)).im := by simp
      _ <= ‖alpha w t - (W t : Complex)‖ := Complex.im_le_norm _
  have hcoeffBound (w : Complex) (hw : w ∈ closedBall z (z.im / 4)) (t : Real) :
      ‖coeff w t‖ <= 2 / delta ^ 2 := by
    have hprod : delta * delta <=
        ‖alpha w t - (W t : Complex)‖ * ‖alpha z t - (W t : Complex)‖ :=
      mul_le_mul (hnormDen w hw t) (hnormDen z hzball t)
        hdelta.le (norm_nonneg _)
    dsimp only [coeff]
    rw [norm_div, norm_neg, norm_ofNat, norm_mul]
    simpa [pow_two] using
      div_le_div_of_nonneg_left (show (0 : Real) <= 2 by norm_num)
        (mul_pos hdelta hdelta) hprod
  have hcoeffTendsto (t : Real) (ht : t ∈ Icc (0 : Real) u) :
      Tendsto (fun w => coeff w t) (nhds z) (nhds (coeff z t)) := by
    have htFull : t ∈ Icc (-E) E := by
      exact ⟨by linarith [ht.1], ht.2.trans hshort.le⟩
    have hat : ContinuousAt (fun w => alpha w t) z :=
      ((hC' t htFull).continuousOn z hzball).continuousAt
        (closedBall_mem_nhds z hradius)
    have hprod : ContinuousAt (fun w =>
        (alpha w t - (W t : Complex)) * (alpha z t - (W t : Complex))) z :=
      (hat.sub continuousAt_const).mul continuousAt_const
    have hprodne :
        (alpha z t - (W t : Complex)) * (alpha z t - (W t : Complex)) ≠ 0 :=
      mul_ne_zero (hden z hzball t) (hden z hzball t)
    simpa only [coeff] using (continuousAt_const.div hprod hprodne)
  have hintegral : Tendsto (fun w => ∫ t in (0 : Real)..u, coeff w t)
      (nhds z) (nhds (∫ t in (0 : Real)..u, coeff z t)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => 2 / delta ^ 2)
    · filter_upwards [closedBall_mem_nhds z hradius] with w hw
      apply ((hcoeffContinuous w hw).mono ?_).aestronglyMeasurable measurableSet_uIoc
      intro t ht
      have := uIoc_subset_uIcc ht
      simpa [uIcc_of_le hu] using this
    · filter_upwards [closedBall_mem_nhds z hradius] with w hw
      exact Filter.Eventually.of_forall (fun t _ht => hcoeffBound w hw t)
    · exact continuous_const.intervalIntegrable _ _
    · exact Filter.Eventually.of_forall (fun t ht => by
        apply hcoeffTendsto t
        have := uIoc_subset_uIcc ht
        simpa [uIcc_of_le hu] using this)
  have hdiff (w : Complex) (hw : w ∈ closedBall z (z.im / 4)) :
      alpha w u - alpha z u =
        (w - z) * Complex.exp (∫ t in (0 : Real)..u, coeff w t) := by
    have hsubE : Icc (0 : Real) u ⊆ Icc (0 : Real) E :=
      Icc_subset_Icc_right hshort.le
    have hdiffContinuous : ContinuousOn (fun t => alpha w t - alpha z t)
        (Icc (0 : Real) u) :=
      ((g w hw).continuousOn.mono hsubE).sub ((g z hzball).continuousOn.mono hsubE)
    have hdiffDeriv : ∀ t ∈ Icc (0 : Real) u,
        HasDerivWithinAt (fun s => alpha w s - alpha z s)
          (coeff w t * (alpha w t - alpha z t)) (Icc (0 : Real) u) t := by
      intro t ht
      have hraw := ((g w hw).deriv t (hsubE ht)).sub
        ((g z hzball).deriv t (hsubE ht))
      have hmono := hraw.mono hsubE
      convert hmono using 1
      exact (hfield w hw t).symm
    have hlinear := linearODE_terminal_eq_initial_mul_exp_integral hu
      (hcoeffContinuous w hw) hdiffContinuous hdiffDeriv
    simpa [(halpha' w hw).1, (halpha' z hzball).1] using hlinear
  have hslope : Filter.Eventually (fun w =>
      slope (loewnerMaximalMaps W u) z w =
        Complex.exp (∫ t in (0 : Real)..u, coeff w t))
      (nhdsWithin z ({z}ᶜ)) := by
    have hballEventually : Filter.Eventually
        (fun w => w ∈ closedBall z (z.im / 4)) (nhdsWithin z ({z}ᶜ)) :=
      by
        have hb : Filter.Eventually (fun w => w ∈ closedBall z (z.im / 4)) (nhds z) :=
          closedBall_mem_nhds z hradius
        exact hb.filter_mono inf_le_left
    have hneEventually : Filter.Eventually (fun w => w ≠ z)
        (nhdsWithin z ({z}ᶜ)) := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      simpa only [mem_compl_iff, mem_singleton_iff] using hw
    filter_upwards [hballEventually, hneEventually] with w hw hwne
    rw [slope_def_field, hmaximal w hw u hu hshort,
      hmaximal z hzball u hu hshort, hdiff w hw]
    exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hwne)
  have hexpTendsto : Tendsto
      (fun w => Complex.exp (∫ t in (0 : Real)..u, coeff w t))
      (nhdsWithin z ({z}ᶜ))
      (nhds (Complex.exp (∫ t in (0 : Real)..u, coeff z t))) :=
    (Complex.continuous_exp.continuousAt.tendsto.comp hintegral).mono_left inf_le_left
  have hderiv : HasDerivAt (loewnerMaximalMaps W u)
      (Complex.exp (∫ t in (0 : Real)..u, coeff z t)) z :=
    hasDerivAt_iff_tendsto_slope.mpr
      (hexpTendsto.congr' (hslope.mono fun _ hw => hw.symm))
  have hintegralEq : (∫ t in (0 : Real)..u, coeff z t) =
      ∫ t in (0 : Real)..u, loewnerInitialVariationalCoefficient W z t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Icc (0 : Real) u := by
      simpa [uIcc_of_le hu] using ht
    dsimp only [coeff, loewnerInitialVariationalCoefficient]
    rw [hmaximal z hzball t htIcc.1 (htIcc.2.trans_lt hshort)]
    simp only [pow_two]
  simpa [loewnerInitialJacobian, hintegralEq] using hderiv


theorem loewnerMaximalMaps_hasDerivAt_initial_zero
    {W : Real -> Real} (hW : Continuous W) {z : Complex}
    (hz : z ∈ upperHalfPlane) :
    HasDerivAt (loewnerMaximalMaps W 0) 1 z := by
  apply (hasDerivAt_id z).congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlane.mem_nhds hz] with w hw
  simpa using loewnerMaximalMaps_zero hW hw


end
end StatMech.SLE
