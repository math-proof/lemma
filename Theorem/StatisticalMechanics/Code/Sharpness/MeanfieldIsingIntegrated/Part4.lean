/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldIsingIntegrated.Part4
open MeasureTheory Real Set Filter Topology
open scoped BigOperators Interval


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising


theorem continuousOn_sctMeanfieldIntegratedError
    (d n : ℕ) (h : ℝ) (hh : 0 < h) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (sctMeanfieldIntegratedError d n h) (Icc a b) := by
  unfold sctMeanfieldIntegratedError
  exact ((((continuousOn_const.mul continuousOn_id).mul
      (continuousOn_const.sub (continuousOn_sctLatticeC_beta d n h hh ha))).mul
        (continuousOn_const.sub
          ((continuous_sctOriginMag_beta d n h).continuousOn.pow 2))).add
    ((((continuousOn_const.mul (continuousOn_id.pow 2)).mul
      (continuousOn_sctLatticeC_beta d n h hh ha)).mul
        (continuous_sctBoundaryCovarianceError_beta d n h).continuousOn)))


theorem sctMeanfieldGDeriv_le_integratedError
    {d n : ℕ} (beta h : ℝ) (hn : 1 ≤ n)
    (hbdd : BddAbove (tildeBetaCIsingSet d))
    (habove : tildeBetaCIsing d < beta) (hh : 0 < h) :
    sctMeanfieldGDeriv d n h beta ≤
      sctMeanfieldIntegratedError d n h beta := by
  have hzero : (0 : ℝ) ∈ tildeBetaCIsingSet d := by
    refine ⟨le_rfl, {Percolation.origin d}, by simp, ?_⟩
    simp [phiIsing]
  have hcrit0 : 0 ≤ tildeBetaCIsing d := by
    unfold tildeBetaCIsing
    exact le_csSup hbdd hzero
  have hbeta : 0 < beta := lt_of_le_of_lt hcrit0 habove
  have hphi : ∀ S : Finset (Site d), Percolation.origin d ∈ S ->
      1 ≤ phiIsing d beta S :=
    si4_phiIsing_ge_one_above_tildeBc d beta hbeta.le hbdd habove
  have hfin := sct_finite_meanfield_inequality_concrete beta h 1 hn hbeta hh hphi
  rw [deriv_sctOriginMag_sq_beta] at hfin
  simp only [one_mul] at hfin
  have hmul := mul_le_mul_of_nonneg_left hfin (sq_nonneg beta)
  have hcancel :
      beta ^ 2 *
          (2 * sctLatticeC d beta h n *
            ((1 / beta) *
                (1 - (sctOriginMag d beta h n) ^ 2) -
              sctBoundaryCovarianceError d beta h n)) =
        2 * beta * sctLatticeC d beta h n *
            (1 - (sctOriginMag d beta h n) ^ 2) -
          2 * beta ^ 2 * sctLatticeC d beta h n *
            sctBoundaryCovarianceError d beta h n := by
    field_simp [hbeta.ne']
    <;> ring
  rw [hcancel] at hmul
  unfold sctMeanfieldGDeriv sctMeanfieldIntegratedError
  linarith


theorem sctMeanfieldG_sub_le_integral_error
    {d n : ℕ} {a b h : ℝ} (hn : 1 ≤ n) (hab : a ≤ b)
    (ha : 0 < a) (hh : 0 < h)
    (hbdd : BddAbove (tildeBetaCIsingSet d))
    (hcrit : tildeBetaCIsing d < a) :
    sctMeanfieldG d n h b - sctMeanfieldG d n h a ≤
      ∫ gamma in a..b, sctMeanfieldIntegratedError d n h gamma := by
  have hftc :
      (∫ gamma in a..b, sctMeanfieldGDeriv d n h gamma) =
        sctMeanfieldG d n h b - sctMeanfieldG d n h a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro gamma hgamma
      exact hasDerivAt_sctMeanfieldG d n h gamma
    · exact (continuous_sctMeanfieldGDeriv d n h).intervalIntegrable a b
  rw [← hftc]
  apply intervalIntegral.integral_mono_on hab
  · exact (continuous_sctMeanfieldGDeriv d n h).intervalIntegrable a b
  · apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using
      (continuousOn_sctMeanfieldIntegratedError d n h hh ha)
  · intro gamma hgamma
    exact sctMeanfieldGDeriv_le_integratedError gamma h hn hbdd
      (hcrit.trans_le hgamma.1) hh


theorem sctBoundaryCovarianceError_le_uniform
    {d n : ℕ} (beta h : ℝ) (hn : 1 ≤ n)
    (hbeta : 0 < beta) (hh : 0 < h) :
    sctBoundaryCovarianceError d beta h n ≤
      (2 * d : ℝ) / (beta * h) := by
  have houter := sctBoundaryCovarianceError_le_outer d beta h
    hbeta.le hh.le n hn
  have hann := sctOuterCovarianceSum_le_magDiff d beta h hbeta hh n
  have hcoef : (0 : ℝ) ≤ (2 * d : ℝ) := by positivity
  have hden : 0 < beta * h := mul_pos hbeta hh
  have hm0 : 0 ≤ sctOriginMag d beta h (n - 1) :=
    (sctOriginMag_pos d beta h hbeta hh (n - 1)).le
  have hm1 : sctOriginMag d beta h n ≤ 1 :=
    sctOriginMag_le_one d beta h n
  calc
    sctBoundaryCovarianceError d beta h n
        ≤ (2 * d : ℝ) * sctOuterCovarianceSum d beta h n := houter
    _ ≤ (2 * d : ℝ) *
        ((sctOriginMag d beta h n - sctOriginMag d beta h (n - 1)) /
          (beta * h)) := mul_le_mul_of_nonneg_left hann hcoef
    _ ≤ (2 * d : ℝ) * (1 / (beta * h)) := by
      apply mul_le_mul_of_nonneg_left _ hcoef
      exact div_le_div_of_nonneg_right (by linarith) hden.le
    _ = (2 * d : ℝ) / (beta * h) := by ring


theorem sctMeanfieldIntegratedError_tendsto_zero
    (d : ℕ) (beta h : ℝ) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto
      (fun k : ℕ => sctMeanfieldIntegratedError d (k + 1) h beta)
      atTop (nhds 0) := by
  have hc := (sctLatticeC_tendsto_one d beta h hbeta hh).comp
    (tendsto_add_atTop_nat 1)
  have hm := (sctOriginMag_tendsto_iSup d beta h hbeta.le hh.le).comp
    (tendsto_add_atTop_nat 1)
  have heps := (sctBoundaryCovarianceError_tendsto_zero d beta h hbeta hh).comp
    (tendsto_add_atTop_nat 1)
  have hfirst : Tendsto
      (fun k : ℕ =>
        2 * beta * (1 - sctLatticeC d beta h (k + 1)) *
          (1 - (sctOriginMag d beta h (k + 1)) ^ 2))
      atTop (nhds 0) := by
    convert ((tendsto_const_nhds.mul (tendsto_const_nhds.sub hc)).mul
      (tendsto_const_nhds.sub (hm.pow 2))) using 1 <;> simp
  have hsecond : Tendsto
      (fun k : ℕ =>
        2 * beta ^ 2 * sctLatticeC d beta h (k + 1) *
          sctBoundaryCovarianceError d beta h (k + 1))
      atTop (nhds 0) := by
    convert ((tendsto_const_nhds.mul hc).mul heps) using 1 <;> simp
  simpa only [sctMeanfieldIntegratedError, zero_add] using hfirst.add hsecond


theorem norm_sctMeanfieldIntegratedError_le
    {d n : ℕ} {a b h beta : ℝ} (hn : 1 ≤ n)
    (hab : a ≤ beta) (hbetab : beta ≤ b) (ha : 0 < a) (hh : 0 < h) :
    ‖sctMeanfieldIntegratedError d n h beta‖ ≤
      2 * b + 2 * b ^ 2 * ((2 * d : ℝ) / (a * h)) := by
  have hbeta : 0 < beta := ha.trans_le hab
  have hb : 0 < b := hbeta.trans_le hbetab
  have hc0 := sctLatticeC_nonneg beta h hbeta hh (d := d) (n := n)
  have hc1 := sctLatticeC_le_one d beta h hbeta hh n
  have hm0 := (sctOriginMag_pos d beta h hbeta hh n).le
  have hm1 := sctOriginMag_le_one d beta h n
  have he0 := sctBoundaryCovarianceError_nonneg d beta h hbeta.le hh.le n
  have he1 := sctBoundaryCovarianceError_le_uniform
    (d := d) (n := n) beta h hn hbeta hh
  have hdenA : 0 < a * h := mul_pos ha hh
  have hdenB : 0 < beta * h := mul_pos hbeta hh
  have hdiv : (2 * d : ℝ) / (beta * h) ≤ (2 * d : ℝ) / (a * h) := by
    apply div_le_div_of_nonneg_left (by positivity) hdenA
    exact mul_le_mul_of_nonneg_right hab hh.le
  have he : sctBoundaryCovarianceError d beta h n ≤
      (2 * d : ℝ) / (a * h) := he1.trans hdiv
  have hu0 : 0 ≤ 1 - (sctOriginMag d beta h n) ^ 2 := by
    nlinarith [sq_nonneg (sctOriginMag d beta h n)]
  have hu1 : 1 - (sctOriginMag d beta h n) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (sctOriginMag d beta h n)]
  have herr0 : 0 ≤ sctMeanfieldIntegratedError d n h beta := by
    unfold sctMeanfieldIntegratedError
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg herr0]
  unfold sctMeanfieldIntegratedError
  have hfirst :
      2 * beta * (1 - sctLatticeC d beta h n) *
          (1 - (sctOriginMag d beta h n) ^ 2) ≤ 2 * b := by
    have hcsub0 : 0 ≤ 1 - sctLatticeC d beta h n := sub_nonneg.mpr hc1
    have hcsub1 : 1 - sctLatticeC d beta h n ≤ 1 := by linarith
    have h2beta : 2 * beta ≤ 2 * b := by linarith
    calc
      2 * beta * (1 - sctLatticeC d beta h n) *
          (1 - (sctOriginMag d beta h n) ^ 2)
          ≤ 2 * b * (1 - sctLatticeC d beta h n) *
              (1 - (sctOriginMag d beta h n) ^ 2) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right h2beta hcsub0) hu0
      _ ≤ 2 * b * 1 * (1 - (sctOriginMag d beta h n) ^ 2) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcsub1 (by positivity)) hu0
      _ ≤ 2 * b * 1 * 1 := by
            exact mul_le_mul_of_nonneg_left hu1 (by positivity)
      _ = 2 * b := by ring
  have hsecond :
      2 * beta ^ 2 * sctLatticeC d beta h n *
          sctBoundaryCovarianceError d beta h n ≤
        2 * b ^ 2 * ((2 * d : ℝ) / (a * h)) := by
    have hb2 : beta ^ 2 ≤ b ^ 2 := by nlinarith
    have hq0 : 0 ≤ (2 * d : ℝ) / (a * h) := by positivity
    calc
      2 * beta ^ 2 * sctLatticeC d beta h n *
          sctBoundaryCovarianceError d beta h n
          ≤ 2 * b ^ 2 * sctLatticeC d beta h n *
              sctBoundaryCovarianceError d beta h n := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hb2 (by norm_num)) hc0) he0
      _ ≤ 2 * b ^ 2 * 1 * sctBoundaryCovarianceError d beta h n := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hc1 (by positivity)) he0
      _ ≤ 2 * b ^ 2 * 1 * ((2 * d : ℝ) / (a * h)) := by
            exact mul_le_mul_of_nonneg_left he (by positivity)
      _ = 2 * b ^ 2 * ((2 * d : ℝ) / (a * h)) := by ring
  linarith


theorem sctMeanfieldIntegratedError_integral_tendsto_zero
    (d : ℕ) {a b h : ℝ} (hab : a ≤ b) (ha : 0 < a) (hh : 0 < h) :
    Tendsto
      (fun k : ℕ =>
        ∫ beta in a..b, sctMeanfieldIntegratedError d (k + 1) h beta)
      atTop (nhds 0) := by
  let K : ℝ := 2 * b + 2 * b ^ 2 * ((2 * d : ℝ) / (a * h))
  have hlim : Tendsto
      (fun k : ℕ =>
        ∫ beta in a..b, sctMeanfieldIntegratedError d (k + 1) h beta)
      atTop (nhds (∫ _beta in a..b, (0 : ℝ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => K)
    · exact Filter.Eventually.of_forall (fun k => by
        apply ContinuousOn.aestronglyMeasurable
        · exact (continuousOn_sctMeanfieldIntegratedError d (k + 1) h hh ha).mono
            (by simpa [uIoc_of_le hab] using
              (show Ioc a b ⊆ Icc a b by intro x hx; exact ⟨hx.1.le, hx.2⟩))
        · exact measurableSet_uIoc)
    · exact Filter.Eventually.of_forall (fun k =>
        Filter.Eventually.of_forall (fun beta hbeta => by
          rw [uIoc_of_le hab] at hbeta
          exact norm_sctMeanfieldIntegratedError_le
            (Nat.succ_le_succ (Nat.zero_le k)) hbeta.1.le hbeta.2 ha hh))
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall (fun beta hbeta => by
        rw [uIoc_of_le hab] at hbeta
        exact sctMeanfieldIntegratedError_tendsto_zero d beta h
          (ha.trans hbeta.1) hh)
  simpa using hlim


end Sharpness
end StatMech
