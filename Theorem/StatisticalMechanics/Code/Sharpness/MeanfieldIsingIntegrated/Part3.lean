/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState.Part2
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldIsingIntegrated.Part3
open MeasureTheory Real Set Filter Topology
open scoped BigOperators Interval


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising


theorem hasDerivAt_sctMeanfieldG (d n : ℕ) (h beta : ℝ) :
    HasDerivAt (sctMeanfieldG d n h)
      (sctMeanfieldGDeriv d n h beta) beta := by
  have hp : HasDerivAt (fun b : ℝ => b ^ 2) (2 * beta) beta := by
    simpa using hasDerivAt_pow 2 beta
  have hm := hasDerivAt_sctOriginMag_sq_beta d n h beta
  have hs : HasDerivAt (fun b => 1 - (sctOriginMag d b h n) ^ 2)
      (-sctOriginMagSqBetaDeriv d n h beta) beta := by
    simpa using (hasDerivAt_const beta (1 : ℝ)).sub hm
  convert hp.mul hs using 1 <;> simp [sctMeanfieldG, sctMeanfieldGDeriv] <;> ring


theorem continuous_isingExpectation_beta
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : ℝ)
    (f : ConfigSpace V → ℝ) :
    Continuous (fun beta => isingExpectation G beta h f) := by
  rw [continuous_iff_continuousAt]
  intro beta
  exact (hasDerivAt_expectation_beta G beta h f).continuousAt

theorem continuous_sctBoxMag_beta (d n : ℕ) (h : ℝ) (x : sctBox d n) :
    Continuous (fun beta => sctBoxMag d beta h n x) :=
  continuous_isingExpectation_beta (sctBoxGraph d n) h (fun s => spin s x)

theorem continuous_sctOriginMag_beta (d n : ℕ) (h : ℝ) :
    Continuous (fun beta => sctOriginMag d beta h n) :=
  continuous_sctBoxMag_beta d n h (sctBoxOrigin d n)

theorem continuous_sctOriginMagBetaDeriv (d n : ℕ) (h : ℝ) :
    Continuous (sctOriginMagBetaDeriv d n h) := by
  unfold sctOriginMagBetaDeriv
  exact
    (continuous_isingExpectation_beta (sctBoxGraph d n) h
      (fun s => spin s (sctBoxOrigin d n) * negHam (sctBoxGraph d n) h s)).sub
    ((continuous_sctOriginMag_beta d n h).mul
      (continuous_isingExpectation_beta (sctBoxGraph d n) h
        (negHam (sctBoxGraph d n) h)))

theorem continuous_sctOriginMagSqBetaDeriv (d n : ℕ) (h : ℝ) :
    Continuous (sctOriginMagSqBetaDeriv d n h) := by
  unfold sctOriginMagSqBetaDeriv
  exact (continuous_const.mul (continuous_sctOriginMag_beta d n h)).mul
    (continuous_sctOriginMagBetaDeriv d n h)

theorem continuous_sctMeanfieldGDeriv (d n : ℕ) (h : ℝ) :
    Continuous (sctMeanfieldGDeriv d n h) := by
  unfold sctMeanfieldGDeriv
  exact ((continuous_const.mul continuous_id).mul
      (continuous_const.sub ((continuous_sctOriginMag_beta d n h).pow 2))).sub
    (((continuous_id.pow 2)).mul (continuous_sctOriginMagSqBetaDeriv d n h))


theorem continuousOn_sctLatticeC_beta (d n : ℕ) (h : ℝ) (hh : 0 < h)
    {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun beta => sctLatticeC d beta h n) (Icc a b) := by
  unfold sctLatticeC sct_cInfDep
  apply ContinuousOn.finset_inf'_apply (sctBoxSites_nonempty d n)
  intro x hx
  apply ContinuousOn.div
  · exact (continuous_sctOriginMag_beta d n h).continuousOn
  · exact (continuous_sctBoxMag_beta d n h x).continuousOn
  · intro beta hbeta
    exact (sctBoxMag_pos d beta h (ha.trans_le hbeta.1) hh n x).ne'

theorem continuous_sctBoxCovariance_beta (d n : ℕ) (h : ℝ) (x : sctBox d n) :
    Continuous (fun beta => sctBoxCovariance d beta h n x) := by
  unfold sctBoxCovariance sctOriginMag sctBoxMag
  exact
    (continuous_isingExpectation_beta (sctBoxGraph d n) h
      (fun s => spin s (sctBoxOrigin d n) * spin s x)).sub
    ((continuous_isingExpectation_beta (sctBoxGraph d n) h
      (fun s => spin s (sctBoxOrigin d n))).mul
      (continuous_isingExpectation_beta (sctBoxGraph d n) h
        (fun s => spin s x)))

theorem continuous_sctBoundaryCovarianceError_beta (d n : ℕ) (h : ℝ) :
    Continuous (fun beta => sctBoundaryCovarianceError d beta h n) := by
  unfold sctBoundaryCovarianceError
  exact continuous_finset_sum Finset.univ (fun x _ =>
    continuous_const.mul (continuous_sctBoxCovariance_beta d n h x))


end Sharpness
end StatMech
