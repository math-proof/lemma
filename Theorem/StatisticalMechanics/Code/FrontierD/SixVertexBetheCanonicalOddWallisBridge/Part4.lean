/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisCore.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisBridge.Part3


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

theorem tendsto_sixVertexCanonicalOddWallisProductArgument_of_comparison
    {c : Real} (hc : 2 < c) (s : Nat)
    (hcomparison : SixVertexCanonicalOddGeneralizedWallisComparison hc s) :
    Tendsto (sixVertexCanonicalOddWallisProductArgument hc s) atTop
      (nhds (Real.cosh (sixVertexAntiferroelectricLambda c))) := by
  let rho0 := sixVertexFourierPhysicalDensity c hc 0
  let A : Nat -> Real := fun k =>
    sixVertexCanonicalOddZeroPrefactorNormalized hc s k / 2
  let B : Nat -> Real := fun k =>
    (sixVertexFourWidth (2 * s + 1) k : Real) *
      sixVertexOddWallisHalfProduct (s + k + 1) ^ 2
  let R : Nat -> Real := fun k =>
    sixVertexCanonicalOddWallisProductRatio hc s k ^ 2
  have hA : Tendsto A atTop
      (nhds ((c ^ 2 * (2 * Real.pi) * rho0) / 2)) :=
    (tendsto_sixVertexCanonicalOddZeroPrefactorNormalized hc s).div_const 2
  have hB : Tendsto B atTop (nhds (4 / Real.pi)) :=
    tendsto_sixVertexOddWallisReferenceProduct_bridge s
  have hR : Tendsto R atTop
      (nhds (Real.cosh (sixVertexAntiferroelectricLambda c) /
        (4 * c ^ 2 * rho0))) := hcomparison
  have hmul := (hA.mul hB).mul hR
  have hlimit :
      (c ^ 2 * (2 * Real.pi) * rho0 / 2) * (4 / Real.pi) *
          (Real.cosh (sixVertexAntiferroelectricLambda c) /
            (4 * c ^ 2 * rho0)) =
        Real.cosh (sixVertexAntiferroelectricLambda c) := by
    have hc0 : c ≠ 0 := by linarith
    have hrho : rho0 ≠ 0 := (sixVertexFourierPhysicalDensity_pos hc 0).ne'
    field_simp [hc0, hrho, Real.pi_ne_zero]
  rw [hlimit] at hmul
  apply hmul.congr'
  filter_upwards [] with k
  have hN : (sixVertexFourWidth (2 * s + 1) k : Real) ≠ 0 := by
    exact_mod_cast (sixVertexFourWidth_pos (2 * s + 1) k).ne'
  have href : sixVertexOddWallisHalfProduct (s + k + 1) ≠ 0 :=
    ne_of_gt (Finset.prod_pos fun j hj => div_pos (by positivity) (by positivity))
  unfold A B R sixVertexCanonicalOddWallisProductArgument
    sixVertexCanonicalOddWallisProductRatio
    sixVertexCanonicalOddZeroPrefactorNormalized
  field_simp [hN, href]

theorem sixVertexCanonicalOddZeroModeWallisLimit_of_comparison
    {c : Real} (hc : 2 < c) (s : Nat)
    (hcomparison : SixVertexCanonicalOddGeneralizedWallisComparison hc s) :
    SixVertexCanonicalOddZeroModeWallisLimit hc s := by
  have harg :=
    tendsto_sixVertexCanonicalOddWallisProductArgument_of_comparison
      hc s hcomparison
  have hlog : Tendsto (fun k => Real.log
      (sixVertexCanonicalOddWallisProductArgument hc s k)) atTop
      (nhds (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)))) :=
    (Real.continuousAt_log (Real.cosh_pos _).ne').tendsto.comp harg
  unfold SixVertexCanonicalOddZeroModeWallisLimit
  apply hlog.congr'
  filter_upwards
    [eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s]
      with k hk
  exact (sixVertexCanonicalOddZeroModeWallisCorrection_eq_log_product
    hc s k hk).symm

theorem sixVertexCanonicalFixedOddCharge_matchesOffsetFourier_of_comparison
    {c : Real} (hc : 2 < c) (s : Nat)
    (hcomparison : SixVertexCanonicalOddGeneralizedWallisComparison hc s) :
    SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc
      (2 * s + 1) := by
  exact sixVertexCanonicalFixedOddCharge_matchesOffsetFourier_of_three_limits
    hc s
    (by
      simpa [Nat.cast_add, Nat.cast_mul] using
        tendsto_sixVertexCanonicalOddBulkLogDisplacement hc s)
    (sixVertexCanonicalOddZeroModeWallisLimit_of_comparison hc s hcomparison)
    (by
      simpa [sixVertexCanonicalOddBoundaryLogSum] using
        tendsto_sum_sixVertexCanonicalOddBoundaryLogObservable hc s)

end
end StatMech.FrontierD
