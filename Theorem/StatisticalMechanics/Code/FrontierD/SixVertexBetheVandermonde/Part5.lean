/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVandermonde.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSpectralIsolation
import Mathlib.LinearAlgebra.Vandermonde
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part4
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHalfFilledPairScaleProduct_ne_zero
    {c : Real} (hc : 2 < c) (k : Nat) :
    sixVertexHalfFilledPairScaleProduct k c ≠ 0 := by
  have hd : ((c ^ 2 - 2 : Real) : Complex) ≠ 0 := by
    norm_cast
    nlinarith
  unfold sixVertexHalfFilledPairScaleProduct
  exact Finset.prod_ne_zero_iff.mpr (fun i _ =>
    Finset.prod_ne_zero_iff.mpr (fun j _ => hd))

theorem sixVertexBethePairProduct_eq_scale_mul_normalized
    {c : Real} (hc : 2 < c) (k : Nat)
    (sigma : Equiv.Perm (Fin ((k + 1) + (k + 1)))) :
    sixVertexBethePairProduct c (sixVertexHalfFilledBetheRoots hc k) sigma =
      sixVertexHalfFilledPairScaleProduct k c *
        ∏ i, ∏ j ∈ Finset.Ioi i,
          sixVertexNormalizedBethePairFactor c
            (sixVertexBethePhase
              (sixVertexHalfFilledBetheRoots hc k (sigma i)))
            (sixVertexBethePhase
              (sixVertexHalfFilledBetheRoots hc k (sigma j))) := by
  have hd : ((c ^ 2 - 2 : Real) : Complex) ≠ 0 := by
    norm_cast
    nlinarith
  unfold sixVertexBethePairProduct sixVertexHalfFilledPairScaleProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  unfold sixVertexNormalizedBethePairFactor
  field_simp [hd]

theorem sixVertexBetheAmplitude_eq_scale_mul_normalized
    {c : Real} (hc : 2 < c) (k : Nat)
    (sigma : Equiv.Perm (Fin ((k + 1) + (k + 1)))) :
    sixVertexBetheAmplitude c (sixVertexHalfFilledBetheRoots hc k) sigma =
      sixVertexHalfFilledPairScaleProduct k c *
        sixVertexHalfFilledNormalizedAmplitude k c sigma := by
  unfold sixVertexBetheAmplitude sixVertexHalfFilledNormalizedAmplitude
  simp_rw [sixVertexHalfFilledBetheRootAt_eq hc]
  rw [sixVertexBethePairProduct_eq_scale_mul_normalized hc k sigma]
  ring


theorem sixVertexCoordinateBetheWave_odd_eq_scale_mul_normalized
    {c : Real} (hc : 2 < c) (k : Nat) :
    sixVertexCoordinateBetheWave c (sixVertexHalfFilledBetheRoots hc k)
        (sixVertexAlternatingOddSector
          (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (by
            unfold sixVertexFourWidth
            omega)) =
      sixVertexHalfFilledPairScaleProduct k c *
        sixVertexHalfFilledNormalizedOddWave k c := by
  unfold sixVertexCoordinateBetheWave sixVertexHalfFilledNormalizedOddWave
  simp_rw [sixVertexHalfFilledBetheRootAt_eq hc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [sixVertexBetheAmplitude_eq_scale_mul_normalized hc k sigma]
  ring


theorem exists_sixVertexHalfFilledBetheRotatedRealWave_ne_zero_of_coordinate
    {c : Real} (hc : 2 < c) (k : Nat)
    (x : SixVertexSector (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)))
    (hx : sixVertexCoordinateBetheWave c
      (sixVertexHalfFilledBetheRoots hc k) x ≠ 0) :
    ∃ a : Complex, sixVertexHalfFilledBetheRotatedRealWave hc k a ≠ 0 := by
  let z := sixVertexCoordinateBetheWave c
    (sixVertexHalfFilledBetheRoots hc k) x
  refine ⟨star z, ?_⟩
  intro hzero
  have hcoord := congrFun hzero x
  change (star z * z).re = 0 at hcoord
  have hprod : star z * z = (Complex.normSq z : Complex) := by
    calc
      star z * z = z * star z := mul_comm _ _
      _ = (Complex.normSq z : Complex) := by
        simpa only [starRingEnd_apply] using Complex.mul_conj z
  rw [hprod] at hcoord
  have hz : z ≠ 0 := hx
  norm_num at hcoord
  exact hz hcoord


theorem eventually_exists_sixVertexHalfFilledBetheRotatedRealWave_ne_zero
    (k : Nat) :
    ∀ᶠ c : Real in atTop, ∀ hc : 2 < c,
      ∃ a : Complex, sixVertexHalfFilledBetheRotatedRealWave hc k a ≠ 0 := by
  have hnormalized : ∀ᶠ c : Real in atTop,
      sixVertexHalfFilledNormalizedOddWave k c ≠ 0 :=
    (tendsto_sixVertexHalfFilledNormalizedOddWave k).eventually_ne
      (sixVertexHalfFilledVandermondeSum_ne_zero k)
  filter_upwards [hnormalized, eventually_gt_atTop (2 : Real)] with c hnonzero hc
  intro hc'
  have heval : sixVertexCoordinateBetheWave c
      (sixVertexHalfFilledBetheRoots hc' k)
      (sixVertexAlternatingOddSector
        (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (by
          unfold sixVertexFourWidth
          omega)) ≠ 0 := by
    rw [sixVertexCoordinateBetheWave_odd_eq_scale_mul_normalized hc' k]
    exact mul_ne_zero
      (sixVertexHalfFilledPairScaleProduct_ne_zero hc' k) hnonzero
  exact exists_sixVertexHalfFilledBetheRotatedRealWave_ne_zero_of_coordinate
    hc' k _ heval


theorem eventually_sixVertexHalfFilledBetheCandidateNormalized_eq_top_vandermonde
    (k : Nat) :
    ∀ᶠ c : Real in atTop,
      sixVertexHalfFilledBetheCandidateNormalized k c =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) (by
            unfold sixVertexFourWidth
            omega) c /
          (c ^ 2 - 2) ^ ((k + 1) + (k + 1)) :=
  eventually_sixVertexHalfFilledBetheCandidateNormalized_eq_top k
    (eventually_exists_sixVertexHalfFilledBetheRotatedRealWave_ne_zero k)


theorem eventually_sixVertexHalfFilledBetheCandidate_eq_top_vandermonde
    (k : Nat) :
    ∀ᶠ c : Real in atTop, ∀ hc : 2 < c,
      sixVertexSymmetricBetheEigenvalueValue c
          (sixVertexPositiveHalfBetheRoots hc k) =
        sixVertexSectorTopEigenvalue (sixVertexFourWidth 0 k)
          ((k + 1) + (k + 1)) (by
            unfold sixVertexFourWidth
            omega) c := by
  filter_upwards
    [eventually_sixVertexHalfFilledBetheCandidateNormalized_eq_top_vandermonde k,
      eventually_gt_atTop (2 : Real)] with c heq hc
  intro hc'
  rw [sixVertexHalfFilledBetheCandidateNormalized, dif_pos hc'] at heq
  have hscale : (c ^ 2 - 2) ^ ((k + 1) + (k + 1)) ≠ 0 := by
    exact pow_ne_zero _ (by nlinarith)
  field_simp [hscale] at heq
  exact heq

end
end StatMech.FrontierD
