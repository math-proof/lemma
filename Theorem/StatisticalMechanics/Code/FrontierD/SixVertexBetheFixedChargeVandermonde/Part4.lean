/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeVandermonde.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeVandermonde.Part3
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedChargePairScaleProduct_ne_zero
    {c : Real} (hc : 2 < c) (r k : Nat) :
    sixVertexFixedChargePairScaleProduct r k c ≠ 0 := by
  have hd : ((c ^ 2 - 2 : Real) : Complex) ≠ 0 := by
    norm_cast
    nlinarith
  unfold sixVertexFixedChargePairScaleProduct
  exact Finset.prod_ne_zero_iff.mpr (fun i _ =>
    Finset.prod_ne_zero_iff.mpr (fun j _ => hd))

theorem sixVertexFixedChargeBethePairProduct_eq_scale_mul_normalized
    {c : Real} (hc : 2 < c) (r k : Nat)
    (sigma : Equiv.Perm (Fin (sixVertexFixedChargeBetheParticleCount r k))) :
    sixVertexBethePairProduct c (sixVertexFixedChargeBetheRoots hc r k) sigma =
      sixVertexFixedChargePairScaleProduct r k c *
        ∏ i, ∏ j ∈ Finset.Ioi i,
          sixVertexNormalizedBethePairFactor c
            (sixVertexBethePhase
              (sixVertexFixedChargeBetheRoots hc r k (sigma i)))
            (sixVertexBethePhase
              (sixVertexFixedChargeBetheRoots hc r k (sigma j))) := by
  have hd : ((c ^ 2 - 2 : Real) : Complex) ≠ 0 := by
    norm_cast
    nlinarith
  unfold sixVertexBethePairProduct sixVertexFixedChargePairScaleProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  unfold sixVertexNormalizedBethePairFactor
  field_simp [hd]

theorem sixVertexFixedChargeBetheAmplitude_eq_scale_mul_normalized
    {c : Real} (hc : 2 < c) (r k : Nat)
    (sigma : Equiv.Perm (Fin (sixVertexFixedChargeBetheParticleCount r k))) :
    sixVertexBetheAmplitude c (sixVertexFixedChargeBetheRoots hc r k) sigma =
      sixVertexFixedChargePairScaleProduct r k c *
        sixVertexFixedChargeNormalizedAmplitude r k c sigma := by
  unfold sixVertexBetheAmplitude sixVertexFixedChargeNormalizedAmplitude
  simp_rw [sixVertexFixedChargeBetheRootAt_eq hc]
  rw [sixVertexFixedChargeBethePairProduct_eq_scale_mul_normalized hc r k sigma]
  ring

theorem sixVertexFixedChargeCoordinateBetheWave_alternating_eq
    {c : Real} (hc : 2 < c) (r k : Nat) :
    sixVertexCoordinateBetheWave c (sixVertexFixedChargeBetheRoots hc r k)
        (sixVertexAlternatingOddSector
          (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k)
          (sixVertexFixedChargeBetheParticleCount_twice_le r k)) =
      sixVertexFixedChargePairScaleProduct r k c *
        sixVertexFixedChargeNormalizedAlternatingWave r k c := by
  unfold sixVertexCoordinateBetheWave
    sixVertexFixedChargeNormalizedAlternatingWave
  simp_rw [sixVertexFixedChargeBetheRootAt_eq hc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [sixVertexFixedChargeBetheAmplitude_eq_scale_mul_normalized hc r k sigma]
  ring

theorem eventually_sixVertexFixedChargeCoordinateBetheWave_ne_zero
    (r k : Nat) :
    ∀ᶠ c : Real in atTop, ∀ hc : 2 < c,
      sixVertexCoordinateBetheWave (N := sixVertexFourWidth r k) c
        (sixVertexFixedChargeBetheRoots hc r k) ≠ 0 := by
  have hnormalized : ∀ᶠ c : Real in atTop,
      sixVertexFixedChargeNormalizedAlternatingWave r k c ≠ 0 :=
    (tendsto_sixVertexFixedChargeNormalizedAlternatingWave r k).eventually_ne
      (sixVertexFixedChargeVandermondeSum_ne_zero r k)
  filter_upwards [hnormalized, eventually_gt_atTop (2 : Real)] with
      c hnonzero hc
  intro hc' hwave
  have heval := congrFun hwave
    (sixVertexAlternatingOddSector
      (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)
      (sixVertexFixedChargeBetheParticleCount_twice_le r k))
  rw [sixVertexFixedChargeCoordinateBetheWave_alternating_eq hc' r k] at heval
  exact (mul_ne_zero
    (sixVertexFixedChargePairScaleProduct_ne_zero hc' r k) hnonzero) heval

end
end StatMech.FrontierD
