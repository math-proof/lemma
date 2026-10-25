/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityWave.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeSpectralBranch
import Mathlib.LinearAlgebra.Vandermonde
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityWave.Part2
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedChargeLimitingPairProduct_eq
    (r k : Nat)
    (sigma : Equiv.Perm
      (Fin (sixVertexFixedChargeBetheParticleCount r k))) :
    (∏ i, ∏ _j ∈ Finset.Ioi i,
        sixVertexFixedChargeLimitingPhase r k (sigma i)) =
      ∏ i, sixVertexFixedChargeLimitingPhase r k (sigma i) ^
        (sixVertexFixedChargeBetheParticleCount r k - 1 - i.val) := by
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_const, Fin.card_Ioi]

theorem sixVertexFixedChargeLimitingWave_eq_alternant
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    sixVertexFixedChargeLimitingWave r k x =
      ∑ sigma : Equiv.Perm
          (Fin (sixVertexFixedChargeBetheParticleCount r k)),
        (((Equiv.Perm.sign sigma : Int) : Complex)) *
          ∏ i, sixVertexFixedChargeLimitingPhase r k (sigma i) ^
            sixVertexFixedChargeAlternantExponent r k x i := by
  unfold sixVertexFixedChargeLimitingWave
    sixVertexFixedChargeLimitingMonomial
  apply Finset.sum_congr rfl
  intro sigma _
  rw [sixVertexFixedChargeLimitingPairProduct_eq]
  rw [mul_assoc]
  rw [← Finset.prod_mul_distrib]
  apply congrArg (fun z : Complex =>
    (((Equiv.Perm.sign sigma : Int) : Complex)) * z)
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_add]
  congr 1
  unfold sixVertexFixedChargeAlternantExponent
  omega


end
end StatMech.FrontierD
