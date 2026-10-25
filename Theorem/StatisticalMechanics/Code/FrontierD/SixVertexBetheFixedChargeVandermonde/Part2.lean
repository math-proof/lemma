/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeVandermonde.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeVandermonde
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexFixedChargeNormalizedAmplitude (r k : Nat)
    (sigma : Equiv.Perm (Fin (sixVertexFixedChargeBetheParticleCount r k))) :
    Tendsto (sixVertexFixedChargeNormalizedAmplitude r k · sigma) atTop
      (nhds ((((Equiv.Perm.sign sigma : Int) : Complex)) *
        ∏ i, ∏ _j ∈ Finset.Ioi i,
          sixVertexFixedChargeLimitingPhase r k (sigma i))) := by
  unfold sixVertexFixedChargeNormalizedAmplitude
  apply tendsto_const_nhds.mul
  apply tendsto_finsetProd Finset.univ
  intro i _
  apply tendsto_finsetProd (Finset.Ioi i)
  intro j _
  exact tendsto_sixVertexFixedChargeNormalizedBethePairFactorAt
    r k (sigma i) (sigma j)

theorem tendsto_sixVertexFixedChargeAlternatingMonomial
    (r k : Nat)
    (sigma : Equiv.Perm (Fin (sixVertexFixedChargeBetheParticleCount r k))) :
    Tendsto
      (fun c => sixVertexBetheMonomial
        (fun j => sixVertexFixedChargeBetheRootAt r k j c) sigma
        (sixVertexAlternatingOddSector
          (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k)
          (sixVertexFixedChargeBetheParticleCount_twice_le r k)))
      atTop
      (nhds (∏ i, sixVertexFixedChargeLimitingPhase r k (sigma i) ^
        (2 * i.val + 1))) := by
  unfold sixVertexBetheMonomial
  simp only [sixVertexSectorPosition_alternatingOdd_apply_val]
  apply tendsto_finsetProd Finset.univ
  intro i _
  exact (tendsto_sixVertexFixedChargeBethePhaseAt r k (sigma i)).pow
    (2 * i.val + 1)

end
end StatMech.FrontierD
