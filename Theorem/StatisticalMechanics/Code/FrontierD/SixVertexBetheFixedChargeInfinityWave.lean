/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityWave.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeSpectralBranch
import Mathlib.LinearAlgebra.Vandermonde
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityWave
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexFixedChargeLimitingMonomial
    (r k : Nat)
    (sigma : Equiv.Perm
      (Fin (sixVertexFixedChargeBetheParticleCount r k)))
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    Tendsto
      (fun c => sixVertexBetheMonomial
        (fun j => sixVertexFixedChargeBetheRootAt r k j c) sigma x)
      atTop (nhds (sixVertexFixedChargeLimitingMonomial r k sigma x)) := by
  unfold sixVertexBetheMonomial sixVertexFixedChargeLimitingMonomial
  apply tendsto_finsetProd Finset.univ
  intro i _
  exact (tendsto_sixVertexFixedChargeBethePhaseAt r k (sigma i)).pow
    (sixVertexSectorPosition x i).val

theorem tendsto_sixVertexFixedChargeNormalizedWave
    (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) :
    Tendsto (fun c => sixVertexFixedChargeNormalizedWave r k c x) atTop
      (nhds (sixVertexFixedChargeLimitingWave r k x)) := by
  unfold sixVertexFixedChargeNormalizedWave sixVertexFixedChargeLimitingWave
  apply tendsto_finsetSum Finset.univ
  intro sigma _
  exact (tendsto_sixVertexFixedChargeNormalizedAmplitude r k sigma).mul
    (tendsto_sixVertexFixedChargeLimitingMonomial r k sigma x)


end
end StatMech.FrontierD
