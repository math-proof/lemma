/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityWave.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeSpectralBranch
import Mathlib.LinearAlgebra.Vandermonde
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeLimitingMonomial (r k : Nat)
    (sigma : Equiv.Perm
      (Fin (sixVertexFixedChargeBetheParticleCount r k)))
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) : Complex :=
  ∏ i, sixVertexFixedChargeLimitingPhase r k (sigma i) ^
    (sixVertexSectorPosition x i).val


def sixVertexFixedChargeNormalizedWave (r k : Nat) (c : Real)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) : Complex :=
  ∑ sigma : Equiv.Perm
      (Fin (sixVertexFixedChargeBetheParticleCount r k)),
    sixVertexFixedChargeNormalizedAmplitude r k c sigma *
      sixVertexBetheMonomial
        (fun j => sixVertexFixedChargeBetheRootAt r k j c) sigma x


def sixVertexFixedChargeLimitingWave (r k : Nat)
    (x : SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k)) : Complex :=
  ∑ sigma : Equiv.Perm
      (Fin (sixVertexFixedChargeBetheParticleCount r k)),
    (((Equiv.Perm.sign sigma : Int) : Complex)) *
      (∏ i, ∏ _j ∈ Finset.Ioi i,
        sixVertexFixedChargeLimitingPhase r k (sigma i)) *
      sixVertexFixedChargeLimitingMonomial r k sigma x

end
end StatMech.FrontierD
