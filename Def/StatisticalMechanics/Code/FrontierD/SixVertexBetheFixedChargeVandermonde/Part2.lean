/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeVandermonde.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeVandermonde.Part2
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeNormalizedAlternatingWave
    (r k : Nat) (c : Real) : Complex :=
  ∑ sigma : Equiv.Perm (Fin (sixVertexFixedChargeBetheParticleCount r k)),
    sixVertexFixedChargeNormalizedAmplitude r k c sigma *
      sixVertexBetheMonomial
        (fun j => sixVertexFixedChargeBetheRootAt r k j c) sigma
        (sixVertexAlternatingOddSector
          (sixVertexFourWidth r k)
          (sixVertexFixedChargeBetheParticleCount r k)
          (sixVertexFixedChargeBetheParticleCount_twice_le r k))

def sixVertexFixedChargeVandermondeSum (r k : Nat) : Complex :=
  ∑ sigma : Equiv.Perm (Fin (sixVertexFixedChargeBetheParticleCount r k)),
    (((Equiv.Perm.sign sigma : Int) : Complex)) *
      (∏ i, ∏ _j ∈ Finset.Ioi i,
        sixVertexFixedChargeLimitingPhase r k (sigma i)) *
      ∏ i, sixVertexFixedChargeLimitingPhase r k (sigma i) ^
        (2 * i.val + 1)

end
end StatMech.FrontierD
