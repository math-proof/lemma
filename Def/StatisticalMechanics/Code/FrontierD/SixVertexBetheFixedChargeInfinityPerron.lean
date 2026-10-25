/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeInfinityPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityEigenrelation
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeInfinityPositive.Part2
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargePositiveInfinityWave (r k : Nat) :
    SixVertexNoAdjacentSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k) -> Real :=
  fun x => ((-Complex.I) ^ sixVertexFixedChargeBethePairCount r k *
    sixVertexFixedChargeLimitingWave r k x.1).re

end
end StatMech.FrontierD
