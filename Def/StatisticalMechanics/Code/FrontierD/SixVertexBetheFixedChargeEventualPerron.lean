/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeEventualPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargePerronIdentification
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeRotatedNormalizedWave (r k : Nat) (c : Real) :
    SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k) -> Real :=
  fun x => ((-Complex.I) ^ sixVertexFixedChargeBethePairCount r k *
    sixVertexFixedChargeNormalizedWave r k c x).re

def sixVertexFixedChargeRotatedLimitingWave (r k : Nat) :
    SixVertexSector (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheParticleCount r k) -> Real :=
  fun x => ((-Complex.I) ^ sixVertexFixedChargeBethePairCount r k *
    sixVertexFixedChargeLimitingWave r k x).re

end
end StatMech.FrontierD
