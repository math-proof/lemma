/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeAnisotropyRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeAnisotropyRoots.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeLimitingRoot (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) : Real :=
  (2 * Real.pi * sixVertexCentralQuantumNumber j) /
    (sixVertexFixedChargeBetheComplementCount r k : Real)


def sixVertexFixedChargeLimitingPhase (r k : Nat)
    (j : Fin (sixVertexFixedChargeBetheParticleCount r k)) : Complex :=
  sixVertexBethePhase (sixVertexFixedChargeLimitingRoot r k j)

end
end StatMech.FrontierD
