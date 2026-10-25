/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenCandidateAnisotropy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenCandidate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeVandermonde.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedEvenCandidateAnisotropy.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedEvenChargeBetheCandidateNormalized
    (s k : Nat) (c : Real) : Real :=
  if hc : 2 < c then
    sixVertexFixedEvenChargeBetheEigenvalueValue hc s k /
      (c ^ 2 - 2) ^ sixVertexFixedChargeBetheParticleCount (2 * s) k
  else 0


def sixVertexFixedEvenChargeBetheCandidateInfinity (s k : Nat) : Real :=
  2 * ∏ j : Fin (s + k + 1),
    sixVertexFixedEvenPositiveLimitingMNormSq s k j

end
end StatMech.FrontierD
