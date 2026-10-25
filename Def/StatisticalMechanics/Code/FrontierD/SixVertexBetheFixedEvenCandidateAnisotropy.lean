/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedEvenCandidateAnisotropy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenCandidate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeVandermonde.Part4
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedEvenPositiveBetheIndex (s k : Nat) (j : Fin (s + k + 1)) :
    Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k) :=
  Fin.cast (sixVertexFixedEvenChargeBetheParticleCount_eq s k).symm
    (Fin.natAdd (s + k + 1) j)


def sixVertexFixedEvenPositiveBetheRootAt (s k : Nat)
    (j : Fin (s + k + 1)) (c : Real) : Real :=
  sixVertexFixedChargeBetheRootAt (2 * s) k
    (sixVertexFixedEvenPositiveBetheIndex s k j) c


def sixVertexFixedEvenPositiveLimitingRoot (s k : Nat)
    (j : Fin (s + k + 1)) : Real :=
  sixVertexFixedChargeLimitingRoot (2 * s) k
    (sixVertexFixedEvenPositiveBetheIndex s k j)

end
end StatMech.FrontierD
