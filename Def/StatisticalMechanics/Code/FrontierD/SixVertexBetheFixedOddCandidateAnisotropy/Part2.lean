/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedOddCandidateAnisotropy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedEvenCandidateAnisotropy.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedOddCandidateAnisotropy.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedOddChargeNormalizedMProduct (s k : Nat) (c : Real) : Real :=
  ∏ j ∈ (Finset.univ.erase
      (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k)),
    ‖sixVertexBetheM c
      (sixVertexBethePhase
        (sixVertexFixedChargeBetheRootAt (2 * s + 1) k j c)) /
      (c ^ 2 - 2 : Real)‖

def sixVertexFixedOddChargeLimitingMProduct (s k : Nat) : Real :=
  ∏ j ∈ (Finset.univ.erase
      (sixVertexFixedChargeBetheCentralIndex (2 * s + 1) k)),
    ‖-1 / (1 - sixVertexFixedChargeLimitingPhase (2 * s + 1) k j)‖

end
end StatMech.FrontierD
