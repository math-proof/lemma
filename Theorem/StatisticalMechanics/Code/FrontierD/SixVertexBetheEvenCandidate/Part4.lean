/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenCandidate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenCandidate.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexEvenChargeBetheCandidateLogRatio_eq
    {c : Real} (hc : 2 < c) (s k : Nat) :
    sixVertexEvenChargeBetheCandidateLogRatio hc s k =
      2 * ((∑ j, Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase
            (sixVertexFixedEvenPositiveBetheRoots hc s k j))‖) -
        ∑ j, Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase
            (sixVertexPositiveHalfBetheRoots hc (2 * s + k) j))‖) := by
  rw [sixVertexEvenChargeBetheCandidateLogRatio,
    sixVertexFixedEvenChargeBetheEigenvalueValue_log hc,
    sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc]
  ring

end
end StatMech.FrontierD
