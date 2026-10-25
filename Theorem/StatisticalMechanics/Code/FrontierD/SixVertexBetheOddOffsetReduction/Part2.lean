/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhase.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddOffsetReduction
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexOddChargeBetheCandidateLogRatio_eq
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) (k : Nat) :
    sixVertexOddChargeBetheCandidateLogRatio hc r k =
      Real.log (sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheRoots hc r k)
        (sixVertexFixedChargeBetheCentralIndex r k)) +
      ∑ j ∈ (Finset.univ.erase
          (sixVertexFixedChargeBetheCentralIndex r k)),
        Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase (sixVertexFixedChargeBetheRoots hc r k j))‖ -
      (Real.log 2 + 2 * ∑ j,
        Real.log ‖sixVertexBetheM c
          (sixVertexBethePhase
            (sixVertexPositiveHalfBetheRoots hc (r + k) j))‖) := by
  rw [sixVertexOddChargeBetheCandidateLogRatio,
    sixVertexFixedOddChargeBetheEigenvalueValue_log hc hr k,
    sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc]


end
end StatMech.FrontierD
