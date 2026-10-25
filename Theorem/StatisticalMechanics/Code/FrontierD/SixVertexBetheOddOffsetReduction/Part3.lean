/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddOffsetReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhase.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierEvaluation.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddOffsetReduction.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourWidth_zero_add (r k : Nat) :
    sixVertexFourWidth 0 (r + k) = sixVertexFourWidth r k := by
  unfold sixVertexFourWidth
  omega

theorem sixVertexHalfFilledCandidateValue_eq_sameWidthCentralPerron
    {c : Real} (hc : 2 < c) (r k : Nat)
    (hhalf : SixVertexHasSymmetricBetheIdentification c
      (sixVertexPositiveHalfBetheRootFamily hc)) :
    sixVertexSymmetricBetheEigenvalueValue c
        (sixVertexPositiveHalfBetheRoots hc (r + k)) =
      sixVertexLambda (sixVertexFourWidth r k) 0
        (sixVertexFourWidth_even r k) (Nat.zero_le _) c := by
  have h := hhalf (r + k)
  unfold sixVertexPositiveHalfBetheRootFamily at h
  unfold sixVertexLambdaAlongFour at h
  simpa only [sixVertexFourWidth_zero_add r k, Nat.sub_zero] using h.symm


theorem sixVertexFixedChargeLogRatio_eq_oddBetheCandidate
    {c : Real} (hc : 2 < c) {r : Nat} (k : Nat)
    (hhalf : SixVertexHasSymmetricBetheIdentification c
      (sixVertexPositiveHalfBetheRootFamily hc))
    (hodd : SixVertexOddChargeBethePerronIdentification c r) :
    sixVertexFixedChargeLogRatio c r k =
      sixVertexOddChargeBetheCandidateLogRatio hc r k := by
  rw [sixVertexFixedChargeLogRatio_eq (by linarith),
    sixVertexOddChargeBetheCandidateLogRatio,
    ← hodd hc k,
    ← sixVertexHalfFilledCandidateValue_eq_sameWidthCentralPerron
      hc r k hhalf]


theorem sixVertexFixedChargeMatchesOffsetFourier_iff_oddBetheCandidate
    {c : Real} (hc : 2 < c) {r : Nat}
    (hhalf : SixVertexHasSymmetricBetheIdentification c
      (sixVertexPositiveHalfBetheRootFamily hc))
    (hodd : SixVertexOddChargeBethePerronIdentification c r) :
    SixVertexFixedChargeMatchesOffsetFourier c r ↔
      SixVertexOddChargeBetheCandidateMatchesOffsetFourier hc r := by
  apply tendsto_congr'
  filter_upwards [] with k
  rw [sixVertexFixedChargeLogRatio_eq_oddBetheCandidate hc k hhalf hodd]

end
end StatMech.FrontierD
