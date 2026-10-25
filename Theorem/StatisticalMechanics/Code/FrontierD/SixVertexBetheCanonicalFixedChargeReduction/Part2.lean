/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedChargeReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronClosed
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualOddPerron
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenCandidate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOddPerronBranch.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedChargeReduction.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFixedChargeLogRatio_eventuallyEq_canonicalBetheCandidate
    {c : Real} (hc : 2 < c) (r : Nat)
    (hfixed : SixVertexEventuallyFixedChargeBethePerronIdentification hc r) :
    sixVertexFixedChargeLogRatio c r =ᶠ[atTop]
      sixVertexCanonicalFixedChargeBetheCandidateLogRatio hc r := by
  have hcentralShift := (tendsto_add_atTop_nat r).eventually
    (eventually_sixVertexLambdaAlongFour_eq_canonicalDensityPerronValue hc)
  filter_upwards [hfixed, hcentralShift] with k hkfixed hkcentral
  rw [Nat.add_comm k r] at hkcentral
  have hkcentral' :
      sixVertexSymmetricBetheEigenvalueValue c
          (sixVertexCanonicalDensityPerronPositiveHalfRoots hc (r + k)) =
        sixVertexLambda (sixVertexFourWidth r k) 0
          (sixVertexFourWidth_even r k) (Nat.zero_le _) c := by
    simpa [sixVertexLambdaAlongFour, sixVertexFourWidth, Nat.add_assoc] using
      hkcentral.symm
  rw [sixVertexFixedChargeLogRatio_eq (by linarith),
    sixVertexCanonicalFixedChargeBetheCandidateLogRatio,
    ← hkfixed, ← hkcentral']


theorem sixVertexFixedChargeMatchesOffsetFourier_iff_canonicalBetheCandidate
    {c : Real} (hc : 2 < c) (r : Nat)
    (hfixed : SixVertexEventuallyFixedChargeBethePerronIdentification hc r) :
    SixVertexFixedChargeMatchesOffsetFourier c r ↔
      SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc r := by
  apply tendsto_congr'
  filter_upwards
    [sixVertexFixedChargeLogRatio_eventuallyEq_canonicalBetheCandidate
      hc r hfixed] with k hk
  rw [hk]


theorem sixVertexAntiferroelectricTransferConclusion_of_canonicalFixedCharge
    {c : Real} (hc : 2 < c)
    (hbranch : ∀ r : Nat, 1 ≤ r →
      SixVertexEventuallyFixedChargeBethePerronIdentification hc r)
    (hoffset : ∀ r : Nat, 1 ≤ r →
      SixVertexCanonicalFixedChargeBetheCandidateMatchesOffsetFourier hc r) :
    SixVertexAntiferroelectricTransferConclusion c
      (sixVertexAntiferroelectricLambda c) := by
  refine ⟨sixVertexBalanced_iteratedLimit_of_canonicalPerron hc, ?_⟩
  intro r hr
  apply (sixVertexFixedChargeRatio_tendsto_iff_matchesOffsetFourier hc r).2
  exact (sixVertexFixedChargeMatchesOffsetFourier_iff_canonicalBetheCandidate
    hc r (hbranch r hr)).2 (hoffset r hr)

end
end StatMech.FrontierD
