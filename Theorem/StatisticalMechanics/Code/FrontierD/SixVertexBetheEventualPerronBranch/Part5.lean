/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheInfiniteAnisotropyGauge
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticCandidateSheet.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch.Part4
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexCanonicalPerronCandidateRate_eq_rootAverage
    {c : Real} (hc : 2 < c) (k : Nat) :
    sixVertexCanonicalPerronCandidateRate hc k =
      Real.log 2 / (sixVertexFourWidth 0 k : Real) +
        sixVertexSymmetricBetheRootAverage c
          (sixVertexCanonicalPerronPositiveHalfRootFamily hc) k := by
  rw [sixVertexCanonicalPerronCandidateRate,
    sixVertexSymmetricBetheEigenvalueValue_log_of_two_lt hc]
  unfold sixVertexSymmetricBetheRootAverage
    sixVertexCanonicalPerronPositiveHalfRootFamily
  ring

theorem sixVertexCentralWidthRate_eventuallyEq_canonicalPerronCandidateRate
    {c : Real} (hc : 2 < c) :
    sixVertexCentralWidthRate c =ᶠ[atTop]
      sixVertexCanonicalPerronCandidateRate hc := by
  filter_upwards [eventually_sixVertexLambdaAlongFour_eq_canonicalPerronValue hc]
    with k hk
  unfold sixVertexCentralWidthRate sixVertexCanonicalPerronCandidateRate
  rw [hk]

theorem sixVertexCentralWidthRate_eventuallyEq_canonicalRootAverage
    {c : Real} (hc : 2 < c) :
    sixVertexCentralWidthRate c =ᶠ[atTop] fun k =>
      Real.log 2 / (sixVertexFourWidth 0 k : Real) +
        sixVertexSymmetricBetheRootAverage c
          (sixVertexCanonicalPerronPositiveHalfRootFamily hc) k := by
  filter_upwards
    [sixVertexCentralWidthRate_eventuallyEq_canonicalPerronCandidateRate hc]
      with k hk
  rw [hk, sixVertexCanonicalPerronCandidateRate_eq_rootAverage]

end
end StatMech.FrontierD
