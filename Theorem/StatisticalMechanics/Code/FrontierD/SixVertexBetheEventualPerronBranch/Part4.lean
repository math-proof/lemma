/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEventualPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheInfiniteAnisotropyGauge
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticCandidateSheet.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch.Part3
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexCanonicalPerronPositiveHalfRoots_mem_Ioo
    {c : Real} (hc : 2 < c) (k : Nat) (j : Fin (k + 1)) :
    sixVertexCanonicalPerronPositiveHalfRoots hc k j ∈ Set.Ioo 0 Real.pi := by
  apply sixVertexEvenSymmetricLift_positive_mem_Ioo
  unfold sixVertexCanonicalPerronPositiveHalfRoots
  rw [sixVertexEvenSymmetricLift_projection (k + 1)
    (sixVertexCanonicalPerronBetheRoots_mem_open hc k).2.1]
  exact sixVertexCanonicalPerronBetheRoots_mem_open hc k


theorem eventually_sixVertexLambdaAlongFour_eq_canonicalPerronValue
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      sixVertexLambdaAlongFour c 0 k =
        sixVertexSymmetricBetheEigenvalueValue c
          (sixVertexCanonicalPerronPositiveHalfRoots hc k) := by
  filter_upwards [eventually_sixVertexCanonicalPerronBetheRoots_witness hc]
    with k hk
  have hkernel : sixVertexSymmetricBetheEigenvalueKernel c
        (sixVertexCanonicalPerronPositiveHalfRoots hc k) =
      sixVertexSymmetricBetheEigenvalueValue c
        (sixVertexCanonicalPerronPositiveHalfRoots hc k) :=
    sixVertexSymmetricBetheEigenvalueKernel_eq_value c _
      (sixVertexCanonicalPerronPositiveHalfRoots_mem_Ioo hc k)
  have hhalf : sixVertexFourWidth 0 k / 2 = (k + 1) + (k + 1) := by
    unfold sixVertexFourWidth
    omega
  unfold SixVertexHalfFilledPerronBranchWitness at hk
  unfold sixVertexLambdaAlongFour sixVertexLambda
  simpa only [Nat.sub_zero, hhalf] using hk.2.2.symm.trans hkernel


end
end StatMech.FrontierD
