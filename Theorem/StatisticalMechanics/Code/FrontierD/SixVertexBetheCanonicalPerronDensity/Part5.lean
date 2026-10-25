/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEventualPerronBranch.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part5
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem eventually_sixVertexLambdaAlongFour_eq_canonicalDensityPerronValue
    {c : Real} (hc : 2 < c) :
    ∀ᶠ k : Nat in atTop,
      sixVertexLambdaAlongFour c 0 k =
        sixVertexSymmetricBetheEigenvalueValue c
          (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k) := by
  filter_upwards
    [eventually_sixVertexCanonicalDensityPerronBetheRoots_gaugeWitness hc]
      with k hk
  have hopen := hk.1.1
  have hpositive : ∀ j,
      sixVertexCanonicalDensityPerronPositiveHalfRoots hc k j ∈
        Set.Ioo 0 Real.pi := by
    intro j
    apply sixVertexEvenSymmetricLift_positive_mem_Ioo
    unfold sixVertexCanonicalDensityPerronPositiveHalfRoots
    rw [sixVertexEvenSymmetricLift_projection (k + 1) hopen.2.1]
    exact hopen
  have hkernel := sixVertexSymmetricBetheEigenvalueKernel_eq_value c
    (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k) hpositive
  have hhalf : sixVertexFourWidth 0 k / 2 = (k + 1) + (k + 1) := by
    unfold sixVertexFourWidth
    omega
  unfold SixVertexHalfFilledPerronGaugeWitness
    SixVertexHalfFilledPerronBranchWitness at hk
  unfold sixVertexLambdaAlongFour sixVertexLambda
  simpa only [Nat.sub_zero, hhalf] using hk.1.2.2.symm.trans hkernel


end
end StatMech.FrontierD
