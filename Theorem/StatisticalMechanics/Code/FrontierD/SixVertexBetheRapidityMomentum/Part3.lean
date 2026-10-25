/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityMomentum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierKernelClosedForm
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheRapidityMomentum.Part2


namespace StatMech.FrontierD

noncomputable section

theorem hasDerivAt_sixVertexRapidityMomentum
    {lam : Real} (hlam : 0 < lam) (alpha : Real) :
    HasDerivAt (sixVertexRapidityMomentum lam)
      (sixVertexXiFourier lam alpha) alpha := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (continuous_sixVertexXiFourier hlam).intervalIntegrable _ _
  · exact (continuous_sixVertexXiFourier hlam).stronglyMeasurable.stronglyMeasurableAtFilter
  · exact (continuous_sixVertexXiFourier hlam).continuousAt

theorem strictMono_sixVertexRapidityMomentum
    {lam : Real} (hlam : 0 < lam) :
    StrictMono (sixVertexRapidityMomentum lam) :=
  strictMono_of_hasDerivAt_pos
    (hasDerivAt_sixVertexRapidityMomentum hlam)
    (sixVertexXiFourier_pos hlam)

theorem sixVertexRapidityMomentum_pi
    {lam : Real} (hlam : 0 < lam) :
    sixVertexRapidityMomentum lam Real.pi = Real.pi :=
  intervalIntegral_zero_pi_sixVertexXiFourier hlam

theorem sixVertexRapidityMomentum_neg_pi
    {lam : Real} (hlam : 0 < lam) :
    sixVertexRapidityMomentum lam (-Real.pi) = -Real.pi := by
  have hleft :
      (∫ t in -Real.pi..(0 : Real), sixVertexXiFourier lam t) = Real.pi := by
    have hnegIntegral := intervalIntegral.integral_comp_neg
      (f := sixVertexXiFourier lam) (a := 0) (b := Real.pi)
    have hnegIntegral' :
        (∫ t in (0 : Real)..Real.pi, sixVertexXiFourier lam (-t)) =
          ∫ t in -Real.pi..(0 : Real), sixVertexXiFourier lam t := by
      simpa only [neg_zero] using hnegIntegral
    rw [<- hnegIntegral']
    apply (intervalIntegral.integral_congr fun t _ => ?_).trans
      (intervalIntegral_zero_pi_sixVertexXiFourier hlam)
    exact sixVertexXiFourier_neg lam t
  rw [sixVertexRapidityMomentum, intervalIntegral.integral_symm, hleft]

theorem sixVertexRapidityMomentum_mem_Icc
    {lam : Real} (hlam : 0 < lam) {alpha : Real}
    (halpha : alpha ∈ Set.Icc (-Real.pi) Real.pi) :
    sixVertexRapidityMomentum lam alpha ∈ Set.Icc (-Real.pi) Real.pi := by
  have hmono := (strictMono_sixVertexRapidityMomentum hlam).monotone
  constructor
  · rw [<- sixVertexRapidityMomentum_neg_pi hlam]
    exact hmono halpha.1
  · rw [<- sixVertexRapidityMomentum_pi hlam]
    exact hmono halpha.2

end
end StatMech.FrontierD
