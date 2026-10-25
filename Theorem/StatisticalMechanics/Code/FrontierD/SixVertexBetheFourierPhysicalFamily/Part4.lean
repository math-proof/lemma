/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierPhysicalFamily.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalDensity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Mathlib.Topology.Homeomorph.Lemmas
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalFamily.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexFourierPhysicalDensityFamily_apply
    {a b : Real} (ha : 2 < a) (z : Set.Icc a b × Real) :
    sixVertexFourierPhysicalDensityFamily ha z =
      sixVertexFourierPhysicalDensity z.1.1
        (ha.trans_le z.1.2.1) z.2 := by
  change sixVertexFourierRootDensity
        (sixVertexAntiferroelectricLambda z.1.1)
        (sixVertexMomentumRapidityFamily (b := b) ha z) /
      (2 * Real.pi * sixVertexRootDensityWeight z.1.1 z.2) = _
  unfold sixVertexFourierPhysicalDensity
  rw [sixVertexMomentumRapidityFamily_eq (b := b)]

theorem sixVertexFourierPhysicalDensityFamily_continuumEquation
    {a b : Real} (ha : 2 < a) (t : Set.Icc a b) :
    SixVertexSatisfiesContinuousDensityEquation t.1
      (sixVertexContinuumDensityAt
        (sixVertexFourierPhysicalDensityFamily ha) t) := by
  simpa only [sixVertexContinuumDensityAt, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, sixVertexFourierPhysicalDensityFamily_apply] using
    sixVertexFourierPhysicalDensity_continuumEquation
      (ha.trans_le t.2.1)

theorem intervalIntegral_sixVertexFourierPhysicalDensityFamily
    {a b : Real} (ha : 2 < a) (t : Set.Icc a b) :
    (∫ x in -Real.pi..Real.pi,
      sixVertexContinuumDensityAt
        (sixVertexFourierPhysicalDensityFamily ha) t x) = 1 / 2 := by
  apply (intervalIntegral.integral_congr fun x _ => ?_).trans
    (intervalIntegral_sixVertexFourierPhysicalDensity
      (ha.trans_le t.2.1))
  exact sixVertexFourierPhysicalDensityFamily_apply ha (t, x)

end
end StatMech.FrontierD
