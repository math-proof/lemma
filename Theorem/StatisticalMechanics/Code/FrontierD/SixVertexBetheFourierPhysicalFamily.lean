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


namespace StatMech.FrontierD

noncomputable section

theorem neg_pi_le_pi : -Real.pi ≤ Real.pi := by
  linarith [Real.pi_pos]

theorem continuous_sixVertexAntiferroelectricLambda_Icc
    {a b : Real} (ha : 2 < a) :
    Continuous (fun t : Set.Icc a b =>
      sixVertexAntiferroelectricLambda t.1) := by
  change Continuous (Real.arcosh ∘ fun t : Set.Icc a b =>
    (t.1 ^ 2 - 2) / 2)
  apply Real.continuousOn_arcosh.comp_continuous
  · fun_prop
  · intro t
    change 1 ≤ (t.1 ^ 2 - 2) / 2
    nlinarith [ha, t.2.1]

theorem sixVertexAntiferroelectricLambda_lower_Icc
    {a b : Real} (ha : 2 < a) (t : Set.Icc a b) :
    sixVertexAntiferroelectricLambda a ≤
      sixVertexAntiferroelectricLambda t.1 := by
  unfold sixVertexAntiferroelectricLambda
  rw [Real.arcosh_le_arcosh]
  · nlinarith [ha, t.2.1]
  · nlinarith [ha]
  · nlinarith [ha, t.2.1]

theorem continuous_sixVertexXiFourier_family
    {a b : Real} (ha : 2 < a) :
    Continuous (fun z : Set.Icc a b × Real =>
      sixVertexXiFourier
        (sixVertexAntiferroelectricLambda z.1.1) z.2) := by
  have hlam := continuous_sixVertexAntiferroelectricLambda_Icc (b := b) ha
  rw [show (fun z : Set.Icc a b × Real =>
      sixVertexXiFourier
        (sixVertexAntiferroelectricLambda z.1.1) z.2) =
      fun z => Real.sinh (sixVertexAntiferroelectricLambda z.1.1) /
        (Real.cosh (sixVertexAntiferroelectricLambda z.1.1) -
          Real.cos z.2) by
    funext z
    exact sixVertexXiFourier_eq
      (sixVertexAntiferroelectricLambda_pos (ha.trans_le z.1.2.1)) z.2]
  apply Continuous.div
  · exact Real.continuous_sinh.comp (hlam.comp continuous_fst)
  · exact (Real.continuous_cosh.comp (hlam.comp continuous_fst)).sub
      (Real.continuous_cos.comp continuous_snd)
  · intro z
    have hcosh : 1 < Real.cosh
        (sixVertexAntiferroelectricLambda z.1.1) :=
      Real.one_lt_cosh.mpr
        (sixVertexAntiferroelectricLambda_pos
          (ha.trans_le z.1.2.1)).ne'
    nlinarith [Real.cos_le_one z.2]

theorem continuous_sixVertexRapidityMomentum_family
    {a b : Real} (ha : 2 < a) :
    Continuous (fun z : Set.Icc a b × Set.Icc (-Real.pi) Real.pi =>
      sixVertexRapidityMomentum
        (sixVertexAntiferroelectricLambda z.1.1) z.2.1) := by
  let X := Set.Icc a b × Set.Icc (-Real.pi) Real.pi
  let F : X → Real → Real := fun z t =>
    Real.sinh (sixVertexAntiferroelectricLambda z.1.1) /
      (Real.cosh (sixVertexAntiferroelectricLambda z.1.1) - Real.cos t)
  have hlam := continuous_sixVertexAntiferroelectricLambda_Icc (b := b) ha
  have hF : Continuous F.uncurry := by
    apply Continuous.div
    · exact Real.continuous_sinh.comp
        (hlam.comp continuous_fst.fst)
    · exact (Real.continuous_cosh.comp
        (hlam.comp continuous_fst.fst)).sub
          (Real.continuous_cos.comp continuous_snd)
    · intro z
      have hcosh : 1 < Real.cosh
          (sixVertexAntiferroelectricLambda z.1.1.1) :=
        Real.one_lt_cosh.mpr
          (sixVertexAntiferroelectricLambda_pos
            (ha.trans_le z.1.1.2.1)).ne'
      nlinarith [Real.cos_le_one z.2]
  have hparam :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := MeasureTheory.volume) (a₀ := 0) (f := F) hF
        continuous_snd.subtype_val
  change Continuous (fun z : X =>
    ∫ t in (0 : Real)..z.2.1, sixVertexXiFourier
      (sixVertexAntiferroelectricLambda z.1.1) t)
  convert hparam using 1
  funext z
  apply intervalIntegral.integral_congr
  intro t _
  exact sixVertexXiFourier_eq
    (sixVertexAntiferroelectricLambda_pos (ha.trans_le z.1.2.1)) t

end
end StatMech.FrontierD
