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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalFamily.Part2


namespace StatMech.FrontierD

noncomputable section

theorem continuous_sixVertexMomentumRapidityFamily
    {a b : Real} (ha : 2 < a) :
    Continuous (sixVertexMomentumRapidityFamily (b := b) ha :
      Set.Icc a b × Real → Real) := by
  unfold sixVertexMomentumRapidityFamily
  exact continuous_subtype_val.comp
    ((sixVertexRapidityMomentumFamilyHomeomorph (b := b) ha).symm.continuous.comp
      (continuous_fst.prodMk (continuous_projIcc.comp continuous_snd)) |>.snd)

theorem sixVertexMomentumRapidityFamily_eq
    {a b : Real} (ha : 2 < a) (z : Set.Icc a b × Real) :
    sixVertexMomentumRapidityFamily (b := b) ha z =
      sixVertexMomentumRapidity
        (sixVertexAntiferroelectricLambda z.1.1)
        (sixVertexAntiferroelectricLambda_pos (ha.trans_le z.1.2.1)) z.2 := by
  rfl

theorem continuous_sixVertexFourierRootDensity_family
    {a b : Real} (ha : 2 < a) :
    Continuous (fun z : Set.Icc a b × Real =>
      sixVertexFourierRootDensity
        (sixVertexAntiferroelectricLambda z.1.1) z.2) := by
  apply continuous_const.add
  apply continuous_tsum
  · intro n
    unfold sixVertexFourierRootDensityTerm
    apply Continuous.div
    · fun_prop
    · exact Real.continuous_cosh.comp
        (((continuous_sixVertexAntiferroelectricLambda_Icc (b := b) ha).comp
          continuous_fst).const_mul (n + 1 : Real))
    · intro z
      exact (Real.cosh_pos _).ne'
  · exact summable_sixVertexFourierRootDensityMajorant
      (sixVertexAntiferroelectricLambda_pos ha)
  · intro n z
    calc
      ‖sixVertexFourierRootDensityTerm
          (sixVertexAntiferroelectricLambda z.1.1) n z.2‖ ≤
          sixVertexFourierRootDensityMajorant
            (sixVertexAntiferroelectricLambda z.1.1) n :=
        norm_sixVertexFourierRootDensityTerm_le
          (sixVertexAntiferroelectricLambda_pos (ha.trans_le z.1.2.1)) n z.2
      _ ≤ sixVertexFourierRootDensityMajorant
          (sixVertexAntiferroelectricLambda a) n := by
        unfold sixVertexFourierRootDensityMajorant
        have hlam := sixVertexAntiferroelectricLambda_lower_Icc ha z.1
        gcongr

theorem continuous_sixVertexRootDensityWeight_family
    {a b : Real} (ha : 2 < a) :
    Continuous (fun z : Set.Icc a b × Real =>
      sixVertexRootDensityWeight z.1.1 z.2) := by
  unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
    sixVertexRootDensityScale sixVertexAnisotropyMagnitude sixVertexDelta
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro z
    exact (sixVertexRootDensityScale_pos
      (ha.trans_le z.1.2.1)).ne'

theorem continuous_sixVertexFourierPhysicalDensityFamily_fun
    {a b : Real} (ha : 2 < a) :
    Continuous (fun z : Set.Icc a b × Real =>
      sixVertexFourierRootDensity
          (sixVertexAntiferroelectricLambda z.1.1)
          (sixVertexMomentumRapidityFamily (b := b) ha z) /
        (2 * Real.pi * sixVertexRootDensityWeight z.1.1 z.2)) := by
  have harg : Continuous (fun z : Set.Icc a b × Real =>
      (z.1, sixVertexMomentumRapidityFamily (b := b) ha z)) :=
    continuous_fst.prodMk
      (continuous_sixVertexMomentumRapidityFamily (b := b) ha)
  have hnum :=
    (continuous_sixVertexFourierRootDensity_family (b := b) ha).comp harg
  have hden : Continuous (fun z : Set.Icc a b × Real =>
      2 * Real.pi * sixVertexRootDensityWeight z.1.1 z.2) :=
    continuous_const.mul (continuous_sixVertexRootDensityWeight_family ha)
  apply hnum.div hden
  intro z
  exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    (sixVertexRootDensityWeight_pos (ha.trans_le z.1.2.1) z.2).ne'

end
end StatMech.FrontierD
