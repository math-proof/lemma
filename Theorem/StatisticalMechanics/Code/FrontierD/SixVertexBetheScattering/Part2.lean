/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheScattering.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part7
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexScatteringDenominator_eq (c x y : ℝ) :
    sixVertexScatteringDenominator c x y =
      (sixVertexThetaDenominator c x y : ℂ) +
        (Real.sin x - Real.sin y : ℝ) * Complex.I := by
  unfold sixVertexScatteringDenominator sixVertexThetaDenominator
  rw [mul_comm Complex.I (x : ℂ), Complex.exp_ofReal_mul_I]
  rw [show -Complex.I * (y : ℂ) = ((-y : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem sixVertexScatteringDenominator_ne_zero {c : ℝ} (hc : 2 < c)
    (x y : ℝ) : sixVertexScatteringDenominator c x y ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  rw [sixVertexScatteringDenominator_eq] at hre
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
    Complex.zero_re] at hre
  exact (sixVertexThetaDenominator_pos hc x y).ne' hre


theorem sixVertexTheta_exp_identity {c : ℝ} (hc : 2 < c) (x y : ℝ) :
    Complex.exp (-Complex.I * sixVertexTheta c x y) =
      Complex.exp (Complex.I * (x - y)) *
        star (sixVertexScatteringDenominator c x y) /
          sixVertexScatteringDenominator c x y := by
  let a := sixVertexThetaDenominator c x y
  let b := Real.sin x - Real.sin y
  have ha : 0 < a := sixVertexThetaDenominator_pos hc x y
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hphase :
      Complex.exp (((-2 * Real.arctan (b / a) : ℝ) : ℂ) * Complex.I) =
        ((a : ℂ) - (b : ℂ) * Complex.I) /
          ((a : ℂ) + (b : ℂ) * Complex.I) := by
    rw [exp_neg_two_arctan_mul_I]
    push_cast
    field_simp
  have hden : sixVertexScatteringDenominator c x y =
      (a : ℂ) + (b : ℂ) * Complex.I := by
    exact sixVertexScatteringDenominator_eq c x y
  have hstar : star (sixVertexScatteringDenominator c x y) =
      (a : ℂ) - (b : ℂ) * Complex.I := by
    rw [hden]
    apply Complex.ext <;> simp
  rw [sixVertexTheta]
  change Complex.exp (-Complex.I *
      (((y - x + 2 * Real.arctan (b / a) : ℝ) : ℂ))) = _
  rw [show -Complex.I * (((y - x + 2 * Real.arctan (b / a) : ℝ) : ℂ)) =
      Complex.I * ((x - y : ℝ) : ℂ) +
        (((-2 * Real.arctan (b / a) : ℝ) : ℂ) * Complex.I) by
    push_cast
    ring]
  rw [Complex.exp_add, hphase, hstar, hden]
  push_cast
  ring


end
end StatMech.FrontierD
