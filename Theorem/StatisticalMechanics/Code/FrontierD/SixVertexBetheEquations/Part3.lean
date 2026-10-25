/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part12
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexTheta_self (c x : ℝ) :
    sixVertexTheta c x x = 0 := by
  simp [sixVertexTheta]

theorem sixVertexTheta_antisymm (c x y : ℝ) :
    sixVertexTheta c y x = -sixVertexTheta c x y := by
  have hden : sixVertexThetaDenominator c y x =
      sixVertexThetaDenominator c x y := by
    unfold sixVertexThetaDenominator
    ring
  unfold sixVertexTheta
  rw [hden]
  have hratio :
      (Real.sin y - Real.sin x) / sixVertexThetaDenominator c x y =
        -((Real.sin x - Real.sin y) /
          sixVertexThetaDenominator c x y) := by ring
  rw [hratio, Real.arctan_neg]
  ring_nf

theorem sixVertexTheta_neg (c x y : ℝ) :
    sixVertexTheta c (-x) (-y) = -sixVertexTheta c x y := by
  unfold sixVertexTheta sixVertexThetaDenominator
  simp only [Real.sin_neg, Real.cos_neg]
  have hratio :
      (-Real.sin x - -Real.sin y) /
          (Real.cos x + Real.cos y - 2 * sixVertexDelta c) =
        -((Real.sin x - Real.sin y) /
          (Real.cos x + Real.cos y - 2 * sixVertexDelta c)) := by ring
  rw [hratio, Real.arctan_neg]
  ring

theorem sixVertexTheta_add_two_pi_left (c x y : ℝ) :
    sixVertexTheta c (x + 2 * Real.pi) y =
      sixVertexTheta c x y - 2 * Real.pi := by
  unfold sixVertexTheta sixVertexThetaDenominator
  rw [Real.sin_add_two_pi, Real.cos_add_two_pi]
  ring

theorem sixVertexTheta_add_two_pi_right (c x y : ℝ) :
    sixVertexTheta c x (y + 2 * Real.pi) =
      sixVertexTheta c x y + 2 * Real.pi := by
  unfold sixVertexTheta sixVertexThetaDenominator
  rw [Real.sin_add_two_pi, Real.cos_add_two_pi]
  ring

theorem sixVertexTheta_pi_pair (c y : ℝ) :
    sixVertexTheta c Real.pi y + sixVertexTheta c Real.pi (-y) =
      -2 * Real.pi := by
  unfold sixVertexTheta sixVertexThetaDenominator
  simp only [Real.sin_pi, Real.cos_pi, Real.sin_neg, Real.cos_neg,
    zero_sub]
  have hratio :
      (-Real.sin y) / (-1 + Real.cos y - 2 * sixVertexDelta c) =
        -(Real.sin y / (-1 + Real.cos y - 2 * sixVertexDelta c)) := by ring
  rw [hratio, Real.arctan_neg]
  ring_nf

theorem sixVertexTheta_neg_pi_pair (c y : ℝ) :
    sixVertexTheta c (-Real.pi) y + sixVertexTheta c (-Real.pi) (-y) =
      2 * Real.pi := by
  have h1 := sixVertexTheta_neg c Real.pi (-y)
  have h2 := sixVertexTheta_neg c Real.pi y
  have hpi := sixVertexTheta_pi_pair c y
  simp only [neg_neg] at h1
  linarith

theorem continuous_sixVertexTheta {c : ℝ} (hc : 2 < c) :
    Continuous fun xy : ℝ × ℝ => sixVertexTheta c xy.1 xy.2 := by
  have hden : ∀ xy : ℝ × ℝ,
      sixVertexThetaDenominator c xy.1 xy.2 ≠ 0 :=
    fun xy => (sixVertexThetaDenominator_pos hc xy.1 xy.2).ne'
  unfold sixVertexTheta
  apply (continuous_snd.sub continuous_fst).add
  apply continuous_const.mul
  apply Real.continuous_arctan.comp
  apply Continuous.div
  · fun_prop
  · unfold sixVertexThetaDenominator
    fun_prop
  · exact hden


theorem hasDerivAt_sixVertexTheta_left {c : ℝ} (hc : 2 < c)
    (x y : ℝ) :
    HasDerivAt (fun t => sixVertexTheta c t y)
      (4 * sixVertexDelta c * (Real.cos y - sixVertexDelta c) /
        (sixVertexThetaDenominator c x y ^ 2 +
          (Real.sin x - Real.sin y) ^ 2)) x := by
  let a := sixVertexThetaDenominator c x y
  let b := Real.sin x - Real.sin y
  have ha : a ≠ 0 := (sixVertexThetaDenominator_pos hc x y).ne'
  have hnum : HasDerivAt (fun t => Real.sin t - Real.sin y)
      (Real.cos x) x := Real.hasDerivAt_sin x |>.sub_const _
  have hden : HasDerivAt
      (fun t => Real.cos t + Real.cos y - 2 * sixVertexDelta c)
      (-Real.sin x) x :=
    (Real.hasDerivAt_cos x).add_const _ |>.sub_const _
  have hratio := hnum.div hden ha
  have harctan := hratio.arctan
  have htheta := ((hasDerivAt_const x y).sub (hasDerivAt_id x)).add
    (HasDerivAt.const_mul 2 harctan)
  convert htheta using 1
  dsimp only
  change
    4 * sixVertexDelta c * (Real.cos y - sixVertexDelta c) /
        (a ^ 2 + b ^ 2) =
      (0 - 1) + 2 *
        (1 / (1 + ((Real.sin x - Real.sin y) / a) ^ 2) *
          ((Real.cos x * a -
            (Real.sin x - Real.sin y) * -Real.sin x) / a ^ 2))
  field_simp
  have hx := Real.sin_sq_add_cos_sq x
  have hy := Real.sin_sq_add_cos_sq y
  dsimp [a, b, sixVertexThetaDenominator]
  nlinarith

theorem sixVertexTheta_left_deriv_neg {c : ℝ} (hc : 2 < c)
    (x y : ℝ) :
    4 * sixVertexDelta c * (Real.cos y - sixVertexDelta c) /
        (sixVertexThetaDenominator c x y ^ 2 +
          (Real.sin x - Real.sin y) ^ 2) < 0 := by
  have hdelta := sixVertexDelta_lt_neg_one hc
  have hcos := Real.neg_one_le_cos y
  have hden := sixVertexThetaDenominator_pos hc x y
  have hcy : 0 < Real.cos y - sixVertexDelta c := by linarith
  have hfour : 4 * sixVertexDelta c < 0 := by nlinarith
  have hsq : 0 < sixVertexThetaDenominator c x y ^ 2 +
      (Real.sin x - Real.sin y) ^ 2 := by positivity
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hfour hcy) hsq

theorem strictAnti_sixVertexTheta_left {c : ℝ} (hc : 2 < c) (y : ℝ) :
    StrictAnti fun x => sixVertexTheta c x y := by
  apply strictAnti_of_deriv_neg
  intro x
  rw [(hasDerivAt_sixVertexTheta_left hc x y).deriv]
  exact sixVertexTheta_left_deriv_neg hc x y

theorem strictMono_sixVertexTheta_right {c : ℝ} (hc : 2 < c) (x : ℝ) :
    StrictMono fun y => sixVertexTheta c x y := by
  intro y z hyz
  have h := strictAnti_sixVertexTheta_left hc x hyz
  have hneg := neg_lt_neg h
  change -sixVertexTheta c y x < -sixVertexTheta c z x at hneg
  rw [← sixVertexTheta_antisymm c y x,
    ← sixVertexTheta_antisymm c z x] at hneg
  exact hneg


end
end StatMech.FrontierD
