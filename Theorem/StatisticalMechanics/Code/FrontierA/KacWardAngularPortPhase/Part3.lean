/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortEmbedding.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part3
import Def.StatisticalMechanics.Code.FrontierA.KacWardAngularPortPhase.Part2


namespace StatMech.FrontierA

open SimpleGraph

theorem kwRawDirectionRoot_ne_zero (a : ℝ) : kwRawDirectionRoot a ≠ 0 :=
  Complex.exp_ne_zero _

theorem kwAngleTurnPhase_coe_eq_rootRatio
    (a b : ℝ) (hlower : -Real.pi < b - a)
    (hupper : b - a ≤ Real.pi) :
    kwAngleTurnPhase (a : Real.Angle) (b : Real.Angle) =
      (kwRawDirectionRoot a)⁻¹ * kwRawDirectionRoot b := by
  unfold kwAngleTurnPhase kwRawDirectionRoot
  have hreal : (((b : ℝ) : Real.Angle) - (a : Real.Angle)).toReal = b - a := by
    rw [← Real.Angle.coe_sub]
    exact Real.Angle.toReal_coe_eq_self_iff.mpr ⟨hlower, hupper⟩
  rw [hreal, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem kwRawDirectionRoot_add_pi_inv (a : ℝ) :
    (kwRawDirectionRoot (a + Real.pi))⁻¹ =
      -Complex.I * (kwRawDirectionRoot a)⁻¹ := by
  unfold kwRawDirectionRoot
  rw [← Complex.exp_neg, ← Complex.exp_neg,
    show -((((a + Real.pi : ℝ) : ℂ) * Complex.I) / 2) =
      (-(Real.pi : ℂ) / 2 * Complex.I) +
        -(((a : ℂ) * Complex.I) / 2) by push_cast; ring,
    Complex.exp_add, Complex.exp_neg_pi_div_two_mul_I]

theorem kwRawDirectionRoot_sub_pi_inv (a : ℝ) :
    (kwRawDirectionRoot (a - Real.pi))⁻¹ =
      Complex.I * (kwRawDirectionRoot a)⁻¹ := by
  unfold kwRawDirectionRoot
  rw [← Complex.exp_neg, ← Complex.exp_neg,
    show -((((a - Real.pi : ℝ) : ℂ) * Complex.I) / 2) =
      ((Real.pi : ℂ) / 2 * Complex.I) +
        -(((a : ℂ) * Complex.I) / 2) by push_cast; ring,
    Complex.exp_add, Complex.exp_pi_div_two_mul_I]

theorem kwPortAngleRoot_eq_rawDirectionRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (p : KWDartPort G) :
    kwPortAngleRoot embedding p = kwRawDirectionRoot
      (embedding.dartAngle (kwDartOfPort G p)).toReal := by
  rfl


end StatMech.FrontierA
