/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonTurning.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardCycleCoefficient.Part5
import Def.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning
open scoped BigOperators


namespace StatMech.FrontierA

theorem kw_principalTurnLift_add (a b c : Real.Angle)
    (hlower : -Real.pi < (b - a).toReal + (c - b).toReal)
    (hupper : (b - a).toReal + (c - b).toReal ≤ Real.pi) :
    (c - a).toReal = (b - a).toReal + (c - b).toReal := by
  have hangle : c - a = (b - a) + (c - b) := by abel
  rw [hangle]
  have hcoe :
      (((b - a).toReal + (c - b).toReal : ℝ) : Real.Angle) =
        (b - a) + (c - b) := by
    rw [Real.Angle.coe_add, Real.Angle.coe_toReal,
      Real.Angle.coe_toReal]
  rw [← hcoe, Real.Angle.toReal_coe_eq_self_iff.mpr ⟨hlower, hupper⟩]


theorem kwAngleTurnPhase_mul (a b c : Real.Angle)
    (hlower : -Real.pi < (b - a).toReal + (c - b).toReal)
    (hupper : (b - a).toReal + (c - b).toReal ≤ Real.pi) :
    kwAngleTurnPhase a b * kwAngleTurnPhase b c =
      kwAngleTurnPhase a c := by
  unfold kwAngleTurnPhase
  rw [← Complex.exp_add]
  congr 1
  rw [kw_principalTurnLift_add a b c hlower hupper]
  push_cast
  ring


theorem kwAngleTurnPhase_ear_splice
    (previous incoming diagonal outgoing next : Real.Angle)
    (hleftLower : -Real.pi <
      (incoming - previous).toReal + (diagonal - incoming).toReal)
    (hleftUpper :
      (incoming - previous).toReal + (diagonal - incoming).toReal ≤ Real.pi)
    (hmiddleLower : -Real.pi <
      (diagonal - incoming).toReal + (outgoing - diagonal).toReal)
    (hmiddleUpper :
      (diagonal - incoming).toReal + (outgoing - diagonal).toReal ≤ Real.pi)
    (hrightLower : -Real.pi <
      (outgoing - diagonal).toReal + (next - outgoing).toReal)
    (hrightUpper :
      (outgoing - diagonal).toReal + (next - outgoing).toReal ≤ Real.pi) :
    kwAngleTurnPhase previous incoming *
          kwAngleTurnPhase incoming outgoing *
          kwAngleTurnPhase outgoing next =
      kwAngleTurnPhase previous diagonal * kwAngleTurnPhase diagonal next := by
  rw [← kwAngleTurnPhase_mul previous incoming diagonal
      hleftLower hleftUpper,
    ← kwAngleTurnPhase_mul diagonal outgoing next
      hrightLower hrightUpper,
    ← kwAngleTurnPhase_mul incoming diagonal outgoing
      hmiddleLower hmiddleUpper]
  ring


theorem kw_three_principal_turn_sum_eq_two_pi_or_neg_two_pi
    (a b c : Real.Angle)
    (hsign :
      (0 < (b - a).toReal ∧ 0 < (c - b).toReal ∧
          0 < (a - c).toReal) ∨
        ((b - a).toReal < 0 ∧ (c - b).toReal < 0 ∧
          (a - c).toReal < 0)) :
    (b - a).toReal + (c - b).toReal + (a - c).toReal =
        2 * Real.pi ∨
      (b - a).toReal + (c - b).toReal + (a - c).toReal =
        -(2 * Real.pi) := by
  let s : ℝ := (b - a).toReal + (c - b).toReal + (a - c).toReal
  have hcoe : (s : Real.Angle) = 0 := by
    simp only [s, Real.Angle.coe_add, Real.Angle.coe_toReal]
    abel
  obtain ⟨k, hk⟩ := Real.Angle.coe_eq_zero_iff.mp hcoe
  have hk' : (k : ℝ) * (2 * Real.pi) = s := by
    simpa [zsmul_eq_mul] using hk
  have hs_lower : -(3 * Real.pi) < s := by
    dsimp only [s]
    nlinarith [Real.Angle.neg_pi_lt_toReal (b - a),
      Real.Angle.neg_pi_lt_toReal (c - b),
      Real.Angle.neg_pi_lt_toReal (a - c)]
  have hs_upper : s ≤ 3 * Real.pi := by
    dsimp only [s]
    nlinarith [Real.Angle.toReal_le_pi (b - a),
      Real.Angle.toReal_le_pi (c - b),
      Real.Angle.toReal_le_pi (a - c)]
  have hk_lower : (-1 : ℤ) ≤ k := by
    by_contra h
    have hk2 : k ≤ -2 := by omega
    have hk2' : (k : ℝ) ≤ -2 := by exact_mod_cast hk2
    nlinarith [Real.pi_pos]
  have hk_upper : k ≤ (1 : ℤ) := by
    by_contra h
    have hk2 : 2 ≤ k := by omega
    have hk2' : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    nlinarith [Real.pi_pos]
  rcases hsign with hpos | hneg
  · left
    change s = 2 * Real.pi
    have hs_pos : 0 < s := by dsimp only [s]; nlinarith
    have hk_pos : 0 < k := by
      by_contra h
      have hk_nonpos : k ≤ 0 := by omega
      have hk_nonpos' : (k : ℝ) ≤ 0 := by exact_mod_cast hk_nonpos
      nlinarith [Real.pi_pos]
    have : k = 1 := by omega
    rw [← hk', this]
    norm_num
  · right
    change s = -(2 * Real.pi)
    have hs_neg : s < 0 := by dsimp only [s]; nlinarith
    have hk_neg : k < 0 := by
      by_contra h
      have hk_nonneg : 0 ≤ k := by omega
      have hk_nonneg' : (0 : ℝ) ≤ k := by exact_mod_cast hk_nonneg
      nlinarith [Real.pi_pos]
    have : k = -1 := by omega
    rw [← hk', this]
    norm_num


theorem kw_three_principal_halfAngle_product_eq_neg_one
    (a b c : Real.Angle)
    (hsign :
      (0 < (b - a).toReal ∧ 0 < (c - b).toReal ∧
          0 < (a - c).toReal) ∨
        ((b - a).toReal < 0 ∧ (c - b).toReal < 0 ∧
          (a - c).toReal < 0)) :
    Complex.exp ((((b - a).toReal : ℂ) * Complex.I) / 2) *
        Complex.exp ((((c - b).toReal : ℂ) * Complex.I) / 2) *
        Complex.exp ((((a - c).toReal : ℂ) * Complex.I) / 2) = -1 := by
  rcases kw_three_principal_turn_sum_eq_two_pi_or_neg_two_pi
      a b c hsign with hsum | hsum
  · rw [← Complex.exp_add, ← Complex.exp_add]
    have hsum' := congrArg
      (fun r : ℝ ↦ ((r : ℂ) * Complex.I) / 2) hsum
    rw [show ((((b - a).toReal : ℂ) * Complex.I) / 2 +
          (((c - b).toReal : ℂ) * Complex.I) / 2) +
          (((a - c).toReal : ℂ) * Complex.I) / 2 =
        (Real.pi : ℂ) * Complex.I by
      convert hsum' using 1 <;> push_cast <;> ring]
    rw [Complex.exp_pi_mul_I]
  · rw [← Complex.exp_add, ← Complex.exp_add]
    have hsum' := congrArg
      (fun r : ℝ ↦ ((r : ℂ) * Complex.I) / 2) hsum
    rw [show ((((b - a).toReal : ℂ) * Complex.I) / 2 +
          (((c - b).toReal : ℂ) * Complex.I) / 2) +
          (((a - c).toReal : ℂ) * Complex.I) / 2 =
        -(Real.pi : ℂ) * Complex.I by
      convert hsum' using 1 <;> push_cast <;> ring]
    rw [show -(Real.pi : ℂ) * Complex.I =
      -((Real.pi : ℂ) * Complex.I) by ring,
      Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num


end StatMech.FrontierA
