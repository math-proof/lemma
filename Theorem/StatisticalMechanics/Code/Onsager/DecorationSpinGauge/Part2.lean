/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationInternalMiddle.Part3
import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopHomology.Part2
import Def.StatisticalMechanics.Code.Onsager.DecorationSpinGauge


namespace StatMech.Onsager

open BigOperators

theorem ons_spinVertexGauge_ne_zero
    (L : ℕ) (a b : Fin 2) (site : ZMod L × ZMod L) :
    ons_spinVertexGauge L a b site ≠ 0 := by
  unfold ons_spinVertexGauge
  exact mul_ne_zero
    (zpow_ne_zero _ (ons_spinPhase_ne_zero L a))
    (zpow_ne_zero _ (ons_spinPhase_ne_zero L b))

theorem ons_spinPhase_zpow_x_gauge
    (L : ℕ) [Fact (2 < L)] (a : Fin 2) (d : ons_Dart L) :
    ons_spinPhase L a ^ ons_dirExponentX d.2 *
        ons_spinPhase L a ^ (d.1.1.val : ℤ) =
      (-1 : ℂ) ^ ((a.val : ℤ) * ons_xWrapSign d) *
        ons_spinPhase L a ^
          ((ons_dirStep L d.2 d.1).1.val : ℤ) := by
  let u := ons_spinPhase L a
  have hu : u ≠ 0 := ons_spinPhase_ne_zero L a
  have hpow : u ^ (L : ℤ) = (-1 : ℂ) ^ (a.val : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact ons_spinPhase_pow_side L a
  have hexp := ons_dirExponentX_eq_val_diff_add_wrap d
  have hadd : ons_dirExponentX d.2 + (d.1.1.val : ℤ) =
      ((ons_dirStep L d.2 d.1).1.val : ℤ) +
        (L : ℤ) * ons_xWrapSign d := by
    omega
  calc
    u ^ ons_dirExponentX d.2 * u ^ (d.1.1.val : ℤ) =
        u ^ (ons_dirExponentX d.2 + (d.1.1.val : ℤ)) :=
      (zpow_add₀ hu _ _).symm
    _ = u ^ (((ons_dirStep L d.2 d.1).1.val : ℤ) +
        (L : ℤ) * ons_xWrapSign d) := by rw [hadd]
    _ = u ^ ((ons_dirStep L d.2 d.1).1.val : ℤ) *
        u ^ ((L : ℤ) * ons_xWrapSign d) :=
      zpow_add₀ hu _ _
    _ = u ^ ((ons_dirStep L d.2 d.1).1.val : ℤ) *
        (u ^ (L : ℤ)) ^ ons_xWrapSign d := by
      rw [_root_.zpow_mul]
    _ = u ^ ((ons_dirStep L d.2 d.1).1.val : ℤ) *
        ((-1 : ℂ) ^ (a.val : ℤ)) ^ ons_xWrapSign d := by
      rw [hpow]
    _ = (-1 : ℂ) ^ ((a.val : ℤ) * ons_xWrapSign d) *
        u ^ ((ons_dirStep L d.2 d.1).1.val : ℤ) := by
      rw [← _root_.zpow_mul]
      ring

theorem ons_spinPhase_zpow_y_gauge
    (L : ℕ) [Fact (2 < L)] (b : Fin 2) (d : ons_Dart L) :
    ons_spinPhase L b ^ ons_dirExponentY d.2 *
        ons_spinPhase L b ^ (d.1.2.val : ℤ) =
      (-1 : ℂ) ^ ((b.val : ℤ) * ons_yWrapSign d) *
        ons_spinPhase L b ^
          ((ons_dirStep L d.2 d.1).2.val : ℤ) := by
  let v := ons_spinPhase L b
  have hv : v ≠ 0 := ons_spinPhase_ne_zero L b
  have hpow : v ^ (L : ℤ) = (-1 : ℂ) ^ (b.val : ℤ) := by
    rw [zpow_natCast, zpow_natCast]
    exact ons_spinPhase_pow_side L b
  have hexp := ons_dirExponentY_eq_val_diff_add_wrap d
  have hadd : ons_dirExponentY d.2 + (d.1.2.val : ℤ) =
      ((ons_dirStep L d.2 d.1).2.val : ℤ) +
        (L : ℤ) * ons_yWrapSign d := by
    omega
  calc
    v ^ ons_dirExponentY d.2 * v ^ (d.1.2.val : ℤ) =
        v ^ (ons_dirExponentY d.2 + (d.1.2.val : ℤ)) :=
      (zpow_add₀ hv _ _).symm
    _ = v ^ (((ons_dirStep L d.2 d.1).2.val : ℤ) +
        (L : ℤ) * ons_yWrapSign d) := by rw [hadd]
    _ = v ^ ((ons_dirStep L d.2 d.1).2.val : ℤ) *
        v ^ ((L : ℤ) * ons_yWrapSign d) :=
      zpow_add₀ hv _ _
    _ = v ^ ((ons_dirStep L d.2 d.1).2.val : ℤ) *
        (v ^ (L : ℤ)) ^ ons_yWrapSign d := by
      rw [_root_.zpow_mul]
    _ = v ^ ((ons_dirStep L d.2 d.1).2.val : ℤ) *
        ((-1 : ℂ) ^ (b.val : ℤ)) ^ ons_yWrapSign d := by
      rw [hpow]
    _ = (-1 : ℂ) ^ ((b.val : ℤ) * ons_yWrapSign d) *
        v ^ ((ons_dirStep L d.2 d.1).2.val : ℤ) := by
      rw [← _root_.zpow_mul]
      ring


theorem ons_dirPhase_spin_mul_vertexGauge
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) d.2 *
        ons_spinVertexGauge L a b d.1 =
      ons_spinDartSeamSign a b d *
        ons_spinVertexGauge L a b (ons_dirStep L d.2 d.1) := by
  rw [ons_dirPhase_eq_zpow]
  unfold ons_spinVertexGauge ons_spinDartSeamSign
  have hx := ons_spinPhase_zpow_x_gauge L a d
  have hy := ons_spinPhase_zpow_y_gauge L b d
  rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  calc
    ons_spinPhase L a ^ ons_dirExponentX d.2 *
          ons_spinPhase L b ^ ons_dirExponentY d.2 *
        (ons_spinPhase L a ^ (d.1.1.val : ℤ) *
          ons_spinPhase L b ^ (d.1.2.val : ℤ)) =
        (ons_spinPhase L a ^ ons_dirExponentX d.2 *
          ons_spinPhase L a ^ (d.1.1.val : ℤ)) *
        (ons_spinPhase L b ^ ons_dirExponentY d.2 *
          ons_spinPhase L b ^ (d.1.2.val : ℤ)) := by ring
    _ = ((-1 : ℂ) ^ ((a.val : ℤ) * ons_xWrapSign d) *
          ons_spinPhase L a ^
            ((ons_dirStep L d.2 d.1).1.val : ℤ)) *
        ((-1 : ℂ) ^ ((b.val : ℤ) * ons_yWrapSign d) *
          ons_spinPhase L b ^
            ((ons_dirStep L d.2 d.1).2.val : ℤ)) := by
      rw [hx, hy]
    _ = _ := by ring

theorem ons_neg_one_zpow_sq (m : ℤ) :
    ((-1 : ℂ) ^ m) ^ 2 = 1 := by
  rw [pow_two, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
    show m + m = 2 * m by ring, _root_.zpow_mul]
  norm_num


theorem ons_spinDartSeamSign_rev
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L) :
    ons_spinDartSeamSign a b (ons_dartRev L d) =
      ons_spinDartSeamSign a b d := by
  let p := ons_spinVertexGauge L a b d.1
  let q := ons_spinVertexGauge L a b (ons_dirStep L d.2 d.1)
  let phase := ons_dirPhase
    (ons_spinPhase L a) (ons_spinPhase L b) d.2
  let sd := ons_spinDartSeamSign a b d
  let sr := ons_spinDartSeamSign a b (ons_dartRev L d)
  have hp : p ≠ 0 := ons_spinVertexGauge_ne_zero L a b d.1
  have hq : q ≠ 0 :=
    ons_spinVertexGauge_ne_zero L a b (ons_dirStep L d.2 d.1)
  have hphase : phase ≠ 0 := by
    rcases d with ⟨site, mu⟩
    fin_cases mu <;>
      simp [phase, ons_dirPhase, ons_spinPhase_ne_zero]
  have hforward : phase * p = sd * q := by
    simpa only [phase, p, q, sd] using
      ons_dirPhase_spin_mul_vertexGauge L a b d
  have hreverse : phase⁻¹ * q = sr * p := by
    have h := ons_dirPhase_spin_mul_vertexGauge
      L a b (ons_dartRev L d)
    simpa only [phase, p, q, sr, ons_dartRev,
      ons_dirPhase_spin_opposite, ons_dirStep_opposite] using h
  have hprod : sd * sr = 1 := by
    apply mul_right_cancel₀ (mul_ne_zero hp hq)
    calc
      sd * sr * (p * q) = (sd * q) * (sr * p) := by ring
      _ = (phase * p) * (phase⁻¹ * q) := by
        rw [hforward, hreverse]
      _ = (phase * phase⁻¹) * (p * q) := by ring
      _ = p * q := by rw [mul_inv_cancel₀ hphase, one_mul]
      _ = 1 * (p * q) := by ring
  have hsq : sd ^ 2 = 1 := by
    exact ons_neg_one_zpow_sq _
  calc
    sr = 1 * sr := by ring
    _ = (sd * sd) * sr := by rw [← pow_two, hsq]
    _ = sd * (sd * sr) := by ring
    _ = sd := by rw [hprod]; ring


end StatMech.Onsager
