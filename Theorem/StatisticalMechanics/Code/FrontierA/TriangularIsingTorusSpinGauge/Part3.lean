/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSpinGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusGraphTransition.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusHomology.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part5
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSpinGauge.Part3


namespace StatMech.FrontierA

open StatMech.Onsager


theorem spinPhase_neg_x_gauge
    (L : Nat) [Fact (2 < L)] (a : Fin 2) (d : ons_Dart L) :
    ons_spinPhase L a ^ (-ons_dirExponentX d.2) *
        ons_spinPhase L a ^ (-(d.1.1.val : Int)) =
      (-1 : Complex) ^ ((a.val : Int) * (-ons_xWrapSign d)) *
        ons_spinPhase L a ^
          (-((ons_dirStep L d.2 d.1).1.val : Int)) := by
  let u := ons_spinPhase L a
  have hu : u ≠ 0 := ons_spinPhase_ne_zero L a
  have hroot : u ^ (L : Int) = (-1 : Complex) ^ (a.val : Int) := by
    rw [zpow_natCast, zpow_natCast]
    exact ons_spinPhase_pow_side L a
  have hexp := ons_dirExponentX_eq_val_diff_add_wrap d
  have hadd : -ons_dirExponentX d.2 - (d.1.1.val : Int) =
      (-((ons_dirStep L d.2 d.1).1.val : Int)) +
        (L : Int) * (-ons_xWrapSign d) := by
    rw [hexp]
    ring
  change u ^ (-ons_dirExponentX d.2) *
      u ^ (-(d.1.1.val : Int)) = _
  calc
    u ^ (-ons_dirExponentX d.2) * u ^ (-(d.1.1.val : Int)) =
        u ^ (-ons_dirExponentX d.2 - (d.1.1.val : Int)) :=
      (zpow_add₀ hu _ _).symm
    _ = u ^ ((-((ons_dirStep L d.2 d.1).1.val : Int)) +
        (L : Int) * (-ons_xWrapSign d)) := by rw [hadd]
    _ = u ^ (-((ons_dirStep L d.2 d.1).1.val : Int)) *
        u ^ ((L : Int) * (-ons_xWrapSign d)) := zpow_add₀ hu _ _
    _ = u ^ (-((ons_dirStep L d.2 d.1).1.val : Int)) *
        (u ^ (L : Int)) ^ (-ons_xWrapSign d) := by
      rw [_root_.zpow_mul]
    _ = u ^ (-((ons_dirStep L d.2 d.1).1.val : Int)) *
        ((-1 : Complex) ^ (a.val : Int)) ^ (-ons_xWrapSign d) := by
      rw [hroot]
    _ = (-1 : Complex) ^ ((a.val : Int) * (-ons_xWrapSign d)) *
        u ^ (-((ons_dirStep L d.2 d.1).1.val : Int)) := by
      rw [← _root_.zpow_mul]
      ring

theorem spinPhase_neg_y_gauge
    (L : Nat) [Fact (2 < L)] (b : Fin 2) (d : ons_Dart L) :
    ons_spinPhase L b ^ (-ons_dirExponentY d.2) *
        ons_spinPhase L b ^ (-(d.1.2.val : Int)) =
      (-1 : Complex) ^ ((b.val : Int) * (-ons_yWrapSign d)) *
        ons_spinPhase L b ^
          (-((ons_dirStep L d.2 d.1).2.val : Int)) := by
  let v := ons_spinPhase L b
  have hv : v ≠ 0 := ons_spinPhase_ne_zero L b
  have hroot : v ^ (L : Int) = (-1 : Complex) ^ (b.val : Int) := by
    rw [zpow_natCast, zpow_natCast]
    exact ons_spinPhase_pow_side L b
  have hexp := ons_dirExponentY_eq_val_diff_add_wrap d
  have hadd : -ons_dirExponentY d.2 - (d.1.2.val : Int) =
      (-((ons_dirStep L d.2 d.1).2.val : Int)) +
        (L : Int) * (-ons_yWrapSign d) := by
    rw [hexp]
    ring
  change v ^ (-ons_dirExponentY d.2) *
      v ^ (-(d.1.2.val : Int)) = _
  calc
    v ^ (-ons_dirExponentY d.2) * v ^ (-(d.1.2.val : Int)) =
        v ^ (-ons_dirExponentY d.2 - (d.1.2.val : Int)) :=
      (zpow_add₀ hv _ _).symm
    _ = v ^ ((-((ons_dirStep L d.2 d.1).2.val : Int)) +
        (L : Int) * (-ons_yWrapSign d)) := by rw [hadd]
    _ = v ^ (-((ons_dirStep L d.2 d.1).2.val : Int)) *
        v ^ ((L : Int) * (-ons_yWrapSign d)) := zpow_add₀ hv _ _
    _ = v ^ (-((ons_dirStep L d.2 d.1).2.val : Int)) *
        (v ^ (L : Int)) ^ (-ons_yWrapSign d) := by
      rw [_root_.zpow_mul]
    _ = v ^ (-((ons_dirStep L d.2 d.1).2.val : Int)) *
        ((-1 : Complex) ^ (b.val : Int)) ^ (-ons_yWrapSign d) := by
      rw [hroot]
    _ = (-1 : Complex) ^ ((b.val : Int) * (-ons_yWrapSign d)) *
        v ^ (-((ons_dirStep L d.2 d.1).2.val : Int)) := by
      rw [← _root_.zpow_mul]
      ring


theorem triangularTorusDirectionPhase_mul_vertexGauge
    (L : Nat) [Fact (2 < L)] (a b : Fin 2)
    (d : triangularTorusDart L) :
    triangularTorusDirectionPhase (ons_spinPhase L a)
        (ons_spinPhase L b) d.2 *
        triangularTorusSpinVertexGauge L a b d.1 =
      triangularTorusSpinDartSeamSign L a b d *
        triangularTorusSpinVertexGauge L a b
          (d.1 - triangularTorusDirectionStep L d.2) := by
  rw [triangularTorusDirectionPhase_eq_movement_zpow]
  unfold triangularTorusSpinVertexGauge
    triangularTorusSpinDartSeamSign
  rw [show -((a.val : Int) *
      ons_xWrapSign (triangularTorusXMovementDart L d)) -
      (b.val : Int) *
        ons_yWrapSign (triangularTorusYMovementDart L d) =
      (a.val : Int) *
          (-ons_xWrapSign (triangularTorusXMovementDart L d)) +
        (b.val : Int) *
          (-ons_yWrapSign (triangularTorusYMovementDart L d)) by ring,
    zpow_add₀ (by norm_num : (-1 : Complex) ≠ 0)]
  have hx := spinPhase_neg_x_gauge L a
    (triangularTorusXMovementDart L d)
  have hy := spinPhase_neg_y_gauge L b
    (triangularTorusYMovementDart L d)
  simp only [triangularTorusXMovementDart,
    triangularTorusYMovementDart] at hx hy
  rw [triangularTorusXMovement_target] at hx
  rw [triangularTorusYMovement_target] at hy
  calc
    ons_spinPhase L a ^
          (-ons_dirExponentX (triangularTorusXMovementDirection d.2)) *
        ons_spinPhase L b ^
          (-ons_dirExponentY (triangularTorusYMovementDirection d.2)) *
        (ons_spinPhase L a ^ (-(d.1.1.val : Int)) *
          ons_spinPhase L b ^ (-(d.1.2.val : Int))) =
      (ons_spinPhase L a ^
          (-ons_dirExponentX (triangularTorusXMovementDirection d.2)) *
        ons_spinPhase L a ^ (-(d.1.1.val : Int))) *
      (ons_spinPhase L b ^
          (-ons_dirExponentY (triangularTorusYMovementDirection d.2)) *
        ons_spinPhase L b ^ (-(d.1.2.val : Int))) := by ring
    _ = _ := by
      rw [hx, hy]
      simp only [triangularTorusXMovementDart,
        triangularTorusYMovementDart]
      ring


end StatMech.FrontierA
