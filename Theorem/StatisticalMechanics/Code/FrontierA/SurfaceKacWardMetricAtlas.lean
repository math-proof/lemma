/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardMetricAtlas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardAtlas.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

universe u v


theorem kwAngleTurnPhase_sq_eq_toCircle_div (a b : Real.Angle) :
    kwAngleTurnPhase a b ^ 2 =
      (b.toCircle : Complex) / (a.toCircle : Complex) := by
  unfold kwAngleTurnPhase
  rw [pow_two, <- Complex.exp_add]
  have hexponent :
      ((((b - a).toReal : Complex) * Complex.I) / 2) +
          (((b - a).toReal : Complex) * Complex.I) / 2 =
        ((b - a).toReal : Complex) * Complex.I := by ring
  rw [hexponent]
  have hcircle :
      Complex.exp (((b - a).toReal : Complex) * Complex.I) =
        ((b - a).toCircle : Complex) := by
    calc
      Complex.exp (((b - a).toReal : Complex) * Complex.I) =
          ((((b - a).toReal : Real.Angle).toCircle : Circle) : Complex) := by
        rw [Real.Angle.toCircle_coe, Circle.coe_exp]
      _ = ((b - a).toCircle : Complex) := by
        congr 2
        exact Real.Angle.coe_toReal (b - a)
  rw [hcircle]
  simp [sub_eq_add_neg, div_eq_mul_inv]


theorem kwAngleTurnPhase_reverse_add_pi
    (a b : Real.Angle) (hne : b - a ≠ Real.pi) :
    kwAngleTurnPhase (b + Real.pi) (a + Real.pi) =
      (kwAngleTurnPhase a b)⁻¹ := by
  have hsub : (a + Real.pi) - (b + Real.pi) = -(b - a) := by abel
  have hneg : (-(b - a)).toReal = -(b - a).toReal :=
    Real.Angle.toReal_neg_eq_neg_toReal_iff.mpr hne
  unfold kwAngleTurnPhase
  rw [hsub, hneg]
  rw [show ((((-(b - a).toReal : Real) : Complex) * Complex.I) / 2) =
      -(((((b - a).toReal : Real) : Complex) * Complex.I) / 2) by
    push_cast
    ring]
  exact Complex.exp_neg _


end StatMech.FrontierA
