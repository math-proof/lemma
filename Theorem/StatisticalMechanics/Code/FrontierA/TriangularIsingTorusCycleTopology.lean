/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusCycleTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part5
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleTopology
open scoped BigOperators


namespace StatMech.FrontierA

theorem angle_sub_toReal_of_eq_mod
    (x y r : Real)
    (hmod : exists k : Int, x - y - r = 2 * Real.pi * k)
    (hrange : -Real.pi < r /\ r <= Real.pi) :
    ((x : Real.Angle) - (y : Real.Angle)).toReal = r := by
  rw [<- Real.Angle.coe_sub]
  have hangle : ((x - y : Real) : Real.Angle) = (r : Real.Angle) :=
    Real.Angle.angle_eq_iff_two_pi_dvd_sub.mpr hmod
  rw [hangle]
  exact Real.Angle.toReal_coe_eq_self_iff.mpr hrange

theorem triangularTorusDirectionAngle_turn
    (a b : Fin 6) (hne : b ≠ triangularTorusDirectionReverse a) :
    (triangularTorusDirectionAngle b -
        triangularTorusDirectionAngle a).toReal =
      (triangularTorusTurnExponent a b : Real) * (Real.pi / 4) := by
  apply angle_sub_toReal_of_eq_mod
  · fin_cases a <;> fin_cases b <;>
      simp [triangularTorusDirectionAngleReal,
        triangularTorusDirectionReverse,
        triangularTorusTurnExponent] at hne ⊢
    all_goals
      solve
      | (refine ⟨(-1 : Int), ?_⟩; push_cast; ring)
      | (refine ⟨0, ?_⟩; push_cast; ring)
      | (refine ⟨1, ?_⟩; push_cast; ring)
  · fin_cases a <;> fin_cases b <;>
      simp [triangularTorusDirectionReverse,
        triangularTorusTurnExponent] at hne ⊢ <;>
      constructor <;> nlinarith [Real.pi_pos]

theorem complex_arg_one_add_I_angle :
    (Complex.arg (1 + Complex.I) : Real.Angle) =
      ((Real.pi / 4 : Real) : Real.Angle) := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [show (1 : Complex) + Complex.I =
      (Real.sqrt 2 : Complex) *
        (Real.cos (Real.pi / 4) +
          Real.sin (Real.pi / 4) * Complex.I) by
    apply Complex.ext <;>
      simp [Real.cos_pi_div_four, Real.sin_pi_div_four] <;>
      nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) <= 2)]]
  exact Complex.arg_mul_cos_add_sin_mul_I_coe_angle hsqrt
    ((Real.pi / 4 : Real) : Real.Angle)

end StatMech.FrontierA
