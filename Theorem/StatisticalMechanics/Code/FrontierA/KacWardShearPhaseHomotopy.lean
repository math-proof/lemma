/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardShearPhaseHomotopy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGenericShear.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleHomotopy.Part3


namespace StatMech.FrontierA

open scoped BigOperators

open Set

theorem fin_add_two_ne_self
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (i : Fin n) : i + 2 ≠ i := by
  intro h
  have htwo : (2 : Fin n) ≠ 0 := by
    apply Fin.ne_of_val_ne
    simp [Nat.mod_eq_of_lt (by omega : 2 < n)]
  apply htwo
  calc
    (2 : Fin n) = (i + 2) - i := by abel
    _ = i - i := by rw [h]
    _ = 0 := sub_self i


theorem KWFiniteSimplePolygon.consecutive_turn_ne_pi
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (k : Fin n) :
    (Complex.arg (polygon.edgeVector (k + 1)) : Real.Angle) -
        (Complex.arg (polygon.edgeVector k) : Real.Angle) ≠
      (Real.pi : Real.Angle) := by
  have hk1k : k + 1 ≠ k := polygon.add_one_ne_self k
  have hk2k : (k + 1) + 1 ≠ k := by
    have h := fin_add_two_ne_self polygon.three_le k
    have hkstep : k + 2 = (k + 1) + 1 := by
      apply Fin.ext
      simp [Fin.val_add]
    intro heq
    exact h (hkstep.trans heq)
  have hk2k1 : (k + 1) + 1 ≠ k + 1 :=
    polygon.add_one_ne_self (k + 1)
  have hPnot : ¬Sbtw ℝ (polygon.vertex (k + 1)) (polygon.vertex k)
      (polygon.vertex ((k + 1) + 1)) := by
    apply polygon.vertex_not_strictly_between (k + 1) k
    · exact hk1k.symm
    · exact hk2k.symm
  have hCnot : ¬Sbtw ℝ (polygon.vertex k)
      (polygon.vertex ((k + 1) + 1))
      (polygon.vertex (k + 1)) := by
    apply polygon.vertex_not_strictly_between k ((k + 1) + 1)
    · exact hk2k
    · exact hk2k1
  have h := kw_angle_diagonal_ne_pi_of_no_between
    (P := polygon.vertex k) (A := polygon.vertex (k + 1))
    (C := polygon.vertex ((k + 1) + 1))
    (polygon.vertex_injective.ne hk1k.symm)
    (polygon.vertex_injective.ne hk2k1.symm)
    (polygon.vertex_injective.ne hk2k.symm) hPnot hCnot
  simpa only [KWFiniteSimplePolygon.edgeVector] using h


end StatMech.FrontierA
