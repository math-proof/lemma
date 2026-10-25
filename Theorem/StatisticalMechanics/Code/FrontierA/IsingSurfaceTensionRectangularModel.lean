/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionRectangularModel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFeketeIdentification
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCriticalCoupling
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionRectangularModel


namespace StatMech.FrontierA

noncomputable section

theorem rectangularDobrushinFreeEnergy_nonneg
    {beta : Real} (hbeta : 0 < beta) (m n : Nat) :
    0 <= rectangularDobrushinFreeEnergy beta m n :=
  cubicalRectangularWilsonFreeEnergy_nonneg hbeta m n


theorem rectangularDobrushinFreeEnergy_eq_dualIsingDisorder
    {beta : Real} (hbeta : 0 < beta) {m n : Nat}
    (hm : 0 < m) (hn : 0 < n) :
    rectangularDobrushinFreeEnergy beta m n =
      cubicalRectangularDisorderFreeEnergy beta m n :=
  cubicalRectangularWilsonFreeEnergy_eq_disorderFreeEnergy hbeta hm hn


theorem rectangularDobrushinFreeEnergy_areaBound
    {beta : Real} (hbeta : 0 < beta) :
    HasRectangularAreaBound (rectangularDobrushinFreeEnergy beta) := by
  refine ⟨2 * gaugeDualCoupling beta,
    mul_nonneg (by norm_num) (gaugeDualCoupling_pos hbeta).le, ?_⟩
  intro m n
  by_cases hm : m = 0
  · subst m
    rw [rectangularDobrushinFreeEnergy,
      cubicalRectangularWilsonFreeEnergy]
    have hempty : cubicalXYLoop
        (a := 0) (b := n) (c := max 0 n)
        (0 : Fin (max 0 n + 1)) = ∅ := by
      simp [cubicalXYLoop, cubicalXYSheet, gaugeSurfaceBoundary]
    rw [hempty, gaugeWilsonExpectation_empty]
    simp
  by_cases hn : n = 0
  · subst n
    rw [rectangularDobrushinFreeEnergy,
      cubicalRectangularWilsonFreeEnergy]
    have hempty : cubicalXYLoop
        (a := m) (b := 0) (c := max m 0)
        (0 : Fin (max m 0 + 1)) = ∅ := by
      simp [cubicalXYLoop, cubicalXYSheet, gaugeSurfaceBoundary]
    rw [hempty, gaugeWilsonExpectation_empty]
    simp
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  have hc_pos : 0 < max m n := hm_pos.trans_le (Nat.le_max_left m n)
  have hbound := cubicalXYWilsonFreeEnergy_le_area_mul_dualCoupling
    hm_pos hn_pos hc_pos (0 : Fin (max m n + 1)) beta hbeta
  change rectangularDobrushinFreeEnergy beta m n <= _
  rw [rectangularDobrushinFreeEnergy,
    cubicalRectangularWilsonFreeEnergy]
  convert hbound using 1 <;> push_cast <;> ring


theorem rectangularDobrushinFreeEnergy_separatelySubadditive
    {beta : Real} (hbeta : 0 < beta) :
    SeparatelySubadditive (rectangularDobrushinFreeEnergy beta) := by
  simpa [rectangularDobrushinFreeEnergy] using
    cubicalRectangularWilsonFreeEnergy_separatelySubadditive hbeta


end
end StatMech.FrontierA
