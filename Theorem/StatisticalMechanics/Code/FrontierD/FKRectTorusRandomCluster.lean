/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster
open scoped BigOperators


namespace StatMech.FrontierD

noncomputable section

theorem fkRectCriticalP_pos {q : Real} (hq : 0 < q) :
    0 < fkRectCriticalP q := by
  unfold fkRectCriticalP
  exact div_pos (Real.sqrt_pos.2 hq) (by positivity)

theorem fkRectCriticalP_lt_one {q : Real} (hq : 0 < q) :
    fkRectCriticalP q < 1 := by
  unfold fkRectCriticalP
  rw [div_lt_one (by positivity : 0 < 1 + Real.sqrt q)]
  linarith

theorem one_sub_fkRectCriticalP {q : Real} (hq : 0 < q) :
    1 - fkRectCriticalP q = 1 / (1 + Real.sqrt q) := by
  unfold fkRectCriticalP
  field_simp [ne_of_gt (by positivity : 0 < 1 + Real.sqrt q)]
  ring

theorem fkRectCriticalP_eq_sqrt_mul_one_sub {q : Real} (hq : 0 < q) :
    fkRectCriticalP q = Real.sqrt q * (1 - fkRectCriticalP q) := by
  rw [one_sub_fkRectCriticalP hq]
  unfold fkRectCriticalP
  ring

theorem card_fkRectEdgeIndex (R : FKRectTorus) :
    Fintype.card R.EdgeIndex = 2 * R.width * R.height := by
  simp [FKRectTorus.EdgeIndex, FKRectTorus.Vertex, mul_assoc]


theorem fkRectEdgeProduct_critical_eq (R : FKRectTorus)
    {q : Real} (hq : 0 < q) (omega : R.Configuration) :
    fkRectEdgeProduct R (fkRectCriticalP q) omega =
      (1 / (1 + Real.sqrt q)) ^ (2 * R.width * R.height) *
        Real.sqrt q ^ fkRectOpenEdgeCount R omega := by
  classical
  let d : Real := 1 / (1 + Real.sqrt q)
  have hpOpen : fkRectCriticalP q = d * Real.sqrt q := by
    dsimp [d]
    unfold fkRectCriticalP
    ring
  have hpClosed : 1 - fkRectCriticalP q = d := by
    exact one_sub_fkRectCriticalP hq
  unfold fkRectEdgeProduct fkRectOpenEdgeCount
  rw [show (∏ a : R.EdgeIndex,
      if omega a then fkRectCriticalP q else 1 - fkRectCriticalP q) =
      ∏ a : R.EdgeIndex, d * (if omega a then Real.sqrt q else 1) by
    apply Finset.prod_congr rfl
    intro a ha
    cases hopen : omega a
    · simpa only [Bool.false_eq_true, ↓reduceIte, mul_one] using hpClosed
    · simp only [↓reduceIte]
      exact hpOpen]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, card_fkRectEdgeIndex]
  congr 1
  rw [Finset.prod_ite]
  simp


end
end StatMech.FrontierD
