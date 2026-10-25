/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectMedialBondLabel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialPrimalLabel.Part3


namespace StatMech.FrontierD

theorem double_cyclicPred (W x : Nat) (hW : 0 < W) (hx : x < W) :
    (2 * x + 2 * W - 1) % (2 * W) =
      2 * ((x + W - 1) % W) + 1 := by
  by_cases hzero : x = 0
  · subst x
    have hlt : 2 * W - 1 < 2 * W := by omega
    have hpred : (W - 1) % W = W - 1 :=
      Nat.mod_eq_of_lt (by omega)
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [hpred, Nat.mod_eq_of_lt hlt]
    omega
  · have hxpos : 0 < x := Nat.pos_of_ne_zero hzero
    have hleft : 2 * x + 2 * W - 1 = (2 * x - 1) + 2 * W := by omega
    have hright : x + W - 1 = (x - 1) + W := by omega
    rw [hleft, hright, Nat.add_mod_right, Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

theorem double_finitePeriodicSucc
    (W x : Nat) (hW : 0 < W) (hx : x < W) :
    (2 * x + 1 + 1) % (2 * W) = 2 * ((x + 1) % W) := by
  by_cases hnext : x + 1 < W
  · rw [Nat.mod_eq_of_lt hnext, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hxlast : x + 1 = W := by omega
    rw [show 2 * x + 1 + 1 = 2 * W by omega, Nat.mod_self,
      hxlast, Nat.mod_self]

theorem double_add_one_lt (W x : Nat) (hx : x < W) :
    1 + x * 2 < W * 2 := by
  omega

theorem double_mul_add_one_lt (W x : Nat) (hx : x < W) :
    2 * x + 1 < 2 * W := by
  omega

theorem double_mul_add_one_mod (W x : Nat) (hx : x < W) :
    (2 * x + 1) % (2 * W) = 1 + 2 * x := by
  rw [Nat.mod_eq_of_lt (double_mul_add_one_lt W x hx)]
  omega

theorem even_finitePeriodicSucc_iff (R : FKRectTorus)
    (y : Fin R.height) :
    Even (finitePeriodicSucc R.height_pos y).val ↔ ¬ Even y.val := by
  change Even ((y.val + 1) % R.height) ↔ ¬ Even y.val
  rw [Even.mod_even_iff R.height_even, Nat.even_add_one]

theorem even_cyclicPred_iff (R : FKRectTorus)
    (y : Fin R.height) :
    Even (SixVertexArrows.cyclicPred R.height_pos y).val ↔
      ¬ Even y.val := by
  let z := SixVertexArrows.cyclicPred R.height_pos y
  have h := even_finitePeriodicSucc_iff R z
  rw [finitePeriodicSucc_cyclicPred] at h
  tauto


theorem finitePeriodicSucc_val {N : Nat} (hN : 0 < N) (i : Fin N) :
    (finitePeriodicSucc hN i).val =
      if i.val + 1 = N then 0 else i.val + 1 := by
  unfold finitePeriodicSucc
  by_cases h : i.val + 1 = N
  · simp [h]
  · have hlt : i.val + 1 < N := by omega
    simp [h, Nat.mod_eq_of_lt hlt]


end StatMech.FrontierD
