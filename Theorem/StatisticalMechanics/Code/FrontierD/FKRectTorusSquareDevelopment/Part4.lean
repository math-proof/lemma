/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part4


namespace StatMech.FrontierD

noncomputable section

theorem fkRectSquareDeckHom_injective (R : FKRectTorus) :
    Function.Injective (fkRectSquareDeckHom R) := by
  intro u v huv
  change fkRectSquareDeckTranslation R u =
    fkRectSquareDeckTranslation R v at huv
  have hp := congrArg Prod.fst huv
  have hq := congrArg Prod.snd huv
  simp only [fkRectSquareDeckTranslation] at hp hq
  have hw : (R.width : Int) ≠ 0 := by
    exact_mod_cast (ne_of_gt R.width_pos)
  have hhalfNat : R.height / 2 ≠ 0 := by
    exact ne_of_gt (Nat.div_pos R.height_gt_two.le (by norm_num))
  have hhalf : (R.height / 2 : Nat) ≠ (0 : Int) := by
    exact_mod_cast hhalfNat
  have hx2 : (2 : Int) * R.width * (u.1 - v.1) = 0 := by
    linear_combination hp + hq
  have hx : u.1 = v.1 := by
    have hcoefficient : (2 : Int) * R.width ≠ 0 :=
      mul_ne_zero (by norm_num) hw
    have : u.1 - v.1 = 0 :=
      (mul_eq_zero.mp hx2).resolve_left hcoefficient
    omega
  have hy2 : (2 : Int) * (R.height / 2 : Nat) *
      (u.2 - v.2) = 0 := by
    linear_combination hp - hq
  have hy : u.2 = v.2 := by
    have hcoefficient : (2 : Int) * (R.height / 2 : Nat) ≠ 0 :=
      mul_ne_zero (by norm_num) hhalf
    have : u.2 - v.2 = 0 :=
      (mul_eq_zero.mp hy2).resolve_left hcoefficient
    omega
  exact Prod.ext hx hy


end
end StatMech.FrontierD
