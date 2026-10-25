/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part2


namespace StatMech.FrontierD

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem finitePerm_pow_sub_apply_eq_of_pow_apply_eq
    (sigma : Equiv.Perm A) (x y : A) (m n : Nat)
    (hmn : m <= n)
    (h : (sigma ^ m) x = (sigma ^ n) y) :
    x = (sigma ^ (n - m)) y := by
  apply (sigma ^ m).injective
  rw [h]
  have hn : n = m + (n - m) := (Nat.add_sub_of_le hmn).symm
  nth_rewrite 1 [hn]
  rw [pow_add, Equiv.Perm.mul_apply]

theorem finiteFirstReturn_injective
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] :
    Function.Injective (finiteFirstReturn sigma selected) := by
  intro x y hxy
  apply Subtype.ext
  let m := finiteFirstReturnTime sigma selected x
  let n := finiteFirstReturnTime sigma selected y
  have hpowers : (sigma ^ m) x.1 = (sigma ^ n) y.1 :=
    congrArg Subtype.val hxy
  rcases le_total m n with hmn | hnm
  · have hback := finitePerm_pow_sub_apply_eq_of_pow_apply_eq
      sigma x.1 y.1 m n hmn hpowers
    by_cases hmnEq : m = n
    · apply (sigma ^ m).injective
      simpa [hmnEq] using hpowers
    · have hpos : 0 < n - m :=
        Nat.sub_pos_of_lt (lt_of_le_of_ne hmn hmnEq)
      have hlt : n - m < n := Nat.sub_lt
        (finiteFirstReturnTime_pos sigma selected y)
        (finiteFirstReturnTime_pos sigma selected x)
      exact False.elim ((finiteFirstReturnTime_minimal sigma selected y
        (n - m) hlt) ⟨hpos, hback ▸ x.2⟩)
  · have hback := finitePerm_pow_sub_apply_eq_of_pow_apply_eq
      sigma y.1 x.1 n m hnm hpowers.symm
    by_cases hnmEq : n = m
    · apply (sigma ^ m).injective
      simpa [hnmEq] using hpowers
    · have hpos : 0 < m - n :=
        Nat.sub_pos_of_lt (lt_of_le_of_ne hnm hnmEq)
      have hlt : m - n < m := Nat.sub_lt
        (finiteFirstReturnTime_pos sigma selected x)
        (finiteFirstReturnTime_pos sigma selected y)
      exact False.elim ((finiteFirstReturnTime_minimal sigma selected x
        (m - n) hlt) ⟨hpos, hback ▸ y.2⟩)

end
end StatMech.FrontierD
