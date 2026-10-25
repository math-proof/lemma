/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part4


namespace StatMech.FrontierD

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

@[simp] theorem length_finiteFirstReturnSegment
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) :
    (finiteFirstReturnSegment sigma selected x).length =
      finiteFirstReturnTime sigma selected x := by
  simp [finiteFirstReturnSegment]

theorem finiteFirstReturnSegment_nodup
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) :
    (finiteFirstReturnSegment sigma selected x).Nodup := by
  rw [finiteFirstReturnSegment, List.nodup_ofFn]
  intro i j hij
  apply Fin.ext
  rcases le_total i.val j.val with hle | hle
  · by_cases heq : i.val = j.val
    · exact heq
    · have hback : x.1 = (sigma ^ (j.val - i.val)) x.1 :=
        finitePerm_pow_sub_apply_eq_of_pow_apply_eq sigma
          x.1 x.1 i.val j.val hle hij
      have hpos : 0 < j.val - i.val :=
        Nat.sub_pos_of_lt (lt_of_le_of_ne hle heq)
      have hlt : j.val - i.val <
          finiteFirstReturnTime sigma selected x := by omega
      exact False.elim ((finiteFirstReturnTime_minimal sigma selected x
        (j.val - i.val) hlt) ⟨hpos, hback ▸ x.2⟩)
  · by_cases heq : j.val = i.val
    · exact heq.symm
    · have hback : x.1 = (sigma ^ (i.val - j.val)) x.1 :=
        finitePerm_pow_sub_apply_eq_of_pow_apply_eq sigma
          x.1 x.1 j.val i.val hle hij.symm
      have hpos : 0 < i.val - j.val :=
        Nat.sub_pos_of_lt (lt_of_le_of_ne hle heq)
      have hlt : i.val - j.val <
          finiteFirstReturnTime sigma selected x := by omega
      exact False.elim ((finiteFirstReturnTime_minimal sigma selected x
        (i.val - j.val) hlt) ⟨hpos, hback ▸ x.2⟩)

theorem finiteFirstReturnSegment_disjoint
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected]
    (x y : {a : A // selected a}) (hxy : x ≠ y) :
    (finiteFirstReturnSegment sigma selected x).Disjoint
      (finiteFirstReturnSegment sigma selected y) := by
  rw [List.disjoint_left]
  intro d hdx hdy
  rw [finiteFirstReturnSegment, List.mem_ofFn] at hdx hdy
  obtain ⟨i, hi⟩ := hdx
  obtain ⟨j, hj⟩ := hdy
  have hpowers : (sigma ^ i.val) x.1 = (sigma ^ j.val) y.1 :=
    hi.trans hj.symm
  rcases le_total i.val j.val with hle | hle
  · by_cases heq : i.val = j.val
    · apply hxy
      apply Subtype.ext
      apply (sigma ^ i.val).injective
      simpa [heq] using hpowers
    · have hback : x.1 = (sigma ^ (j.val - i.val)) y.1 :=
        finitePerm_pow_sub_apply_eq_of_pow_apply_eq sigma
          x.1 y.1 i.val j.val hle hpowers
      have hpos : 0 < j.val - i.val :=
        Nat.sub_pos_of_lt (lt_of_le_of_ne hle heq)
      have hlt : j.val - i.val <
          finiteFirstReturnTime sigma selected y := by omega
      exact (finiteFirstReturnTime_minimal sigma selected y
        (j.val - i.val) hlt) ⟨hpos, hback ▸ x.2⟩
  · by_cases heq : j.val = i.val
    · apply hxy
      apply Subtype.ext
      apply (sigma ^ i.val).injective
      simpa [heq] using hpowers
    · have hback : y.1 = (sigma ^ (i.val - j.val)) x.1 :=
        finitePerm_pow_sub_apply_eq_of_pow_apply_eq sigma
          y.1 x.1 j.val i.val hle hpowers.symm
      have hpos : 0 < i.val - j.val :=
        Nat.sub_pos_of_lt (lt_of_le_of_ne hle heq)
      have hlt : i.val - j.val <
          finiteFirstReturnTime sigma selected x := by omega
      exact (finiteFirstReturnTime_minimal sigma selected x
        (i.val - j.val) hlt) ⟨hpos, hback ▸ y.2⟩

end
end StatMech.FrontierD
