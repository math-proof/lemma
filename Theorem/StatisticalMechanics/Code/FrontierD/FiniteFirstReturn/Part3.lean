/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part3


namespace StatMech.FrontierD

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

@[simp] theorem finiteFirstReturnPerm_apply
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) :
    finiteFirstReturnPerm sigma selected x =
    finiteFirstReturn sigma selected x :=
  rfl


theorem finiteFirstReturnPerm_pow_eq_ambient_pow
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x : {a : A // selected a}) (n : Nat) :
    exists k : Nat,
      ((finiteFirstReturnPerm sigma selected ^ n) x).1 =
        (sigma ^ k) x.1 := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      let y := (finiteFirstReturnPerm sigma selected ^ n) x
      let t := finiteFirstReturnTime sigma selected y
      refine ⟨t + k, ?_⟩
      rw [pow_succ', Equiv.Perm.mul_apply,
        finiteFirstReturnPerm_apply]
      change (sigma ^ t) y.1 = (sigma ^ (t + k)) x.1
      rw [hk, pow_add, Equiv.Perm.mul_apply]


theorem finiteFirstReturnPerm_sameCycle_ambient
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (x y : {a : A // selected a})
    (hcycle : (finiteFirstReturnPerm sigma selected).SameCycle x y) :
    sigma.SameCycle x.1 y.1 := by
  obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
  obtain ⟨k, hk⟩ := finiteFirstReturnPerm_pow_eq_ambient_pow
    sigma selected x n
  rw [hn] at hk
  exact ⟨k, by simpa using hk.symm⟩


end
end StatMech.FrontierD
