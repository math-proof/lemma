/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey


namespace StatMech.FrontierD

noncomputable section

theorem finitePerm_function_invariant_of_firstReturn
    {A B : Type*} [Fintype A] [DecidableEq A]
    (sigma : Equiv.Perm A) (selected : A → Prop) [DecidablePred selected]
    (f : A → B)
    (hreturn : ∀ x : {a : A // selected a},
      f (finiteFirstReturn sigma selected x) = f x.1)
    (hinactive : ∀ x : A, ¬ selected x → f (sigma x) = f x) :
    ∀ x : A, f (sigma x) = f x := by
  intro x
  by_cases hx : selected x
  · let active : {a : A // selected a} := ⟨x, hx⟩
    let n := finiteFirstReturnTime sigma selected active
    have hnpos : 0 < n := finiteFirstReturnTime_pos sigma selected active
    have htail : ∀ k : Nat, 0 < k → k ≤ n →
        f ((sigma ^ k) x) = f (sigma x) := by
      intro k hkpos hkn
      induction k using Nat.case_strong_induction_on with
      | hz => omega
      | hi k ih =>
          by_cases hk : k = 0
          · subst k
            simp
          · have hkpos' : 0 < k := Nat.pos_of_ne_zero hk
            have hklt : k < n := by omega
            have hknot : ¬ selected ((sigma ^ k) x) := by
              intro hkselected
              exact (finiteFirstReturnTime_minimal sigma selected active k
                hklt) ⟨hkpos', hkselected⟩
            calc
              f ((sigma ^ (k + 1)) x) = f (sigma ((sigma ^ k) x)) := by
                rw [pow_succ']
                rfl
              _ = f ((sigma ^ k) x) := hinactive _ hknot
              _ = f (sigma x) := ih k (by omega) hkpos' (by omega)
    have hfirst := htail n hnpos (le_refl n)
    have hreturn' : f ((sigma ^ n) x) = f x := by
      simpa [active, n, finiteFirstReturn] using hreturn active
    exact hfirst.symm.trans hreturn'
  · exact hinactive x hx


theorem finitePerm_function_invariant_of_firstReturn_of_inactive_arrival
    {A B : Type*} [Fintype A] [DecidableEq A]
    (sigma : Equiv.Perm A) (selected : A → Prop) [DecidablePred selected]
    (f : A → B)
    (hreturn : ∀ x : {a : A // selected a},
      f (finiteFirstReturn sigma selected x) = f x.1)
    (hinactiveArrival : ∀ x : A,
      ¬ selected (sigma x) → f (sigma x) = f x) :
    ∀ x : A, f (sigma x) = f x := by
  intro x
  by_cases harrival : selected (sigma x)
  · let y : {a : A // selected a} := ⟨sigma x, harrival⟩
    let z := (finiteFirstReturnPerm sigma selected).symm y
    let n := finiteFirstReturnTime sigma selected z
    have hnpos : 0 < n := finiteFirstReturnTime_pos sigma selected z
    have hreturnPoint : finiteFirstReturn sigma selected z = y := by
      change finiteFirstReturnPerm sigma selected z = y
      simp [z]
    have hlast : (sigma ^ (n - 1)) z.1 = x := by
      apply sigma.injective
      calc
        sigma ((sigma ^ (n - 1)) z.1) = (sigma ^ n) z.1 := by
          rw [show n = (n - 1) + 1 by omega, pow_succ']
          rfl
        _ = y.1 := congrArg Subtype.val hreturnPoint
        _ = sigma x := rfl
    have hprefix : ∀ k : Nat, k < n →
        f ((sigma ^ k) z.1) = f z.1 := by
      intro k hk
      induction k using Nat.case_strong_induction_on with
      | hz => simp
      | hi k ih =>
          have hpos : 0 < k + 1 := by omega
          have hnot : ¬ selected ((sigma ^ (k + 1)) z.1) := by
            intro hselected
            exact (finiteFirstReturnTime_minimal sigma selected z (k + 1)
              hk) ⟨hpos, hselected⟩
          calc
            f ((sigma ^ (k + 1)) z.1) = f (sigma ((sigma ^ k) z.1)) := by
              rw [pow_succ']
              rfl
            _ = f ((sigma ^ k) z.1) := by
              apply hinactiveArrival
              simpa [pow_succ'] using hnot
            _ = f z.1 := ih k (by omega) (by omega)
    have hxcolor : f x = f z.1 := by
      rw [← hlast]
      exact hprefix (n - 1) (by omega)
    have hycolor : f y.1 = f z.1 := by
      rw [← hreturnPoint]
      exact hreturn z
    exact hycolor.trans hxcolor.symm
  · exact hinactiveArrival x harrival


end
end StatMech.FrontierD
