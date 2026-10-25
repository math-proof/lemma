/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part5


namespace StatMech.FrontierD

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem mem_finiteFirstReturnSegments_iff
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (d : A) :
    d ∈ finiteFirstReturnSegments sigma selected states ↔
      ∃ x ∈ states, ∃ k : Nat,
        k < finiteFirstReturnTime sigma selected x ∧
          (sigma ^ k) x.1 = d := by
  simp only [finiteFirstReturnSegments, List.mem_flatMap,
    finiteFirstReturnSegment, List.mem_ofFn]
  constructor
  · rintro ⟨x, hx, k, hk⟩
    exact ⟨x, hx, k.val, k.isLt, hk⟩
  · rintro ⟨x, hx, k, hk, hd⟩
    exact ⟨x, hx, ⟨⟨k, hk⟩, hd⟩⟩


theorem mem_finiteFirstReturnSegments_step_iff_of_not_selected
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (d : A) (hnext : Not (selected (sigma d))) :
    sigma d ∈ finiteFirstReturnSegments sigma selected states ↔
      d ∈ finiteFirstReturnSegments sigma selected states := by
  rw [mem_finiteFirstReturnSegments_iff,
    mem_finiteFirstReturnSegments_iff]
  constructor
  · rintro ⟨x, hx, k, hk, hpow⟩
    have hkpos : 0 < k := by
      by_contra hnot
      have hkzero : k = 0 := by omega
      subst k
      apply hnext
      rw [← hpow]
      exact x.2
    refine ⟨x, hx, k - 1, by omega, ?_⟩
    apply sigma.injective
    calc
      sigma ((sigma ^ (k - 1)) x.1) =
          (sigma ^ k) x.1 := by
        rw [show k = (k - 1) + 1 by omega, pow_succ']
        rfl
      _ = sigma d := hpow
  · rintro ⟨x, hx, k, hk, hpow⟩
    have hsucc : k + 1 < finiteFirstReturnTime sigma selected x := by
      by_contra hnot
      have heq : k + 1 = finiteFirstReturnTime sigma selected x := by omega
      apply hnext
      rw [← hpow]
      rw [show sigma ((sigma ^ k) x.1) =
          (sigma ^ (k + 1)) x.1 by rw [pow_succ']; rfl, heq]
      exact finiteFirstReturnTime_selected sigma selected x
    refine ⟨x, hx, k + 1, hsucc, ?_⟩
    rw [← hpow, pow_succ']
    rfl


theorem mem_finiteFirstReturnSegments_predecessor_iff
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (d : A) (y : {a : A // selected a}) (hstep : sigma d = y.1) :
    d ∈ finiteFirstReturnSegments sigma selected states ↔
      (finiteFirstReturnPerm sigma selected).symm y ∈ states := by
  rw [mem_finiteFirstReturnSegments_iff]
  constructor
  · rintro ⟨x, hx, k, hk, hpow⟩
    have hpowsucc : (sigma ^ (k + 1)) x.1 = y.1 := by
      rw [pow_succ']
      exact congrArg sigma hpow |>.trans hstep
    have hlast : k + 1 = finiteFirstReturnTime sigma selected x := by
      by_contra hne
      have hlt : k + 1 < finiteFirstReturnTime sigma selected x := by omega
      exact (finiteFirstReturnTime_minimal sigma selected x (k + 1) hlt)
        ⟨by omega, hpowsucc ▸ y.2⟩
    have hreturn : finiteFirstReturnPerm sigma selected x = y := by
      apply Subtype.ext
      change (sigma ^ finiteFirstReturnTime sigma selected x) x.1 = y.1
      rw [← hlast]
      exact hpowsucc
    have hxprev : x = (finiteFirstReturnPerm sigma selected).symm y := by
      apply (finiteFirstReturnPerm sigma selected).injective
      rw [hreturn, (finiteFirstReturnPerm sigma selected).apply_symm_apply]
    rwa [← hxprev]
  · intro hprev
    let x := (finiteFirstReturnPerm sigma selected).symm y
    let time := finiteFirstReturnTime sigma selected x
    have htime : 0 < time := finiteFirstReturnTime_pos sigma selected x
    have hreturn : finiteFirstReturnPerm sigma selected x = y := by
      simp [x]
    have hlast : (sigma ^ (time - 1)) x.1 = d := by
      apply sigma.injective
      calc
        sigma ((sigma ^ (time - 1)) x.1) =
            (sigma ^ time) x.1 := by
          rw [show time = (time - 1) + 1 by omega, pow_succ']
          rfl
        _ = y.1 := congrArg Subtype.val hreturn
        _ = sigma d := hstep.symm
    exact ⟨x, hprev, time - 1, by omega, hlast⟩

theorem finiteFirstReturnSegments_nodup
    (sigma : Equiv.Perm A) (selected : A -> Prop)
    [DecidablePred selected] (states : List {a : A // selected a})
    (hstates : states.Nodup) :
    (finiteFirstReturnSegments sigma selected states).Nodup := by
  rw [finiteFirstReturnSegments, List.nodup_flatMap]
  constructor
  · intro x hx
    exact finiteFirstReturnSegment_nodup sigma selected x
  · exact (List.nodup_iff_pairwise_ne.mp hstates).imp (fun hxy =>
      finiteFirstReturnSegment_disjoint sigma selected _ _ hxy)

end
end StatMech.FrontierD
