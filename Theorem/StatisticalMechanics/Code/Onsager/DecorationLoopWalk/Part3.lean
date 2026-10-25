/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part4
import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
import Def.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part2


namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_decKWChainExponent_eq_zipWith
    (L : ℕ) (start : ons_Dart L) (tail : List (ons_Dart L)) :
    ons_decKWChainExponent L start tail =
      (List.zipWith
        (fun source target ↦ ons_decTransitionExponent L target source)
        (start :: tail) tail).sum := by
  induction tail generalizing start with
  | nil => rfl
  | cons target rest ih =>
      simp [ons_decKWChainExponent, ih]

theorem ons_isChain_closed_ofFn_mk
    {alpha : Type*} {R : alpha → alpha → Prop}
    {n : ℕ} [NeZero n] (f : Fin n → alpha)
    (hstep : ∀ k : Fin n, R (f k) (f (k + 1))) :
    List.IsChain R (List.ofFn f ++ [f 0]) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  apply List.IsChain.append
  · rw [List.isChain_ofFn]
    intro i hi
    let k : Fin (m + 1) := ⟨i, by omega⟩
    have hk : k ≠ Fin.last m := by
      intro h
      have := Fin.mk.inj_iff.mp h
      omega
    have hnext : k + 1 = ⟨i + 1, by omega⟩ := by
      apply Fin.ext
      exact Fin.val_add_one_of_lt (lt_of_le_of_ne (Fin.le_last k) hk)
    simpa [k, hnext] using hstep k
  · exact .singleton _
  · intro x hx y hy
    have hxlast : x = f (Fin.last m) := by
      rw [List.getLast?_eq_getLast (by simp), List.getLast_ofFn] at hx
      simpa using hx.symm
    have hyzero : y = f 0 := by simpa using hy.symm
    subst x
    subst y
    simpa using hstep (Fin.last m)

end StatMech.Onsager
