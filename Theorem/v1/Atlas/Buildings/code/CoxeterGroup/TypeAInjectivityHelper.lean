/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeAInjectivityHelper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.SetTheory.Cardinal.Finite
open Equiv Fin Function


/-- Braid relation: $(\operatorname{swap}(a,b) \cdot \operatorname{swap}(b,c))^3 = 1$ for distinct $a,b,c$. -/
theorem swap_mul_swap_cube {α : Type*} [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (swap a b * swap b c) ^ 3 = 1 := by
  have h1 := swap_mul_swap_mul_swap hab hac
  have h2 : swap a b * swap c a * swap a b = swap b c := by
    have := swap_mul_swap_mul_swap hac.symm (Ne.symm hbc)
    simp only [swap_comm] at this ⊢; exact this
  show swap a b * swap b c * (swap a b * swap b c) * (swap a b * swap b c) = 1
  calc swap a b * swap b c * (swap a b * swap b c) * (swap a b * swap b c)
      = swap a b * (swap b c * swap a b * swap b c) * (swap a b * swap b c) := by
        simp only [mul_assoc]
    _ = swap a b * swap c a * swap a b * swap b c := by rw [h1]; simp only [mul_assoc]
    _ = swap b c * swap b c := by rw [h2]
    _ = 1 := swap_mul_self b c

/-- Reversed braid relation: $(\operatorname{swap}(b,c) \cdot \operatorname{swap}(a,b))^3 = 1$. -/
theorem swap_mul_swap_cube' {α : Type*} [DecidableEq α]
    {a b c : α} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (swap b c * swap a b) ^ 3 = 1 := by
  rw [show swap b c * swap a b = (swap a b * swap b c)⁻¹ from by
    rw [mul_inv_rev, swap_inv, swap_inv]]
  rw [inv_pow, swap_mul_swap_cube hab hbc hac, inv_one]

set_option maxHeartbeats 400000 in
/-- The assignment $i \mapsto \operatorname{swap}(\operatorname{castSucc} i, \operatorname{succ} i)$
satisfies the type-$A$ Coxeter relations. -/
theorem adjTransp_isLiftable (n : ℕ) :
    (CoxeterMatrix.A n).IsLiftable (fun i : Fin n => swap (castSucc i) (succ i)) := by
  intro i j
  simp only [CoxeterMatrix.A, Matrix.of_apply]
  split_ifs with hij hadj
  ·
    subst hij; simp [swap_mul_self]
  ·
    rcases hadj with h1 | h2
    ·
      conv_lhs =>
        rw [show (castSucc i : Fin (n + 1)) = succ j from by
          ext; simp [Fin.val_succ, Fin.val_castSucc]; omega]
      apply swap_mul_swap_cube'
      · intro h; simp [Fin.ext_iff] at h
      · intro h; exact hij (Fin.ext (by simpa using congr_arg Fin.val h)).symm
      · intro h
        have := congr_arg Fin.val h; rw [Fin.val_castSucc, Fin.val_succ] at this; omega
    ·
      conv_lhs =>
        rw [show (castSucc j : Fin (n + 1)) = succ i from by
          ext; simp [Fin.val_succ, Fin.val_castSucc]; omega]
      apply swap_mul_swap_cube
      · intro h; simp [Fin.ext_iff] at h
      · intro h; exact hij (Fin.ext (by simpa using congr_arg Fin.val h))
      · intro h
        have := congr_arg Fin.val h; rw [Fin.val_castSucc, Fin.val_succ] at this; omega
  ·
    have hne : i ≠ j := hij
    push Not at hadj
    obtain ⟨hnadj1, hnadj2⟩ := hadj
    have hci_cj : (castSucc i : Fin (n + 1)) ≠ castSucc j := by
      intro h; exact hne (Fin.ext (by simpa [Fin.val_castSucc] using congr_arg Fin.val h))
    have hsi_sj : (succ i : Fin (n + 1)) ≠ succ j := by
      intro h; exact hne (Fin.ext (by simpa [Fin.val_succ] using congr_arg Fin.val h))
    have hci_sj : (castSucc i : Fin (n + 1)) ≠ succ j := by
      intro h
      have := congr_arg Fin.val h; rw [Fin.val_castSucc, Fin.val_succ] at this; omega
    have hsi_cj : (succ i : Fin (n + 1)) ≠ castSucc j := by
      intro h
      have := congr_arg Fin.val h; rw [Fin.val_succ, Fin.val_castSucc] at this; omega
    have hdisjoint : (swap (castSucc i) (succ i) : Equiv.Perm (Fin (n + 1))).Disjoint
        (swap (castSucc j) (succ j)) := by
      intro x
      by_cases hxcj : x = castSucc j
      · left; subst hxcj; exact swap_apply_of_ne_of_ne hci_cj.symm hsi_cj.symm
      · by_cases hxsj : x = succ j
        · left; subst hxsj; exact swap_apply_of_ne_of_ne hci_sj.symm hsi_sj.symm
        · right; exact swap_apply_of_ne_of_ne hxcj hxsj
    rw [Commute.mul_pow hdisjoint.commute, sq, sq, swap_mul_self, swap_mul_self, mul_one]

