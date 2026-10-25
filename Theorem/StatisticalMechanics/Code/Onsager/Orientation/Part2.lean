/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Orientation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WalkCellBridge
import Def.StatisticalMechanics.Code.Onsager.Orientation.Part2


namespace StatMech.Onsager.Orientation

open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing
  StatMech.Onsager.JordanParity

open Fin.NatCast

variable {n : ℕ} [NeZero n]


theorem leftParity_step (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) (k : Fin n) :
    leftParity d k = leftParity d (k + 1) := by
  rcases hreflexfree k with h0 | h1
  · exact leftCell_parity_eq_of_straight d hclosed hsimple k (by rw [sub_eq_zero] at h0; exact h0)
  · unfold leftParity; rw [leftCell_eq_of_leftTurn d hclosed k h1]


theorem leftParity_const (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hsimple : Function.Injective (pos d))
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) (k : Fin n) :
    leftParity d k = leftParity d 0 := by
  have haux : ∀ m : ℕ, leftParity d (Nat.cast m) = leftParity d 0 := by
    intro m
    induction m with
    | zero => simp
    | succ j ih =>
      have hcast : (Nat.cast (j + 1) : Fin n) = Nat.cast j + 1 := by
        apply Fin.ext
        rw [Fin.val_natCast, Fin.val_add, Fin.val_natCast, Fin.val_one',
          Nat.add_mod (j % n) (1 % n) n, Nat.mod_mod_of_dvd _ (dvd_refl n),
          Nat.mod_mod_of_dvd _ (dvd_refl n), ← Nat.add_mod]
      rw [hcast, ← leftParity_step d hclosed hsimple hreflexfree (Nat.cast j), ih]
  have := haux k.val
  rwa [Fin.cast_val_eq_self] at this

end StatMech.Onsager.Orientation
