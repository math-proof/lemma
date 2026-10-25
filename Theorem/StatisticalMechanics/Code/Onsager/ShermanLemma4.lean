/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop


namespace StatMech.Onsager

open Matrix BigOperators Finset

section Orbit

variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ} [NeZero n]


theorem ons_cyclicShift_iterate_apply (v : Fin n → E) (j : ℕ) :
    ons_cyclicShift^[j] v = fun k => v (k + Fin.ofNat n j) := by
  induction j with
  | zero =>
    funext k
    simp [Fin.ofNat]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold ons_cyclicShift
    funext k
    show v ((k + 1) + Fin.ofNat n j) = v (k + Fin.ofNat n (j + 1))
    congr 1
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_ofNat, Fin.val_one', Nat.mod_add_mod, Nat.add_mod_mod]
    congr 1
    omega


theorem ons_cyclicShift_iterate_self (v : Fin n → E) :
    ons_cyclicShift^[n] v = v := by
  rw [ons_cyclicShift_iterate_apply]
  funext k
  congr 1
  apply Fin.ext
  simp


theorem ons_cyclicShift_iterate_eq_id :
    ons_cyclicShift^[n] = (id : (Fin n → E) → Fin n → E) := by
  funext v
  exact ons_cyclicShift_iterate_self v


theorem ons_cyclicShift_iterate_mul_self (v : Fin n → E) (j : ℕ) :
    ons_cyclicShift^[n * j] v = v := by
  have h : ons_cyclicShift^[n * j] = (id : (Fin n → E) → Fin n → E) := by
    rw [Function.iterate_mul, ons_cyclicShift_iterate_eq_id, Function.iterate_id]
  rw [h]; rfl


theorem ons_cyclicShift_iterate_mod (v : Fin n → E) (j : ℕ) :
    ons_cyclicShift^[j % n] v = ons_cyclicShift^[j] v := by
  conv_rhs => rw [← Nat.div_add_mod j n]
  rw [Function.iterate_add_apply, ons_cyclicShift_iterate_mul_self]


end Orbit
end StatMech.Onsager
