/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma4


namespace StatMech.Onsager

open Matrix BigOperators Finset

section Orbit

variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ} [NeZero n]


def ons_orbitSetoid (E : Type*) [Fintype E] [DecidableEq E] (n : ℕ) [NeZero n] :
    Setoid (Fin n → E) where
  r v w := ∃ j : ℕ, ons_cyclicShift^[j] v = w
  iseqv :=
    { refl := fun _ => ⟨0, rfl⟩
      symm := by
        constructor
        rintro v w ⟨j, rfl⟩
        refine ⟨(n - 1) * j, ?_⟩
        have hmul : (n - 1) * j + j = n * j := by
          have h1 : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos (Nat.pos_of_neZero n)
          calc (n - 1) * j + j = (n - 1) * j + 1 * j := by rw [one_mul]
            _ = (n - 1 + 1) * j := by rw [add_mul]
            _ = n * j := by rw [h1]
        rw [← Function.iterate_add_apply, hmul, ons_cyclicShift_iterate_mul_self]
      trans := by
        rintro u v w ⟨i, rfl⟩ ⟨j, rfl⟩
        exact ⟨j + i, by rw [Function.iterate_add_apply]⟩ }


noncomputable def ons_rep (v : Fin n → E) : Fin n → E :=
  (Quotient.mk (ons_orbitSetoid E n) v).out


end Orbit
end StatMech.Onsager
