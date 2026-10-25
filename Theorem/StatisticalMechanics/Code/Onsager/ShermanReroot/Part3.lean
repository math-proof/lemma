/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanReroot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma4.Part3
import Theorem.StatisticalMechanics.Code.Onsager.ShermanSplit.Part5
import Def.StatisticalMechanics.Code.Onsager.ShermanReroot.Part3


namespace StatMech.Onsager

open Matrix BigOperators Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {n : ℕ} [NeZero n]


theorem ons_visitCount_eq_card_filter (e : E) (v : Fin n → E) :
    ons_visitCount e v = (Finset.univ.filter fun k : Fin n => v k = e).card := by
  unfold ons_visitCount
  rw [← Finset.card_subtype]
  simp

theorem ons_visitCount_pos_iff (e : E) (v : Fin n → E) :
    0 < ons_visitCount e v ↔ ∃ k, v k = e := by
  rw [ons_visitCount_eq_card_filter, Finset.card_pos]
  rw [Finset.filter_nonempty_iff]
  simp


theorem ons_visitCount_rotate (e : E) (k : Fin n) (v : Fin n → E) :
    ons_visitCount e (ons_rotate k v) = ons_visitCount e v := by
  unfold ons_visitCount
  apply Fintype.card_congr
  exact
    { toFun := fun j => ⟨j.1 + k, j.2⟩
      invFun := fun j => ⟨j.1 - k, by
        simpa [ons_rotate, sub_add_cancel] using j.2⟩
      left_inv := fun j => by ext; simp
      right_inv := fun j => by ext; simp }


theorem ons_avoids_rotate (r : E) (k : Fin n) (v : Fin n → E) :
    (∀ j, ons_rotate k v j ≠ r) ↔ ∀ j, v j ≠ r := by
  constructor
  · intro h j
    have := h (j - k)
    simpa [ons_rotate, sub_add_cancel] using this
  · intro h j
    exact h (j + k)

end StatMech.Onsager
