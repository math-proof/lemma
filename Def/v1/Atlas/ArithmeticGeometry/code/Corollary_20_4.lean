/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary_20_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.IndependenceOfValuations
open Finset

variable {F : Type*} [Field F]


/-- The intersection $\bigcap_i R_{v_i}$ of the valuation subrings of finitely many discrete valuations $v_i$ on a field $F$, viewed as a subring of $F$. -/
noncomputable def DVRIntersection (n : ℕ) (v : Fin n → AddValuation F (WithTop ℤ)) :
    Subring F where
  carrier := {x : F | ∀ i, (0 : WithTop ℤ) ≤ v i x}
  mul_mem' := by
    intro a b ha hb i; rw [(v i).map_mul]; exact add_nonneg (ha i) (hb i)
  one_mem' := by intro i; simp [AddValuation.map_one]
  add_mem' := by
    intro a b ha hb i
    exact le_trans (le_min (ha i) (hb i)) ((v i).map_add a b)
  zero_mem' := by intro i; simp [AddValuation.map_zero]
  neg_mem' := by
    intro a ha i
    have hvm1 : v i (-1 : F) = 0 := by
      have h1 := (v i).map_mul (-1 : F) (-1)
      rw [show (-1 : F) * (-1) = 1 from by ring, AddValuation.map_one] at h1
      have hne : v i (-1 : F) ≠ ⊤ := by
        rw [ne_eq, AddValuation.top_iff]; exact neg_ne_zero.mpr one_ne_zero
      set c := (v i (-1 : F)).untop hne
      have hc : v i (-1 : F) = (c : WithTop ℤ) := (WithTop.coe_untop _ hne).symm
      rw [hc, ← WithTop.coe_add] at h1
      have h2 : c + c = 0 := WithTop.coe_injective h1.symm
      rw [hc, show c = 0 from by linarith]; rfl
    rw [show (-a : F) = -1 * a from by ring, (v i).map_mul, hvm1, zero_add]; exact ha i

