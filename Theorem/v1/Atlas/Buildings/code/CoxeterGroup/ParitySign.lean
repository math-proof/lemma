/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ParitySign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Coxeter.Basic


namespace CoxeterSystem

open List

/-- Helper: $(-1)^a = (-1)^b$ in $\mathbb{Z}^\times$ whenever $a \equiv b \pmod 2$. -/
theorem neg_one_units_pow_eq_of_mod_two_eq {a b : ℕ} (h : a % 2 = b % 2) :
    ((-1 : ℤˣ) ^ a) = ((-1 : ℤˣ) ^ b) := by
  ext
  show ((-1 : ℤ) ^ a) = ((-1 : ℤ) ^ b)
  rcases Nat.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩ <;>
  rcases Nat.even_or_odd b with ⟨l, hl⟩ | ⟨l, hl⟩
  · simp [hk, hl]
  · exfalso; omega
  · exfalso; omega
  · simp [hk, hl, show Odd (2 * k + 1) from ⟨k, rfl⟩, show Odd (2 * l + 1) from ⟨l, rfl⟩,
          Odd.neg_one_pow]

end CoxeterSystem
