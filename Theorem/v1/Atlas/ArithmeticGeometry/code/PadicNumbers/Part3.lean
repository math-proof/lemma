/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Order.DirectedInverseSystem
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib
import Def.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part7


namespace PadicInt

open Finset PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

/-- Each $p$-adic digit lies in $\{0, 1, \ldots, p-1\}$. -/
theorem padicDigit_lt (a : ℤ_[p]) (n : ℕ) : padicDigit a n < p := by
  unfold padicDigit
  obtain ⟨k, hk⟩ := dvd_appr_sub_appr a n (n + 1) (Nat.le_succ n)
  rw [hk, Nat.mul_div_cancel_left _ (pos_of_ne_zero (pow_ne_zero n (Nat.Prime.pos hp.out).ne'))]
  have h_sub_lt : a.appr (n + 1) - a.appr n < p ^ (n + 1) :=
    lt_of_le_of_lt (Nat.sub_le _ _) (appr_lt a (n + 1))
  rw [hk, pow_succ] at h_sub_lt
  exact Nat.lt_of_mul_lt_mul_left h_sub_lt

end PadicInt
