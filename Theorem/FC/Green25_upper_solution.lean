/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.Green25_upper_solution
open Asymptotics Filter Finset


namespace Green25

lemma candidate25_special (t : ℕ) (ht : 5 ≤ t) :
    candidate25 (2 ^ (4 * (2 ^ t) ^ 2)) =
      2 ^ (4 * (2 ^ t) ^ 2 - (4 + 4 * t)) := by
  rw [candidate25, Nat.log_pow (by omega)]
  have he : (4 * (2 ^ t) ^ 2) ^ 2 = 2 ^ (4 + 4 * t) := by
    ring_nf
  rw [he]
  have hpow : ∀ a : ℕ, a ≤ 2 ^ a := by
    intro a
    induction a with
    | zero => simp
    | succ a ih =>
        rw [pow_succ]
        have hp : 1 ≤ 2 ^ a := one_le_pow₀ (by omega)
        omega
  have hle : 4 + 4 * t ≤ 4 * (2 ^ t) ^ 2 := by
    have hp : 1 ≤ 2 ^ t := one_le_pow₀ (by omega)
    have := hpow t
    nlinarith
  rw [Nat.pow_div hle (by omega)]
  exact max_eq_right (one_le_pow₀ (by omega))


end Green25
