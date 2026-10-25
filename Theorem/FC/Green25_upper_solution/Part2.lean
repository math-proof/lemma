/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.Green25_upper_solution.Part2
open Asymptotics Filter Finset


namespace Green25

lemma complementKey_eq_iff (Q a b : ℕ) (ha : a < Q) (hb : b < Q)
    (heven : 2 ∣ Q) :
    complementKey Q a = complementKey Q b ↔ b = a ∨ b = Q - 1 - a := by
  obtain ⟨k, rfl⟩ := heven
  simp only [complementKey, min_def]
  split_ifs <;> omega

lemma ne_complement (Q a : ℕ) (ha : a < Q) (heven : 2 ∣ Q) :
    a ≠ Q - 1 - a := by
  obtain ⟨k, rfl⟩ := heven
  omega

end Green25
