/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.Green25_upper_solution.Part7
open Asymptotics Filter Finset


namespace Green25

def scale25 (t : ℕ) : ℕ := 2 ^ (4 * (2 ^ t) ^ 2)


def level25 (N : ℕ) : ℕ := Nat.log 4 (Nat.log 2 N) - 1

noncomputable def fallbackPartition25 (N : ℕ) : Finpartition (Icc 1 N) := by
  let s : Setoid ℕ := ⊤
  letI : DecidableRel s.r := Classical.decRel _
  exact Finpartition.ofSetSetoid s _

noncomputable def selectedPartition25 (N : ℕ) : Finpartition (Icc 1 N) :=
  if h : 5 ≤ level25 N ∧ scale25 (level25 N) ≤ N then
    Classical.choose (tiled_digit_partition (level25 N) N h.1 (by simpa [scale25] using h.2))
  else fallbackPartition25 N

end Green25
