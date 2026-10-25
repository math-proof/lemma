/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace OeisA108081

open Nat


def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (n + k - 1).choose k * fib (n - k + 1)


end OeisA108081
