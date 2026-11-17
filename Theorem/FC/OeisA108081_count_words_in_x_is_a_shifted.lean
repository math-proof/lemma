/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Def.FC.OeisA108081_count_words_in_x_is_a_shifted.Part2

@[expose] public section

namespace OeisA108081

open Nat


@[simp] public theorem length_l (w : Word) : (l w).length = w.length := by
  simp [l]

@[simp] public theorem length_r (w : Word) : (r w).length = w.length := by
  simp [r]

@[simp] public theorem l_r (w : Word) : l (r w) = w := by
  simp [l, r, List.map_reverse, Function.comp_def]

@[simp] public theorem r_l (w : Word) : r (l w) = w := by
  simp [l, r, List.map_reverse, Function.comp_def]


end OeisA108081
