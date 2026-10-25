/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.OeisA108081_count_words_in_x_is_a_shifted.Part2


namespace OeisA108081

open Nat


@[simp] lemma length_l (w : Word) : (l w).length = w.length := by
  simp [l]

@[simp] lemma length_r (w : Word) : (r w).length = w.length := by
  simp [r]

@[simp] lemma l_r (w : Word) : l (r w) = w := by
  simp [l, r, List.map_reverse, Function.comp_def]

@[simp] lemma r_l (w : Word) : r (l w) = w := by
  simp [l, r, List.map_reverse, Function.comp_def]


end OeisA108081
