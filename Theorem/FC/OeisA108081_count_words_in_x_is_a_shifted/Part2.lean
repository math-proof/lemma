/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.OeisA108081_count_words_in_x_is_a_shifted.Part4


namespace OeisA108081

open Nat


@[simp] lemma edgeValue_edgeCoord (z : ℤ) : edgeValue (edgeCoord z) = z := by
  simp only [edgeCoord]
  split_ifs with h
  · obtain ⟨k, hk⟩ := h
    simp only [edgeValue, Bool.false_eq_true, ↓reduceIte]
    omega
  · have ho : Odd z := Int.not_even_iff_odd.mp h
    obtain ⟨k, hk⟩ := ho
    simp only [edgeValue, ↓reduceIte]
    omega

@[simp] lemma edgeCoord_edgeValue (q : EdgeCoord) : edgeCoord (edgeValue q) = q := by
  rcases q with ⟨k, e⟩
  cases e <;> simp [edgeCoord, edgeValue]


end OeisA108081
