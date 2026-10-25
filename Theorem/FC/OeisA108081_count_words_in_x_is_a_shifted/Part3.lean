/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.OeisA108081_count_words_in_x_is_a_shifted.Part5


namespace OeisA108081

open Nat


@[simp] lemma leftChild_edgeValue_false (k : ℤ) :
    leftChild (edgeValue (k, false)) = edgeValue (k, true) := by
  have h : Even (2 * k) := ⟨k, by ring⟩
  simp [leftChild, edgeValue, h]

@[simp] lemma leftChild_edgeValue_true (k : ℤ) :
    leftChild (edgeValue (k, true)) = edgeValue (k, false) := by
  have h : ¬ Even (2 * k - 1) := by
    rw [Int.not_even_iff_odd]
    exact ⟨k - 1, by ring⟩
  simp [leftChild, edgeValue, h]

@[simp] lemma rightChild_edgeValue_false (k : ℤ) :
    rightChild (edgeValue (k, false)) = edgeValue (k + 1, true) := by
  have h : Even (2 * k) := ⟨k, by ring⟩
  simp [rightChild, edgeValue, h]
  ring

@[simp] lemma rightChild_edgeValue_true (k : ℤ) :
    rightChild (edgeValue (k, true)) = edgeValue (k - 1, false) := by
  have h : ¬ Even (2 * k - 1) := by
    rw [Int.not_even_iff_odd]
    exact ⟨k - 1, by ring⟩
  simp [rightChild, edgeValue, h]
  ring

end OeisA108081
