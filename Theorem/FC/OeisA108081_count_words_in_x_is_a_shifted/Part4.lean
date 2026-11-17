/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Def.FC.OeisA108081_count_words_in_x_is_a_shifted.Part5
public import Def.FC.OeisA108081_count_words_in_x_is_a_shifted.Part6

@[expose] public section



namespace OeisA108081

open Nat


@[simp] public theorem map_edgeValue_coordWord (w : Word) :
    (coordWord w).map edgeValue = w := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
      change edgeValue (edgeCoord x) :: (coordWord xs).map edgeValue = x :: xs
      simp [ih]

@[simp] public theorem coordWord_map_edgeValue (w : List EdgeCoord) :
    coordWord (w.map edgeValue) = w := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
      change edgeCoord (edgeValue x) :: coordWord (xs.map edgeValue) = x :: xs
      simp [ih]

@[simp] public theorem edgeValue_coordLeft (q : EdgeCoord) :
    edgeValue (coordLeft q) = leftChild (edgeValue q) := by
  rcases q with ⟨k, e⟩
  cases e <;> simp [coordLeft]

@[simp] public theorem edgeValue_coordRight (q : EdgeCoord) :
    edgeValue (coordRight q) = rightChild (edgeValue q) := by
  rcases q with ⟨k, e⟩
  cases e <;> simp [coordRight]

@[simp] public theorem edgeCoord_leftChild (z : ℤ) :
    edgeCoord (leftChild z) = coordLeft (edgeCoord z) := by
  apply (Equiv.injective edgeEquiv)
  simp [edgeEquiv]

@[simp] public theorem edgeCoord_rightChild (z : ℤ) :
    edgeCoord (rightChild z) = coordRight (edgeCoord z) := by
  apply (Equiv.injective edgeEquiv)
  simp [edgeEquiv]


end OeisA108081
