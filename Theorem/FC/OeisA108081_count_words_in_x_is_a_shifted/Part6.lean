/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.OeisA108081_count_words_in_x_is_a_shifted.Part10


namespace OeisA108081

open Nat


@[simp] lemma bitsToCoords_cons (k : ℤ) (e : Bool) (b : List Bool) :
    bitsToCoords k (e :: b) = (k, e) :: match b with
      | [] => []
      | y :: cs => bitsToCoords (bitStep k e y) cs := by
  cases b <;> rfl


end OeisA108081
