/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.OeisA108081_count_words_in_x_is_a_shifted.Part7


namespace OeisA108081

open Nat


def coordForestXN (m : ℕ) : Set (List EdgeCoord) :=
  {w | CoordForestForm (0, false) w ∧ w.length = m + 1}


def TreeBits (m : ℕ) : Set (List Bool) :=
  coordsToBits '' coordXN (m + 1)


def CoordTree (root : EdgeCoord) (w : List EdgeCoord) : Prop :=
  Relation.ReflTransGen CoordExpand [root] w

end OeisA108081
