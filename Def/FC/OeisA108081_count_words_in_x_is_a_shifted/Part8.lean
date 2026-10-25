/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Inductive.FC.OeisA108081_count_words_in_x_is_a_shifted.Part4


namespace OeisA108081

open Nat


def rightIndex (q : EdgeCoord) : ℤ := q.1 - if q.2 then 1 else 0


def CoordAdjacent (q r : EdgeCoord) : Prop :=
  r.1 = q.1 ∨ r.1 = rightIndex q ∨ r.1 = rightIndex q + 1

end OeisA108081
