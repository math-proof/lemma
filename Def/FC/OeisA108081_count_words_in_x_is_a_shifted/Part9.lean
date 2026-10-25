/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Inductive.FC.OeisA108081_count_words_in_x_is_a_shifted.Part5


namespace OeisA108081

open Nat


def CoordForestForm (root : EdgeCoord) (w : List EdgeCoord) : Prop :=
  w = [] ∨
    CoordPath w ∧ (w.head?.map Prod.fst = some root.1) ∧
      (w.getLast?.map rightIndex = some (rightIndex root))

end OeisA108081
