/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Abbrev.FC.OeisA108081_count_words_in_x_is_a_shifted.Part2


namespace OeisA108081

open Nat


def edgeValue (q : EdgeCoord) : ℤ :=
  2 * q.1 - if q.2 then 1 else 0

def edgeCoord (z : ℤ) : EdgeCoord :=
  if h : Even z then (z / 2, false) else ((z + 1) / 2, true)

end OeisA108081
