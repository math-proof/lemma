/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.OeisA108081_count_words_in_x_is_a_shifted.Part8


namespace OeisA108081

open Nat


inductive CoordPath : List EdgeCoord → Prop
  | nil : CoordPath []
  | singleton (q : EdgeCoord) : CoordPath [q]
  | cons {q r : EdgeCoord} {s : List EdgeCoord}
      (hqr : CoordAdjacent q r) (hrs : CoordPath (r :: s)) :
      CoordPath (q :: r :: s)


end OeisA108081
