/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.OeisA108081_count_words_in_x_is_a_shifted.Part4


namespace OeisA108081

open Nat


inductive CoordExpand : List EdgeCoord → List EdgeCoord → Prop
  | left (p s : List EdgeCoord) (q : EdgeCoord) :
      CoordExpand (p ++ q :: s) (p ++ coordLeft q :: q :: s)
  | right (p s : List EdgeCoord) (q : EdgeCoord) :
      CoordExpand (p ++ q :: s) (p ++ q :: coordRight q :: s)


end OeisA108081
