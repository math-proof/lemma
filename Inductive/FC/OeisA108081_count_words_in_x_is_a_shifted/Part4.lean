/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.OeisA108081_count_words_in_x_is_a_shifted.Part7


namespace OeisA108081

open Nat


inductive CoordForest (root : EdgeCoord) : List EdgeCoord → Prop
  | nil : CoordForest root []
  | cons {u v : List EdgeCoord} :
      Relation.ReflTransGen CoordExpand [root] u →
      CoordForest root v → CoordForest root (u ++ v)


end OeisA108081
