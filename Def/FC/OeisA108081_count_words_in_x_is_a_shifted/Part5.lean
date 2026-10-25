/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.OeisA108081_count_words_in_x_is_a_shifted.Part2


namespace OeisA108081

open Nat


def edgeEquiv : EdgeCoord ≃ ℤ where
  toFun := edgeValue
  invFun := edgeCoord
  left_inv := edgeCoord_edgeValue
  right_inv := edgeValue_edgeCoord

end OeisA108081
