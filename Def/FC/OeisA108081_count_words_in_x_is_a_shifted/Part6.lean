/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.OeisA108081_count_words_in_x_is_a_shifted.Part3


namespace OeisA108081

open Nat


def coordLeft : EdgeCoord → EdgeCoord
  | (k, false) => (k, true)
  | (k, true) => (k, false)

def coordRight : EdgeCoord → EdgeCoord
  | (k, false) => (k + 1, true)
  | (k, true) => (k - 1, false)


def coordWord (w : Word) : List EdgeCoord := w.map edgeCoord

end OeisA108081
