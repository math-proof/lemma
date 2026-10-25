/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Abbrev.FC.OeisA108081_count_words_in_x_is_a_shifted


namespace OeisA108081

open Nat


def l (w : Word) : Word :=
  w.reverse.map (fun x => x - 1)


def r (w : Word) : Word :=
  w.reverse.map (fun x => x + 1)

end OeisA108081
