/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.OeisA108081_count_words_in_x_is_a_shifted


namespace OeisA108081

open Nat


inductive XWord : Word → Prop
  | base : XWord [0]
  | step_left {u v : Word} (hu : XWord u) (hv : XWord v) : XWord (l u ++ v)
  | step_right {u v : Word} (hu : XWord u) (hv : XWord v) : XWord (u ++ r v)


end OeisA108081
