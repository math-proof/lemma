/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.OeisA108081_count_words_in_x_is_a_shifted.Part3


namespace OeisA108081

open Nat


inductive Expand : Word → Word → Prop
  | left (p s : Word) (z : ℤ) :
      Expand (p ++ z :: s) (p ++ leftChild z :: z :: s)
  | right (p s : Word) (z : ℤ) :
      Expand (p ++ z :: s) (p ++ z :: rightChild z :: s)


end OeisA108081
