/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Inductive.FC.OeisA108081_count_words_in_x_is_a_shifted.Part3


namespace OeisA108081

open Nat


def XInsert (w : Word) : Prop := Relation.ReflTransGen Expand [0] w


def CoordInsert (w : List EdgeCoord) : Prop :=
  Relation.ReflTransGen CoordExpand [(0, false)] w


end OeisA108081
