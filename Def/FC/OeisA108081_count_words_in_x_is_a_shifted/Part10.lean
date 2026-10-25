/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.OeisA108081_count_words_in_x_is_a_shifted.Part5


namespace OeisA108081

open Nat


def xN (n : ℕ) : Set Word :=
  {w : Word | XWord w ∧ w.length = n}


def coordXN (n : ℕ) : Set (List EdgeCoord) :=
  {w | CoordInsert w ∧ w.length = n}


def bitStep (k : ℤ) (e y : Bool) : ℤ :=
  if e = y then if e then k - 1 else k + 1 else k


def bitsToCoords : ℤ → List Bool → List EdgeCoord
  | _, [] => []
  | k, e :: bs => (k, e) :: match bs with
    | [] => []
    | y :: cs => bitsToCoords (bitStep k e y) cs

end OeisA108081
