/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA108081_count_words_in_x_is_a_shifted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.OeisA108081_count_words_in_x_is_a_shifted.Part6


namespace OeisA108081

open Nat


def ForestBits (m : ℕ) : Set (List Bool) :=
  {b | b.length = 2 * m + 1 ∧ b.count true = m}


def coordMovementBit (q r : EdgeCoord) : Bool :=
  if r.1 = q.1 then !q.2 else q.2


def coordsToBits : List EdgeCoord → List Bool
  | [] => []
  | [q] => [q.2]
  | q :: r :: s => q.2 :: coordMovementBit q r :: coordsToBits (r :: s)


def subsetBits (N : ℕ) (s : Finset (Fin N)) : List Bool :=
  List.ofFn (fun i => decide (i ∈ s))

end OeisA108081
