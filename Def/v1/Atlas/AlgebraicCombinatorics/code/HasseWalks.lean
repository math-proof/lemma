/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Grade
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Linarith
import Inductive.v1.Atlas.AlgebraicCombinatorics.code.HasseWalks


namespace HasseWalks

def HStep.toInt : HStep → ℤ
  | HStep.U => 1
  | HStep.D => -1

def expandBlock (p : ℕ × ℕ) : List HStep :=
  List.replicate p.1 HStep.U ++ List.replicate p.2 HStep.D

def expandBlocks (w : List (ℕ × ℕ)) : List HStep :=
  w.flatMap expandBlock

def displacement (w : List (ℕ × ℕ)) : ℤ :=
  (w.map fun p => (p.1 : ℤ) - (p.2 : ℤ)).sum

def partialDisplacement (w : List (ℕ × ℕ)) (j : ℕ) : ℤ :=
  displacement (w.take j)

def IsValidWord (w : List (ℕ × ℕ)) (n : ℕ) : Prop :=
  displacement w = (n : ℤ) ∧
  ∀ j, 1 ≤ j → j ≤ w.length → 0 ≤ partialDisplacement w j

end HasseWalks
