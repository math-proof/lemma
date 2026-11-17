module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.Order.Grade
public import Mathlib.Order.Antichain
public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public section

open Finset


namespace SpernerProperty

class Poset (α : Type*) extends PartialOrder α, Fintype α

class GradedPoset (α : Type*) [PartialOrder α] [Fintype α] [GradeMinOrder ℕ α] where
  rank : ℕ
  grade_le_rank : ∀ (a : α), grade ℕ a ≤ rank
  grade_rank_exists : ∃ (a : α), grade ℕ a = rank

end SpernerProperty
