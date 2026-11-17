/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Grade
public import Mathlib.Order.Antichain
public import Mathlib.Data.Finset.Grade
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Abbrev.v1.Atlas.AlgebraicCombinatorics.code.SpernerProperty

@[expose] public section

open Finset


namespace SpernerProperty

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

instance booleanPoset_gradedPoset (n : ℕ) : GradedPoset (BooleanPoset n) where
  rank := n
  grade_le_rank a := by
    simp only [Finset.grade_eq]
    calc a.card ≤ Fintype.card (Fin n) := Finset.card_le_univ a
    _ = n := Fintype.card_fin n
  grade_rank_exists := by
    exact ⟨Finset.univ, by simp [Finset.grade_eq, Finset.card_fin]⟩

end SpernerProperty
