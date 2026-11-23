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
public import Instance.v1.Atlas.AlgebraicCombinatorics.code.SpernerProperty

@[expose] public section

open Finset


namespace SpernerProperty

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

variable [GradeMinOrder ℕ α]

def HasOrderRaisingMatching (i : ℕ) : Prop :=
  ∃ (φ : α → α),
    (∀ x, grade ℕ x = i → grade ℕ (φ x) = i + 1) ∧
    (∀ x, grade ℕ x = i → x < φ x) ∧
    (∀ x y, grade ℕ x = i → grade ℕ y = i → φ x = φ y → x = y)

def HasOrderLoweringMatching (i : ℕ) : Prop :=
  ∃ (ψ : α → α),
    (∀ x, grade ℕ x = i → grade ℕ (ψ x) = i - 1) ∧
    (∀ x, grade ℕ x = i → ψ x < x) ∧
    (∀ x y, grade ℕ x = i → grade ℕ y = i → ψ x = ψ y → x = y)

def HasOrderMatchings [GradedPoset α] (j : ℕ) : Prop :=
  j ≤ GradedPoset.rank (α := α) ∧
  (∀ i, i < j → HasOrderRaisingMatching (α := α) i) ∧
  (∀ i, j < i → i ≤ GradedPoset.rank (α := α) → HasOrderLoweringMatching (α := α) i)

noncomputable def raise (φ : ℕ → α → α) (start : ℕ) : ℕ → α → α
  | 0, x => x
  | k + 1, x => φ (start + k) (raise φ start k x)

noncomputable def lower (ψ : ℕ → α → α) (start : ℕ) : ℕ → α → α
  | 0, x => x
  | k + 1, x => ψ (start - k) (lower ψ start k x)

end SpernerProperty
