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
public import Class.v1.Atlas.AlgebraicCombinatorics.code.SpernerProperty

@[expose] public section

open Finset


namespace SpernerProperty

variable {α : Type*} [PartialOrder α] [Fintype α] [DecidableEq α]

def rankCount [GradeMinOrder ℕ α] (i : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : α => grade ℕ x = i)).card

def IsRankSymmetric [GradeMinOrder ℕ α] [GradedPoset α] : Prop :=
  let n := GradedPoset.rank (α := α)
  ∀ i : ℕ, i ≤ n → rankCount (α := α) i = rankCount (α := α) (n - i)

def IsRankUnimodal [GradeMinOrder ℕ α] [GradedPoset α] : Prop :=
  let n := GradedPoset.rank (α := α)
  ∃ j : ℕ, j ≤ n ∧
    (∀ i₁ i₂ : ℕ, i₁ ≤ i₂ → i₂ ≤ j → rankCount (α := α) i₁ ≤ rankCount (α := α) i₂) ∧
    (∀ i₁ i₂ : ℕ, j ≤ i₁ → i₁ ≤ i₂ → i₂ ≤ n → rankCount (α := α) i₂ ≤ rankCount (α := α) i₁)

def maxRankCount [GradeMinOrder ℕ α] [GradedPoset α] : ℕ :=
  (Finset.range (GradedPoset.rank (α := α) + 1)).sup (fun i => rankCount (α := α) i)

def HasSpernerProperty [GradeMinOrder ℕ α] [GradedPoset α] : Prop :=
  ∀ (A : Finset α), IsAntichain (· ≤ ·) (A : Set α) → A.card ≤ maxRankCount (α := α)

end SpernerProperty
