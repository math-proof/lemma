/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Order.Grade
import Mathlib.Order.Antichain
import Mathlib.Data.Finset.Grade
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold

open Finset

namespace SpernerProperty

class Poset (α : Type*) extends PartialOrder α, Fintype α

class GradedPoset (α : Type*) [PartialOrder α] [Fintype α] [GradeMinOrder ℕ α] where
  rank : ℕ
  grade_le_rank : ∀ (a : α), grade ℕ a ≤ rank
  grade_rank_exists : ∃ (a : α), grade ℕ a = rank

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

abbrev BooleanPoset (n : ℕ) : Type := Finset (Fin n)

instance booleanPoset_gradedPoset (n : ℕ) : GradedPoset (BooleanPoset n) where
  rank := n
  grade_le_rank a := by
    simp only [Finset.grade_eq]
    calc a.card ≤ Fintype.card (Fin n) := Finset.card_le_univ a
    _ = n := Fintype.card_fin n
  grade_rank_exists := by
    exact ⟨Finset.univ, by simp [Finset.grade_eq, Finset.card_fin]⟩

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
