/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalkFormula.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicCombinatorics.code.NormalOrderCoeff.Part2
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.NormalOrderCoeff
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.HasseWalks
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkCountOps
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkCountBridge
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkOperatorLemmas
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.HasseWalks
import Def.v1.Atlas.AlgebraicCombinatorics.code.WalkCountOps
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WalkCountBridge.Part2
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WalkOperatorLemmas
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Combinatorics.Young.YoungDiagram
set_option autoImplicit false

open scoped Nat


noncomputable def HasseWalkFormula.numSYT (lam : YoungDiagram) : ℕ := by
  classical
  exact Nat.card { chain : Fin (lam.card + 1) → YoungDiagram //
    chain ⟨0, Nat.zero_lt_succ _⟩ = ⊥ ∧
    chain ⟨lam.card, Nat.lt_succ_of_le le_rfl⟩ = lam ∧
    ∀ i : Fin lam.card,
      chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
      chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ }

noncomputable def HasseWalkFormula.hasseWalkCount (ell : ℕ) (lam : YoungDiagram) : ℕ := by
  classical
  exact Nat.card { walk : Fin (ell + 1) → YoungDiagram //
    walk ⟨0, Nat.zero_lt_succ _⟩ = ⊥ ∧
    walk ⟨ell, Nat.lt_succ_of_le le_rfl⟩ = lam ∧
    ∀ i : Fin ell,
      walk ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
        walk ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ∨
      walk ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ⋖
        walk ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ }

noncomputable def HasseWalkFormula.upWalkCount (n : ℕ) (lam : YoungDiagram) : ℕ := by
  classical
  exact Nat.card { walk : Fin (n + 1) → YoungDiagram //
    walk ⟨0, Nat.zero_lt_succ _⟩ = ⊥ ∧
    walk ⟨n, Nat.lt_succ_of_le le_rfl⟩ = lam ∧
    ∀ i : Fin n,
      walk ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
        walk ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ }

def HasseWalkFormula.HasseWalkType (n : ℕ) (lam : YoungDiagram) :=
  { walk : Fin (n + 1) → YoungDiagram //
    walk ⟨0, Nat.zero_lt_succ _⟩ = ⊥ ∧
    walk ⟨n, Nat.lt_succ_of_le le_rfl⟩ = lam ∧
    ∀ i : Fin n,
      walk ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
        walk ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ∨
      walk ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ⋖
        walk ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ }

