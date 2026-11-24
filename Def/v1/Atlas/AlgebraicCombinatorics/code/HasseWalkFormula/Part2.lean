module
public import Def.v1.Atlas.AlgebraicCombinatorics.code.NormalOrderCoeff.Part2
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.NormalOrderCoeff
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.HasseWalks
public import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkCountOps
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkCountBridge
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkOperatorLemmas
public import Theorem.v1.Atlas.AlgebraicCombinatorics.code.HasseWalks
public import Def.v1.Atlas.AlgebraicCombinatorics.code.WalkCountOps
public import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WalkCountBridge.Part2
public import Theorem.v1.Atlas.AlgebraicCombinatorics.code.WalkOperatorLemmas
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Instance.v1.Atlas.AlgebraicCombinatorics.code.HasseWalkFormula
set_option autoImplicit false
open scoped Nat


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalkFormula.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
def HasseWalkFormula.UpWalkType (n : ℕ) (lam : YoungDiagram) :=
  { walk : Fin (n + 1) → YoungDiagram //
    walk ⟨0, Nat.zero_lt_succ _⟩ = ⊥ ∧
    walk ⟨n, Nat.lt_succ_of_le le_rfl⟩ = lam ∧
    ∀ i : Fin n,
      walk ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⋖
        walk ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ }

