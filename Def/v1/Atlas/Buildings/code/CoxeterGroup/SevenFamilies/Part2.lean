/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SevenFamilies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Coxeter.Basic
public import Def.v1.Atlas.Buildings.code.CoxeterGroup.TypeACoxeterSystem.Part2
public import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper
public import Def.v1.Atlas.Buildings.code.CoxeterGroup.SignedPermGroup.Part2
public import Def.v1.Atlas.Buildings.code.CoxeterGroup.TypeCInjectivityHelper
public import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.SevenFamilies

@[expose] public section

/-- Adjacency predicate encoding the edges of the affine type-$\tilde D_n$ Dynkin diagram. -/
def affinDCond (n i j : ℕ) : Prop :=
  (i = 0 ∧ j = 2) ∨ (j = 0 ∧ i = 2) ∨
  (i = 1 ∧ j = 2) ∨ (j = 1 ∧ i = 2) ∨
  (i + 1 = j ∧ i ≥ 2 ∧ j + 2 ≤ n) ∨ (j + 1 = i ∧ j ≥ 2 ∧ i + 2 ≤ n) ∨
  (i + 2 = n ∧ j = n - 1) ∨ (j + 2 = n ∧ i = n - 1) ∨
  (i + 2 = n ∧ j = n) ∨ (j + 2 = n ∧ i = n)

