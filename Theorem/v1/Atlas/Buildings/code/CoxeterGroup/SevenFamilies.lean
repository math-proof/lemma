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
public import Instance.v1.Atlas.Buildings.code.CoxeterGroup.SevenFamilies

public section

/-- The affine-$B$ adjacency predicate is symmetric in its arguments. -/
theorem affinBCond_comm (i j : ℕ) : affinBCond i j ↔ affinBCond j i := by
  unfold affinBCond
  constructor <;> intro h <;>
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  all_goals first
    | (right; left; exact ⟨h1 ▸ rfl, h2 ▸ rfl⟩)
    | (left; exact ⟨h1 ▸ rfl, h2 ▸ rfl⟩)
    | (right; right; right; left; exact ⟨h1 ▸ rfl, h2 ▸ rfl⟩)
    | (right; right; left; exact ⟨h1 ▸ rfl, h2 ▸ rfl⟩)
    | (right; right; right; right; right; exact ⟨h1, h2⟩)
    | (right; right; right; right; left; exact ⟨h1, h2⟩)

