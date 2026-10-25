/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SevenFamilies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.TypeACoxeterSystem.Part2
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper
import Def.v1.Atlas.Buildings.code.CoxeterGroup.SignedPermGroup.Part2
import Def.v1.Atlas.Buildings.code.CoxeterGroup.TypeCInjectivityHelper
import Instance.v1.Atlas.Buildings.code.CoxeterGroup.SevenFamilies.Part2


/-- The affine-$D$ adjacency predicate is symmetric in $i$ and $j$. -/
theorem affinDCond_comm (n i j : ℕ) : affinDCond n i j ↔ affinDCond n j i := by
  unfold affinDCond
  constructor <;> intro h <;>
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
                  ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  all_goals first
    | (right; left; exact ⟨h1 ▸ rfl, h2 ▸ rfl⟩)
    | (left; exact ⟨h1 ▸ rfl, h2 ▸ rfl⟩)
    | (right; right; right; left; exact ⟨h1 ▸ rfl, h2 ▸ rfl⟩)
    | (right; right; left; exact ⟨h1 ▸ rfl, h2 ▸ rfl⟩)
    | (right; right; right; right; right; left; exact ⟨h1, h2, h3⟩)
    | (right; right; right; right; left; exact ⟨h1, h2, h3⟩)
    | (right; right; right; right; right; right; right; left; constructor <;> omega)
    | (right; right; right; right; right; right; left; constructor <;> omega)
    | (right; right; right; right; right; right; right; right; right; constructor <;> omega)
    | (right; right; right; right; right; right; right; right; left; constructor <;> omega)

