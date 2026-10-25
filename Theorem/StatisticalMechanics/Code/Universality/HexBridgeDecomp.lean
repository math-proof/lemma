/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp


namespace StatMech.Universality

open List


namespace HexBridge

theorem rungs_ne_nil (b : HexBridge) : b.rungs ≠ [] := by
  simp only [rungs, ne_eq, List.map_eq_nil_iff]
  exact b.content_ne


theorem mem_rungs_fst {b : HexBridge} {p : ℕ × ℤ} (hp : p ∈ b.rungs) : p.1 = b.width := by
  simp only [rungs, List.mem_map] at hp
  obtain ⟨t, _, rfl⟩ := hp
  rfl


@[simp]
theorem length_rungs (b : HexBridge) : b.rungs.length = b.content.length := by
  simp [rungs]

end HexBridge
end StatMech.Universality
