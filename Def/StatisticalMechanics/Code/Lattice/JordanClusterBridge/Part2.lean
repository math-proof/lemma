/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanClusterBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
import Instance.StatisticalMechanics.Code.Lattice.JordanClusterBridge
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[reducible] noncomputable def jcb_uniqueBoundedRegion_of_nullity_one (P : PlanarZ2Subgraph)
    (h1 : nullity P.G = 1) : Unique (jcb_BoundedRegion P) := by
  have hcard : Nat.card (jcb_BoundedRegion P) = 1 := by
    rw [jcb_boundedRegion_card_eq_nullity, h1]
  obtain ⟨hsub, hne⟩ := Nat.card_eq_one_iff_unique.mp hcard
  exact ⟨⟨hne.some⟩, fun a => hsub.elim a hne.some⟩


end Lattice
end StatMech
