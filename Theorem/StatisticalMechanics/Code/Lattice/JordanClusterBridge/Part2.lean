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
import Def.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jcb_boundedRegion_card_eq_one_of_nullity_one (P : PlanarZ2Subgraph)
    (h1 : nullity P.G = 1) : Nat.card (jcb_BoundedRegion P) = 1 := by
  rw [jcb_boundedRegion_card_eq_nullity, h1]


end Lattice
end StatMech
