/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part3
open Set Finset Filter Topology


namespace StatMech

namespace Lattice

theorem boxSV_boundary_card (d n : ℕ) (hn : 1 ≤ n) :
    boxSV_boundaryCard d n = (2 * n + 1) ^ d - (2 * n - 1) ^ d := by
  unfold boxSV_boundaryCard
  rw [← boxSV_vbF_eq_toFinset, boxSV_vbF,
    Finset.card_sdiff_of_subset (boxSV_boxF_subset d (Nat.sub_le n 1)),
    boxSV_card_boxF, boxSV_card_boxF]
  congr 2
  omega


end Lattice
end StatMech
