/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part2
open Set Finset Filter Topology


namespace StatMech

namespace Lattice

theorem boxSV_coe_vbF (d n : ℕ) : ↑(boxSV_vbF d n) = vertexBoundary d n := by
  unfold boxSV_vbF vertexBoundary
  rw [Finset.coe_sdiff, boxSV_coe_boxF, boxSV_coe_boxF]

theorem boxSV_vbF_eq_toFinset (d n : ℕ) :
    boxSV_vbF d n = (vertexBoundary_finite d n).toFinset := by
  apply Finset.coe_injective
  rw [boxSV_coe_vbF, Set.Finite.coe_toFinset]


end Lattice
end StatMech
