/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part4
open Set Finset Filter Topology


namespace StatMech

namespace Lattice

theorem boxSV_mem_edgeF {d n : ℕ} {p : Site d × Site d} :
    p ∈ boxSV_edgeF d n ↔
      p.1 ∈ boxSV_boxF d n ∧ p.2 ∈ boxSV_boxF d n ∧ (hypercubicLattice d).Adj p.1 p.2 := by
  unfold boxSV_edgeF
  rw [Finset.mem_filter, Finset.mem_product, hypercubicLattice_adj]
  tauto


end Lattice
end StatMech
