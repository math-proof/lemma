/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterContourBijection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part2
open Set Finset


namespace StatMech

namespace Lattice

open StatMech.Ising

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem ccb_connClusterFamily_props {n : ℕ} {K : Finset (Site d)}
    (hK : K ∈ connClusterFamily (d := d) n) :
    IsConnectedCluster K ∧ (↑K : Set (Site d)) ⊆ box d n := by
  rw [pcc_mem_connClusterFamily] at hK
  exact ⟨hK.2, clusterFamily_subset_box hK.1⟩


end Lattice
end StatMech
