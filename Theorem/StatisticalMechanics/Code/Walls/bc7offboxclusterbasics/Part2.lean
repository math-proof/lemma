/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc7offboxclusterbasics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc6raysetdef.Part3
import Def.StatisticalMechanics.Code.Walls.bc7offboxclusterbasics
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc7_offBoxClusterBasics_holds {N : ℕ} {a : Fin d} {R : ℕ} (hNR : N < R)
    (ω : ConfigSpace (Sym2 (Site d))) :
    bc7_offBoxClusterBasics N a R ω :=
  ⟨bc7_farEnd_mem_offBoxCluster hNR ω, bc7_offBoxCluster_subset_offBox⟩


theorem bc7_offBoxClusterBasics_iff {N : ℕ} {a : Fin d} {R : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} :
    bc7_offBoxClusterBasics N a R ω ↔
      (hrHD_rayPt a (R : ℤ)) ∈ bc6_offBoxCluster N a R ω ∧
        ∀ x ∈ bc6_offBoxCluster N a R ω, x ∉ box d N := by
  unfold bc7_offBoxClusterBasics
  constructor
  · rintro ⟨hfar, hsub⟩
    exact ⟨hfar, fun x hx => hsub hx⟩
  · rintro ⟨hfar, hmem⟩
    exact ⟨hfar, fun x hx => hmem x hx⟩

end Walls
end StatMech
