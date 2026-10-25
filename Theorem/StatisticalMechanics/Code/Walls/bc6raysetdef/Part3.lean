/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6raysetdef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc3_core.Part3
import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Def.StatisticalMechanics.Code.Walls.bc6raysetdef.Part3
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


lemma bc6_mem_armRegion {N : ℕ} {a : Fin d} {R : ℕ} {ω : ConfigSpace (Sym2 (Site d))}
    {x : Site d} :
    x ∈ bc6_armRegion N a R ω ↔
      x ∈ bc6_rayInterior a R ∨ x ∈ bc6_offBoxCluster N a R ω :=
  Set.mem_union _ _ _


lemma bc6_rayInterior_subset_armRegion {N : ℕ} {a : Fin d} {R : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} :
    bc6_rayInterior a R ⊆ bc6_armRegion N a R ω :=
  Set.subset_union_left


lemma bc6_offBoxCluster_subset_armRegion {N : ℕ} {a : Fin d} {R : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} :
    bc6_offBoxCluster N a R ω ⊆ bc6_armRegion N a R ω :=
  Set.subset_union_right


lemma bc6_rayPt_mem_armRegion {N : ℕ} {a : Fin d} {R p : ℕ} {ω : ConfigSpace (Sym2 (Site d))}
    (h1 : 1 ≤ p) (h2 : p ≤ R) :
    hrHD_rayPt a (p : ℤ) ∈ bc6_armRegion N a R ω :=
  bc6_rayInterior_subset_armRegion (bc6_rayPt_mem_rayInterior h1 h2)


lemma bc6_mouth_mem_armRegion {N : ℕ} {a : Fin d} {R : ℕ} {ω : ConfigSpace (Sym2 (Site d))}
    (hR : 1 ≤ R) :
    (hrHD_rayPt a 1 : Site d) ∈ bc6_armRegion N a R ω :=
  bc6_rayInterior_subset_armRegion (bc6_mouth_mem_rayInterior hR)


lemma bc6_farEnd_mem_armRegion {N : ℕ} {a : Fin d} {R : ℕ} (hNR : N < R)
    (ω : ConfigSpace (Sym2 (Site d))) :
    (hrHD_rayPt a (R : ℤ)) ∈ bc6_armRegion N a R ω :=
  bc6_offBoxCluster_subset_armRegion (bc6_farEnd_mem_offBoxCluster hNR ω)

end Walls
end StatMech
