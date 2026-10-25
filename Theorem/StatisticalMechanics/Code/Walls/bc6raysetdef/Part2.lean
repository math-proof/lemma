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
import Def.StatisticalMechanics.Code.Walls.bc6raysetdef.Part2
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


lemma bc6_offBoxCluster_subset_offBox {N : ℕ} {a : Fin d} {R : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} :
    bc6_offBoxCluster N a R ω ⊆ (box d N)ᶜ := by
  rintro x ⟨hxS, _, _⟩
  exact hxS


lemma bc6_mem_offBoxCluster_offBox {N : ℕ} {a : Fin d} {R : ℕ}
    {ω : ConfigSpace (Sym2 (Site d))} {x : Site d}
    (hx : x ∈ bc6_offBoxCluster N a R ω) : x ∉ box d N :=
  bc6_offBoxCluster_subset_offBox hx


lemma bc6_farEnd_notMem_box {N : ℕ} {a : Fin d} {R : ℕ} (hNR : N < R) :
    (hrHD_rayPt a (R : ℤ)) ∉ box d N := by
  rw [mem_box, not_forall]
  refine ⟨a, ?_⟩
  rw [hrHD_rayPt_self]
  simp only [Int.natAbs_natCast]
  omega


lemma bc6_farEnd_mem_offBoxCluster {N : ℕ} {a : Fin d} {R : ℕ} (hNR : N < R)
    (ω : ConfigSpace (Sym2 (Site d))) :
    (hrHD_rayPt a (R : ℤ)) ∈ bc6_offBoxCluster N a R ω := by
  have hoff : (hrHD_rayPt a (R : ℤ)) ∈ (box d N)ᶜ := bc6_farEnd_notMem_box hNR
  exact ⟨hoff, hoff, connectedWithin_refl _ _ _⟩


end Walls
end StatMech
