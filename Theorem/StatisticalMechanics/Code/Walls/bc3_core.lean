/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc3_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc2_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc3_barrierblocks
import Theorem.StatisticalMechanics.Code.Walls.bc3_rhoedgecases
import Theorem.StatisticalMechanics.Code.Walls.bc3_anchordecomp.Part2
import Def.StatisticalMechanics.Code.Walls.bc3_core
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


lemma bc3_mem_clusterNbhd {ω : ConfigSpace (Sym2 (Site d))} {j : Fin d} {L : ℕ} {x : Site d} :
    x ∈ bc3_clusterNbhd ω j L ↔
      ∃ t : ℕ, (1 ≤ t ∧ t ≤ L) ∧ x ∈ cluster d (removeSite 0 ω) (hrHD_rayPt j (t : ℤ)) := by
  simp only [bc3_clusterNbhd, Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht, hx⟩; exact ⟨t, ht, hx⟩
  · rintro ⟨t, ht, hx⟩; exact ⟨t, ht, hx⟩


lemma bc3_rayPt_mem_clusterNbhd {ω : ConfigSpace (Sym2 (Site d))} {j : Fin d} {L t : ℕ}
    (h1 : 1 ≤ t) (h2 : t ≤ L) : hrHD_rayPt j (t : ℤ) ∈ bc3_clusterNbhd ω j L := by
  rw [bc3_mem_clusterNbhd]
  exact ⟨t, ⟨h1, h2⟩, self_mem_cluster _ _⟩


lemma bc3_mouth_mem_clusterNbhd {ω : ConfigSpace (Sym2 (Site d))} {j : Fin d} {L : ℕ}
    (hL : 1 ≤ L) : (hrHD_rayPt j 1 : Site d) ∈ bc3_clusterNbhd ω j L := by
  have h : hrHD_rayPt j ((1 : ℕ) : ℤ) = hrHD_rayPt j 1 := by norm_num
  rw [← h]
  exact bc3_rayPt_mem_clusterNbhd le_rfl hL


lemma bc3_corridorEdge_structure {j : Fin d} {L : ℕ} {u v : Site d}
    (h : s(u, v) ∈ hrHD_corridorEdges j L) :
    ∃ p : ℕ, p < L ∧ s(u, v) = s(hrHD_rayPt j (p : ℤ), hrHD_rayPt j ((p : ℤ) + 1)) := by
  rw [hrHD_corridorEdges, Finset.mem_image] at h
  obtain ⟨p, hp, hpe⟩ := h
  rw [Finset.mem_range] at hp
  exact ⟨p, hp, hpe.symm⟩


end Walls
end StatMech
