/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc19menger.Part5
import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part3
import Theorem.StatisticalMechanics.Code.Percolation.AvoidingAttachment.Part3
import Def.StatisticalMechanics.Code.Walls.bc20mengerroute.Part2
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech.Walls

variable {d : ℕ}


theorem bc20_mapWalk_support (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {u v : box d m} (p : (bc20_boxGraph d m ω).Walk u v) :
    (bc20_mapWalk d m ω p).support
      = (p.support).map (Embedding.induce (G := openSubgraph d ω) (box d m)).toHom :=
  Walk.support_map _ _


theorem bc20_connected_of_boxWalk (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {u v : box d m} (p : (bc20_boxGraph d m ω).Walk u v) :
    Connected d ω (u : Site d) (v : Site d) :=
  (bc20_mapWalk d m ω p).reachable


theorem bc20_boxWalk_support_mem_box (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {u v : box d m} (p : (bc20_boxGraph d m ω).Walk u v) :
    ∀ z ∈ (bc20_mapWalk d m ω p).support, z ∈ box d m := by
  intro z hz
  rw [bc20_mapWalk_support, List.mem_map] at hz
  obtain ⟨w, _, rfl⟩ := hz
  exact w.2


theorem bc20_edge_removeSite (ω : ConfigSpace (Sym2 (Site d))) {x y : Site d}
    (hadj : (openSubgraph d ω).Adj x y) (hx : x ≠ 0) (hy : y ≠ 0) :
    (openSubgraph d (removeSite 0 ω)).Adj x y := by
  obtain ⟨hadj', hval⟩ := hadj
  refine ⟨hadj', ?_⟩
  have h0 : (0 : Site d) ∉ s(x, y) := by
    rw [Sym2.mem_iff]; push Not; exact ⟨fun h => hx h.symm, fun h => hy h.symm⟩
  rw [removeSite_apply_of_notMem h0]; exact hval


end StatMech.Walls
