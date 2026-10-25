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
import Def.StatisticalMechanics.Code.Walls.bc20mengerroute.Part3
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech.Walls

variable {d : ℕ}


theorem bc20_connected_removeSite_of_avoiding (ω : ConfigSpace (Sym2 (Site d)))
    {a x : Site d} (w : (openSubgraph d ω).Walk a x) (h0 : (0 : Site d) ∉ w.support) :
    Connected d (removeSite 0 ω) a x :=
  (bc20_walk_removeSite ω w h0).reachable


theorem bc20_origin_avoid_of_boxAvoid (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {u v : box d m} (p : (bc20_boxGraph d m ω).Walk u v)
    (h : bc20_originBox d m ∉ p.support) :
    (0 : Site d) ∉ (bc20_mapWalk d m ω p).support := by
  intro hmem
  rw [bc20_mapWalk_support, List.mem_map] at hmem
  obtain ⟨w, hw, hw0⟩ := hmem
  have hwe : w = bc20_originBox d m := Subtype.ext hw0
  exact h (hwe ▸ hw)


universe u

variable {V : Type u} [DecidableEq V] {GG : SimpleGraph V}

omit [DecidableEq V] in


theorem bc20_unique_index_through {A B : Set V} {k : ℕ}
    (F : bc16_DisjointPathFamily GG A B (Fin k)) (z₀ : V) {i j : Fin k}
    (hi : z₀ ∈ (F.p i).support) (hj : z₀ ∈ (F.p j).support) : i = j := by
  by_contra hne
  exact F.hdisj hne hi hj

omit [DecidableEq V] in


theorem bc20_disjointFamily_avoids_origin {A B : Set V}
    (F : bc16_DisjointPathFamily GG A B (Fin 2)) (z₀ : V) :
    ∃ i : Fin 2, z₀ ∉ (F.p i).support := by
  by_contra h
  push Not at h
  exact F.hdisj (by decide) (h 0) (h 1)


theorem bc20_origin_avoiding_boxPath_of_min2 (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {A B : Set (box d m)}
    (hmin : ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω) A B C → 2 ≤ C.ncard) :
    ∃ (u v : box d m) (p : (bc20_boxGraph d m ω).Walk u v),
      u ∈ A ∧ v ∈ B ∧ bc20_originBox d m ∉ p.support := by
  obtain ⟨F⟩ := bc20_hardDir_boxGraph d m ω A B 2 hmin
  obtain ⟨i, hi⟩ := bc20_disjointFamily_avoids_origin F (bc20_originBox d m)
  exact ⟨F.a i, F.b i, F.p i, F.ha i, F.hb i, hi⟩


theorem bc20_connected_removeSite_of_min2 (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {A B : Set (box d m)}
    (hmin : ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω) A B C → 2 ≤ C.ncard) :
    ∃ (u v : box d m), u ∈ A ∧ v ∈ B ∧
      Connected d (removeSite 0 ω) (u : Site d) (v : Site d) := by
  obtain ⟨u, v, p, hu, hv, h0⟩ := bc20_origin_avoiding_boxPath_of_min2 d m ω hmin
  refine ⟨u, v, hu, hv, ?_⟩
  exact bc20_connected_removeSite_of_avoiding ω (bc20_mapWalk d m ω p)
    (bc20_origin_avoid_of_boxAvoid d m ω p h0)


end StatMech.Walls
