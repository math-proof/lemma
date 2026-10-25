/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc22trifexist.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc20mengerroute.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc21trifurc.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneAttachment.Part4
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech.Walls

variable {d : ℕ}


universe u

variable {V : Type u} {GG : SimpleGraph V}


theorem bc22_through_index_unique {A B : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily GG A B ι) (z₀ : V) {i j : ι}
    (hi : z₀ ∈ (F.p i).support) (hj : z₀ ∈ (F.p j).support) : i = j := by
  by_contra hne
  exact F.hdisj hne hi hj


theorem bc22_subfamily_avoiding {A B : Set V} {k : ℕ}
    (F : bc16_DisjointPathFamily GG A B (Fin (k + 1))) (z₀ : V) :
    ∃ G : bc16_DisjointPathFamily GG A B (Fin k),
      ∀ i : Fin k, z₀ ∉ (G.p i).support := by
  classical
  
  by_cases hex : ∃ i₀ : Fin (k + 1), z₀ ∈ (F.p i₀).support
  · obtain ⟨i₀, hi₀⟩ := hex
    
    refine ⟨⟨fun i => F.a (i₀.succAbove i), fun i => F.b (i₀.succAbove i),
      fun i => F.p (i₀.succAbove i), fun i => F.ha _, fun i => F.hb _, fun i => F.hp _, ?_⟩, ?_⟩
    · intro i j hij x hxi hxj
      exact F.hdisj (fun h => hij (i₀.succAbove_right_injective h)) hxi hxj
    · intro i hmem
      
      have heq : i₀.succAbove i = i₀ := bc22_through_index_unique F z₀ hmem hi₀
      exact (i₀.succAbove_ne i) heq
  · push Not at hex
    
    refine ⟨⟨fun i => F.a i.castSucc, fun i => F.b i.castSucc, fun i => F.p i.castSucc,
      fun i => F.ha _, fun i => F.hb _, fun i => F.hp _, ?_⟩, ?_⟩
    · intro i j hij x hxi hxj
      exact F.hdisj (fun h => hij (Fin.castSucc_injective k h)) hxi hxj
    · intro i; exact hex i.castSucc


theorem bc22_three_origin_avoiding_boxPaths_of_min4 (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {A B : Set (box d m)}
    (hmin : ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω) A B C → 4 ≤ C.ncard) :
    ∃ G : bc16_DisjointPathFamily (bc20_boxGraph d m ω) A B (Fin 3),
      ∀ i : Fin 3, bc20_originBox d m ∉ (G.p i).support := by
  obtain ⟨F⟩ := bc20_hardDir_boxGraph d m ω A B 4 hmin
  exact bc22_subfamily_avoiding F (bc20_originBox d m)


theorem bc22_connected_removeSite_of_path (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {u v : box d m} (p : (bc20_boxGraph d m ω).Walk u v) (h0 : bc20_originBox d m ∉ p.support) :
    Connected d (removeSite 0 ω) (u : Site d) (v : Site d) :=
  bc20_connected_removeSite_of_avoiding ω (bc20_mapWalk d m ω p)
    (bc20_origin_avoid_of_boxAvoid d m ω p h0)


theorem bc22_branch_origin_cut_survival (d m : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {A B : Set (box d m)}
    (hmin : ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω) A B C → 2 ≤ C.ncard) :
    ∃ (u v : box d m), u ∈ A ∧ v ∈ B ∧
      Connected d (removeSite 0 ω) (u : Site d) (v : Site d) :=
  bc20_connected_removeSite_of_min2 d m ω hmin


theorem bc22_mem_cluster_of_connected (ϱ : ConfigSpace (Sym2 (Site d))) {a u v : Site d}
    (hu : u ∈ cluster d ϱ a) (huv : Connected d ϱ u v) : v ∈ cluster d ϱ a := by
  rw [mem_cluster] at hu ⊢
  exact hu.trans huv


end StatMech.Walls
