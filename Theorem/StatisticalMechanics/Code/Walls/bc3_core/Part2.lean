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
import Def.StatisticalMechanics.Code.Walls.bc3_core.Part2
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


lemma bc3_sameAxis_step_mem (ω : ConfigSpace (Sym2 (Site d))) (a : Fin d) (La : ℕ)
    {u v : Site d} (hno0 : (0 : Site d) ∉ s(u, v))
    (hmem : s(u, v) ∈ hrHD_corridorEdges a (La + 1)) :
    v ∈ bc3_clusterNbhd ω a (La + 1) := by
  obtain ⟨p, hp, hpe⟩ := bc3_corridorEdge_structure hmem
  have hp1 : 1 ≤ p := by
    by_contra hlt
    have hp0 : p = 0 := by omega
    subst hp0
    apply hno0; rw [hpe]; simp only [Nat.cast_zero, hrHD_rayPt_zero]; exact Sym2.mem_mk_left _ _
  have hvmem : v ∈ s(hrHD_rayPt a (p : ℤ), hrHD_rayPt a ((p : ℤ) + 1)) := by
    rw [← hpe]; exact Sym2.mem_mk_right _ _
  rw [Sym2.mem_iff] at hvmem
  rcases hvmem with rfl | rfl
  · exact bc3_rayPt_mem_clusterNbhd hp1 (by omega)
  · have h : hrHD_rayPt a ((p : ℤ) + 1) = hrHD_rayPt a ((p + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h]; exact bc3_rayPt_mem_clusterNbhd (by omega) (by omega)


lemma bc3_crossAxis_step_absurd (ω : ConfigSpace (Sym2 (Site d))) (a c : Fin d) (La Lc : ℕ)
    (hcross : bc3_CrossDisjoint ω a c (La + 1) (Lc + 1))
    {u v : Site d} (hno0 : (0 : Site d) ∉ s(u, v))
    (hu : u ∈ bc3_clusterNbhd ω a (La + 1))
    (hmem : s(u, v) ∈ hrHD_corridorEdges c (Lc + 1)) : False := by
  obtain ⟨p, hp, hpe⟩ := bc3_corridorEdge_structure hmem
  have hp1 : 1 ≤ p := by
    by_contra hlt
    have hp0 : p = 0 := by omega
    subst hp0
    apply hno0; rw [hpe]; simp only [Nat.cast_zero, hrHD_rayPt_zero]; exact Sym2.mem_mk_left _ _
  have humem : u ∈ s(hrHD_rayPt c (p : ℤ), hrHD_rayPt c ((p : ℤ) + 1)) := by
    rw [← hpe]; exact Sym2.mem_mk_left _ _
  rw [Sym2.mem_iff] at humem
  rcases humem with rfl | rfl
  · exact hcross p hp1 (by omega) hu
  · have h : hrHD_rayPt c ((p : ℤ) + 1) = hrHD_rayPt c ((p + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h] at hu
    exact hcross (p + 1) (by omega) (by omega) hu


lemma bc3_clusterNbhd_adjClosed_gen (ω : ConfigSpace (Sym2 (Site d)))
    (a c₁ c₂ : Fin d) (La Lc₁ Lc₂ : ℕ)
    (hcross1 : bc3_CrossDisjoint ω a c₁ (La + 1) (Lc₁ + 1))
    (hcross2 : bc3_CrossDisjoint ω a c₂ (La + 1) (Lc₂ + 1)) :
    bc3_AdjClosed (removeSite 0 (forceOpenFinset
        (hrHD_corridorEdges a (La + 1) ∪ hrHD_corridorEdges c₁ (Lc₁ + 1) ∪
          hrHD_corridorEdges c₂ (Lc₂ + 1)) ω))
      (bc3_clusterNbhd ω a (La + 1)) := by
  set G : Finset (Sym2 (Site d)) := hrHD_corridorEdges a (La + 1) ∪
    hrHD_corridorEdges c₁ (Lc₁ + 1) ∪ hrHD_corridorEdges c₂ (Lc₂ + 1) with hGdef
  intro u v hu hadj
  have hopen : removeSite 0 (forceOpenFinset G ω) s(u, v) = true := hadj.2
  obtain ⟨hno0, hcase⟩ := bc3_rhoEdge_cases ω G hopen
  rcases hcase with hωopen | hGmem
  · 
    rw [bc3_mem_clusterNbhd] at hu ⊢
    obtain ⟨t, ht, hut⟩ := hu
    refine ⟨t, ht, ?_⟩
    have hrm0 : removeSite (0 : Site d) ω s(u, v) = true := by
      rw [removeSite_apply_of_notMem hno0]; exact hωopen
    have huv : IsOpenEdge d (removeSite 0 ω) u v := ⟨hadj.1, hrm0⟩
    rw [mem_cluster] at hut ⊢
    exact hut.trans huv.connected
  · 
    rw [hGdef, Finset.mem_union, Finset.mem_union] at hGmem
    rcases hGmem with (ha | h1) | h2
    · exact bc3_sameAxis_step_mem ω a La hno0 ha
    · exact absurd (bc3_crossAxis_step_absurd ω a c₁ La Lc₁ hcross1 hno0 hu h1) (by simp)
    · exact absurd (bc3_crossAxis_step_absurd ω a c₂ La Lc₂ hcross2 hno0 hu h2) (by simp)


lemma bc3_clusterNbhd_adjClosed (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ)
    (hcross2 : bc3_CrossDisjoint ω j₁ j₂ (L₁ + 1) (L₂ + 1))
    (hcross3 : bc3_CrossDisjoint ω j₁ j₃ (L₁ + 1) (L₃ + 1)) :
    bc3_AdjClosed (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
      (bc3_clusterNbhd ω j₁ (L₁ + 1)) := by
  have h := bc3_clusterNbhd_adjClosed_gen ω j₁ j₂ j₃ L₁ L₂ L₃ hcross2 hcross3
  rwa [bc3_corridorUnion]


lemma bc3_corridorUnion_perm2 (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) :
    bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃ =
      hrHD_corridorEdges j₂ (L₂ + 1) ∪ hrHD_corridorEdges j₁ (L₁ + 1) ∪
        hrHD_corridorEdges j₃ (L₃ + 1) := by
  rw [bc3_corridorUnion]; ext e; simp only [Finset.mem_union]; tauto


lemma bc3_corridorUnion_perm3 (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ) :
    bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃ =
      hrHD_corridorEdges j₃ (L₃ + 1) ∪ hrHD_corridorEdges j₁ (L₁ + 1) ∪
        hrHD_corridorEdges j₂ (L₂ + 1) := by
  rw [bc3_corridorUnion]; ext e; simp only [Finset.mem_union]; tauto


lemma bc3_mouth_separated_of_cross (ω : ConfigSpace (Sym2 (Site d)))
    (j₁ j₂ j₃ : Fin d) (L₁ L₂ L₃ : ℕ)
    (hcross2 : bc3_CrossDisjoint ω j₁ j₂ (L₁ + 1) (L₂ + 1))
    (hcross3 : bc3_CrossDisjoint ω j₁ j₃ (L₁ + 1) (L₃ + 1))
    (q : Site d) (hq : q ∉ bc3_clusterNbhd ω j₁ (L₁ + 1)) :
    ¬ Connected d (removeSite 0 (forceOpenFinset (bc3_corridorUnion j₁ j₂ j₃ L₁ L₂ L₃) ω))
        (hrHD_rayPt j₁ 1) q :=
  bc3_barrier_blocks _ (bc3_clusterNbhd ω j₁ (L₁ + 1)) (hrHD_rayPt j₁ 1) q
    (bc3_clusterNbhd_adjClosed ω j₁ j₂ j₃ L₁ L₂ L₃ hcross2 hcross3)
    (bc3_mouth_mem_clusterNbhd (Nat.succ_pos L₁)) hq


end Walls
end StatMech
