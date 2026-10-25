/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc3_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc3_barrierblocks
import Theorem.StatisticalMechanics.Code.Walls.bc3_anchordecomp.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc6edgedichotomy
import Theorem.StatisticalMechanics.Code.Walls.bc6corridoraxisunique
import Theorem.StatisticalMechanics.Code.Walls.bc6raysetdef.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc6stepsameray
import Def.StatisticalMechanics.Code.Walls.bc6core
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


lemma bc6_armRegion_adjClosed {N : ℕ} {a c₁ c₂ : Fin d} (hac1 : a ≠ c₁) (hac2 : a ≠ c₂)
    {Lc₁ Lc₂ : ℕ} {ω : ConfigSpace (Sym2 (Site d))} (G : Finset (Sym2 (Site d)))
    (hGdef : G = hrHD_corridorEdges a (N + 1) ∪ hrHD_corridorEdges c₁ (Lc₁ + 1) ∪
        hrHD_corridorEdges c₂ (Lc₂ + 1))
    (harm : bc6_ArmClosed N a (N + 1) G ω) :
    bc3_AdjClosed (removeSite 0 (bc6_closeBoxExcept N G ω)) (bc6_armRegion N a (N + 1) ω) := by
  intro u v hu hadj
  have hopen : IsOpenEdge d (removeSite 0 (bc6_closeBoxExcept N G ω)) u v := hadj
  obtain ⟨hadjlat, hno0, hcase⟩ := bc6_edgedichotomy ω N G hopen
  rw [bc6_mem_armRegion] at hu ⊢
  rcases hu with hray | hoff
  · obtain ⟨s, ⟨hs1, _hsR⟩, hus⟩ := hray
    subst hus
    rcases hcase with hGmem | ⟨_hωopen, hnbox⟩
    · rw [hGdef, Finset.mem_union, Finset.mem_union] at hGmem
      rcases hGmem with (ha | h1) | h2
      · left
        obtain ⟨p, _hp, hpe⟩ := bc6_corridorEdge_structure ha
        have hp1 : 1 ≤ p := by
          by_contra hlt
          have hp0 : p = 0 := by omega
          subst hp0
          apply hno0; rw [hpe]; simp only [Nat.cast_zero, hrHD_rayPt_zero]
          exact Sym2.mem_mk_left _ _
        have hvmem : v ∈ s(hrHD_rayPt a (p : ℤ), hrHD_rayPt a ((p : ℤ) + 1)) := by
          rw [← hpe]; exact Sym2.mem_mk_right _ _
        rw [Sym2.mem_iff] at hvmem
        rcases hvmem with rfl | rfl
        · exact bc6_rayPt_mem_rayInterior hp1 (by omega)
        · have h : hrHD_rayPt a ((p : ℤ) + 1) = hrHD_rayPt a ((p + 1 : ℕ) : ℤ) := by
            push_cast; ring
          rw [h]; exact bc6_rayPt_mem_rayInterior (by omega) (by omega)
      · exfalso
        refine bc6_rayPt_notMem_crossCorridor (Ne.symm hac1)
          (q := (s : ℤ)) (by exact_mod_cast (by omega : (s : ℤ) ≠ 0)) h1 ?_
        exact Sym2.mem_mk_left _ _
      · exfalso
        refine bc6_rayPt_notMem_crossCorridor (Ne.symm hac2)
          (q := (s : ℤ)) (by exact_mod_cast (by omega : (s : ℤ) ≠ 0)) h2 ?_
        exact Sym2.mem_mk_left _ _
    · by_cases hsN : s ≤ N
      · have hubox : (hrHD_rayPt a (s : ℤ)) ∈ box d N := bc6_rayPt_mem_box hsN
        have hvbox : v ∉ box d N := by
          rcases bc6_endpoint_outside_box_of_not_boxEdge hadjlat hnbox with hb | hb
          · exact absurd hubox hb
          · exact hb
        obtain ⟨hsEq, hveq⟩ := bc6_rayPt_offBox_neighbor hs1 hsN hadjlat hvbox
        right
        have hvfar : v = hrHD_rayPt a (((N + 1 : ℕ) : ℤ)) := by
          rw [hveq, hsEq]; norm_cast
        rw [hvfar]
        exact bc6_farEnd_mem_offBoxCluster (by omega) ω
      · push Not at hsN
        have hsN1 : s = N + 1 := by omega
        have hufar : (hrHD_rayPt a (s : ℤ)) ∈ bc6_offBoxCluster N a (N + 1) ω := by
          subst hsN1
          have hfar := bc6_farEnd_mem_offBoxCluster (a := a) (N := N) (R := N + 1) (by omega) ω
          rw [show ((N + 1 : ℕ) : ℤ) = ((N : ℤ) + 1) from by push_cast; ring] at hfar
          exact hfar
        exact (harm _ v hufar hopen).symm
  · exact (harm u v hoff hopen).symm


lemma bc6_crossRayPt_notMem_armRegion {N : ℕ} {a c : Fin d} (hac : a ≠ c) {p : ℕ}
    (hp1 : 1 ≤ p) (hpR : p ≤ N + 1) (ω : ConfigSpace (Sym2 (Site d)))
    (hfar : (hrHD_rayPt c ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) ω) :
    (hrHD_rayPt c (p : ℤ)) ∉ bc6_armRegion N a (N + 1) ω := by
  rw [bc6_mem_armRegion]
  rintro (hray | hoff)
  · 
    rw [bc6_mem_rayInterior] at hray
    obtain ⟨q, ⟨_hq1, _hqR⟩, heq⟩ := hray
    exact hrHD_rayPt_disjoint_of_ne (Ne.symm hac)
      (by exact_mod_cast (by omega : (p : ℤ) ≠ 0)) heq
  · 
    by_cases hpN : p ≤ N
    · have : (hrHD_rayPt c (p : ℤ)) ∉ box d N := bc6_mem_offBoxCluster_offBox hoff
      exact this (bc6_rayPt_mem_box hpN)
    · have hpEq : p = N + 1 := by omega
      apply hfar
      rwa [hpEq] at hoff


theorem bc6_crossDisjoint_of_armClosed {N : ℕ} {a c₁ c₂ : Fin d}
    (hac1 : a ≠ c₁) (hac2 : a ≠ c₂) {Lc₂ : ℕ} {ω : ConfigSpace (Sym2 (Site d))}
    (G : Finset (Sym2 (Site d)))
    (hGdef : G = hrHD_corridorEdges a (N + 1) ∪ hrHD_corridorEdges c₁ (N + 1) ∪
        hrHD_corridorEdges c₂ (Lc₂ + 1))
    (harm : bc6_ArmClosed N a (N + 1) G ω)
    (hfar : (hrHD_rayPt c₁ ((N + 1 : ℕ) : ℤ)) ∉ bc6_offBoxCluster N a (N + 1) ω) :
    bc3_CrossDisjoint (bc6_closeBoxExcept N G ω) a c₁ (N + 1) (N + 1) := by
  have hclosed := bc6_armRegion_adjClosed (Lc₁ := N) hac1 hac2 G hGdef harm
  intro p hp1 hpR hmem
  rw [bc3_mem_clusterNbhd] at hmem
  obtain ⟨t, ⟨ht1, htR⟩, hconn⟩ := hmem
  rw [mem_cluster] at hconn
  have hta : (hrHD_rayPt a (t : ℤ)) ∈ bc6_armRegion N a (N + 1) ω :=
    bc6_rayInterior_subset_armRegion (bc6_rayPt_mem_rayInterior ht1 htR)
  have hpc : (hrHD_rayPt c₁ (p : ℤ)) ∉ bc6_armRegion N a (N + 1) ω :=
    bc6_crossRayPt_notMem_armRegion hac1 hp1 hpR ω hfar
  exact bc3_barrier_blocks _ (bc6_armRegion N a (N + 1) ω) _ _ hclosed hta hpc hconn


lemma bc6_wiring_perm1 (j₁ j₂ j₃ : Fin d) (N : ℕ) :
    bc3_corridorUnion j₁ j₂ j₃ N N N =
      hrHD_corridorEdges j₁ (N + 1) ∪ hrHD_corridorEdges j₂ (N + 1) ∪
        hrHD_corridorEdges j₃ (N + 1) := by
  rw [bc3_corridorUnion]


lemma bc6_wiring_perm2 (j₁ j₂ j₃ : Fin d) (N : ℕ) :
    bc3_corridorUnion j₁ j₂ j₃ N N N =
      hrHD_corridorEdges j₂ (N + 1) ∪ hrHD_corridorEdges j₁ (N + 1) ∪
        hrHD_corridorEdges j₃ (N + 1) := by
  rw [bc3_corridorUnion]; ext e; simp only [Finset.mem_union]; tauto


lemma bc6_wiring_perm3 (j₁ j₂ j₃ : Fin d) (N : ℕ) :
    bc3_corridorUnion j₁ j₂ j₃ N N N =
      hrHD_corridorEdges j₃ (N + 1) ∪ hrHD_corridorEdges j₁ (N + 1) ∪
        hrHD_corridorEdges j₂ (N + 1) := by
  rw [bc3_corridorUnion]; ext e; simp only [Finset.mem_union]; tauto


end Walls
end StatMech
