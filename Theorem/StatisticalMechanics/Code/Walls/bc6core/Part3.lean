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
import Def.StatisticalMechanics.Code.Walls.bc6core.Part2
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc6_corridorClustersDisjoint_of_armClosed {N : ℕ} {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃)
    {ω : ConfigSpace (Sym2 (Site d))}
    (h : bc6_CorridorArmsDisjoint N j₁ j₂ j₃ ω) :
    bc3_CorridorClustersDisjoint
      (bc6_closeBoxExcept N (bc3_corridorUnion j₁ j₂ j₃ N N N) ω) j₁ j₂ j₃ N N N := by
  obtain ⟨⟨ha1, ha2, ha3⟩, hf12, hf13, hf21, hf23, hf31, hf32⟩ := h
  set G := bc3_corridorUnion j₁ j₂ j₃ N N N with hG
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · 
    exact bc6_crossDisjoint_of_armClosed (c₂ := j₃) hj12 hj13 G
      (by rw [hG, bc6_wiring_perm1]) ha1 hf12
  · 
    exact bc6_crossDisjoint_of_armClosed (c₂ := j₂) hj13 hj12 G
      (by rw [hG]; ext e; simp only [bc3_corridorUnion, Finset.mem_union]; tauto) ha1 hf13
  · 
    exact bc6_crossDisjoint_of_armClosed (c₂ := j₃) (Ne.symm hj12) hj23 G
      (by rw [hG, bc6_wiring_perm2]) ha2 hf21
  · 
    exact bc6_crossDisjoint_of_armClosed (c₂ := j₁) hj23 (Ne.symm hj12) G
      (by rw [hG]; ext e; simp only [bc3_corridorUnion, Finset.mem_union]; tauto) ha2 hf23
  · 
    exact bc6_crossDisjoint_of_armClosed (c₂ := j₂) (Ne.symm hj13) (Ne.symm hj23) G
      (by rw [hG, bc6_wiring_perm3]) ha3 hf31
  · 
    exact bc6_crossDisjoint_of_armClosed (c₂ := j₁) (Ne.symm hj23) (Ne.symm hj13) G
      (by rw [hG]; ext e; simp only [bc3_corridorUnion, Finset.mem_union]; tauto) ha3 hf32


theorem bc6_pairwiseSeparated_of_armClosed {N : ℕ} {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃)
    {ω : ConfigSpace (Sym2 (Site d))}
    (h : bc6_CorridorArmsDisjoint N j₁ j₂ j₃ ω) :
    bc2_PairwiseSeparated
      (bc6_closeBoxExcept N (bc3_corridorUnion j₁ j₂ j₃ N N N) ω) j₁ j₂ j₃ N N N :=
  bc3_pairwiseSeparated_of_corridorClustersDisjoint _ j₁ j₂ j₃ N N N
    (bc6_corridorClustersDisjoint_of_armClosed hj12 hj13 hj23 h)


lemma bc6_bot_no_adj {S : Set (Site d)} (x y : S) :
    ¬ (openSubgraphInduce d (removeSite 0 (⊥ : ConfigSpace (Sym2 (Site d)))) S).Adj x y := by
  intro hadj
  rw [openSubgraphInduce_adj, openSubgraph_adj] at hadj
  have hval := hadj.2
  by_cases h0 : (0 : Site d) ∈ s((x : Site d), (y : Site d))
  · rw [removeSite_apply_of_mem h0] at hval; exact Bool.false_ne_true hval
  · rw [removeSite_apply_of_notMem h0] at hval; exact Bool.false_ne_true hval


lemma bc6_bot_walk_eq {S : Set (Site d)} {x y : S}
    (w : (openSubgraphInduce d (removeSite 0 (⊥ : ConfigSpace (Sym2 (Site d)))) S).Walk x y) :
    x = y := by
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (bc6_bot_no_adj _ _)


lemma bc6_offBoxCluster_bot_eq {N : ℕ} {a : Fin d} {R : ℕ} {x : Site d}
    (hx : x ∈ bc6_offBoxCluster N a R (⊥ : ConfigSpace (Sym2 (Site d)))) :
    x = hrHD_rayPt a (R : ℤ) := by
  obtain ⟨_hxS, _hoS, hconn⟩ := hx
  obtain ⟨w⟩ := hconn
  exact congrArg Subtype.val (bc6_bot_walk_eq w).symm


theorem bc6_armClosed_bot {N : ℕ} {a c₁ c₂ : Fin d} (hac1 : a ≠ c₁) (hac2 : a ≠ c₂)
    {Lc₁ Lc₂ : ℕ} (G : Finset (Sym2 (Site d)))
    (hGdef : G = hrHD_corridorEdges a (N + 1) ∪ hrHD_corridorEdges c₁ (Lc₁ + 1) ∪
        hrHD_corridorEdges c₂ (Lc₂ + 1)) :
    bc6_ArmClosed N a (N + 1) G (⊥ : ConfigSpace (Sym2 (Site d))) := by
  intro u v hu hopen
  have hueq : u = hrHD_rayPt a ((N + 1 : ℕ) : ℤ) := bc6_offBoxCluster_bot_eq hu
  obtain ⟨_hadjlat, hno0, hcase⟩ := bc6_edgedichotomy (⊥ : ConfigSpace (Sym2 (Site d))) N G hopen
  rcases hcase with hGmem | ⟨hωopen, _⟩
  · rw [hGdef, Finset.mem_union, Finset.mem_union] at hGmem
    right
    rcases hGmem with (ha | h1) | h2
    · obtain ⟨p, _hp, hpe⟩ := bc6_corridorEdge_structure ha
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
      · have h : hrHD_rayPt a ((p : ℤ) + 1) = hrHD_rayPt a ((p + 1 : ℕ) : ℤ) := by push_cast; ring
        rw [h]; exact bc6_rayPt_mem_rayInterior (by omega) (by omega)
    · exfalso
      refine bc6_rayPt_notMem_crossCorridor (Ne.symm hac1)
        (q := ((N + 1 : ℕ) : ℤ)) (by exact_mod_cast (by omega : ((N + 1 : ℕ) : ℤ) ≠ 0)) h1 ?_
      rw [← hueq]; exact Sym2.mem_mk_left _ _
    · exfalso
      refine bc6_rayPt_notMem_crossCorridor (Ne.symm hac2)
        (q := ((N + 1 : ℕ) : ℤ)) (by exact_mod_cast (by omega : ((N + 1 : ℕ) : ℤ) ≠ 0)) h2 ?_
      rw [← hueq]; exact Sym2.mem_mk_left _ _
  · exact absurd hωopen (by simp)


theorem bc6_crossFarEnd_bot {N : ℕ} {a c : Fin d} (hac : a ≠ c) :
    (hrHD_rayPt c ((N + 1 : ℕ) : ℤ)) ∉
      bc6_offBoxCluster N a (N + 1) (⊥ : ConfigSpace (Sym2 (Site d))) := by
  intro hmem
  have heq : (hrHD_rayPt c ((N + 1 : ℕ) : ℤ)) = hrHD_rayPt a ((N + 1 : ℕ) : ℤ) :=
    bc6_offBoxCluster_bot_eq hmem
  exact hrHD_rayPt_disjoint_of_ne (Ne.symm hac)
    (by exact_mod_cast (by omega : ((N + 1 : ℕ) : ℤ) ≠ 0)) heq


theorem bc6_corridorArmsDisjoint_bot {N : ℕ} {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃) :
    bc6_CorridorArmsDisjoint N j₁ j₂ j₃ (⊥ : ConfigSpace (Sym2 (Site d))) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bc6_armClosed_bot hj12 hj13 _ (bc6_wiring_perm1 j₁ j₂ j₃ N)
  · exact bc6_armClosed_bot (Ne.symm hj12) hj23 _ (bc6_wiring_perm2 j₁ j₂ j₃ N)
  · exact bc6_armClosed_bot (Ne.symm hj13) (Ne.symm hj23) _ (bc6_wiring_perm3 j₁ j₂ j₃ N)
  · exact bc6_crossFarEnd_bot hj12
  · exact bc6_crossFarEnd_bot hj13
  · exact bc6_crossFarEnd_bot (Ne.symm hj12)
  · exact bc6_crossFarEnd_bot hj23
  · exact bc6_crossFarEnd_bot (Ne.symm hj13)
  · exact bc6_crossFarEnd_bot (Ne.symm hj23)


theorem bc6_corridorClustersDisjoint_closeBox_bot {N : ℕ} {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃) :
    bc3_CorridorClustersDisjoint
      (bc6_closeBoxExcept N (bc3_corridorUnion j₁ j₂ j₃ N N N)
        (⊥ : ConfigSpace (Sym2 (Site d)))) j₁ j₂ j₃ N N N :=
  bc6_corridorClustersDisjoint_of_armClosed hj12 hj13 hj23
    (bc6_corridorArmsDisjoint_bot hj12 hj13 hj23)


theorem bc6_pairwiseSeparated_closeBox_bot {N : ℕ} {j₁ j₂ j₃ : Fin d}
    (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃) :
    bc2_PairwiseSeparated
      (bc6_closeBoxExcept N (bc3_corridorUnion j₁ j₂ j₃ N N N)
        (⊥ : ConfigSpace (Sym2 (Site d)))) j₁ j₂ j₃ N N N :=
  bc6_pairwiseSeparated_of_armClosed hj12 hj13 hj23
    (bc6_corridorArmsDisjoint_bot hj12 hj13 hj23)

end Walls
end StatMech
