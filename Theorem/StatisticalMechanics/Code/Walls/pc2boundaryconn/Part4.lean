/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc2boundaryconn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Def.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem pc2_bdEdge_trom {p q : Site 2} (hp : p ∈ (↑pc2_tromino : Set (Site 2)))
    (hq : q ∉ (↑pc2_tromino : Set (Site 2))) : bdEdge (↑pc2_tromino : Set (Site 2)) s(p, q) := by
  rw [bdEdge_mk]; exact ⟨fun _ => hq, fun _ => hp⟩


theorem pc2_trom_adj_1 :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(-1:ℤ), -1] ![(0:ℤ), -1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨?_, ?_⟩
  · have := latAdj_right (-1) (-1); rwa [show (-1:ℤ) + 1 = 0 from by ring] at this
  · have h := sharedPrimalEdge_right (-1) (-1)
    rw [show (-1:ℤ) + 1 = 0 from by ring] at h
    rw [h]; unfold faceCorner10 faceCorner11; rw [show (-1:ℤ) + 1 = 0 from by ring]
    
    rw [show s((![(0:ℤ), -1] : Site 2), (![(0:ℤ), 0] : Site 2))
      = s((![(0:ℤ), 0] : Site 2), (![(0:ℤ), -1] : Site 2)) from Sym2.eq_swap]
    exact pc2_bdEdge_trom ((pc2_mem_tromino _ _).mpr (by tauto))
      (fun hmem => by rw [pc2_mem_tromino] at hmem; omega)


theorem pc2_trom_adj_2 :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(0:ℤ), -1] ![(1:ℤ), -1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨?_, ?_⟩
  · have := latAdj_right (0) (-1); rwa [show (0:ℤ) + 1 = 1 from by ring] at this
  · have h := sharedPrimalEdge_right (0) (-1)
    rw [show (0:ℤ) + 1 = 1 from by ring] at h
    rw [h]; unfold faceCorner10 faceCorner11; rw [show (0:ℤ) + 1 = 1 from by ring,
      show (-1:ℤ) + 1 = 0 from by ring]
    rw [show s((![(1:ℤ), -1] : Site 2), (![(1:ℤ), 0] : Site 2))
      = s((![(1:ℤ), 0] : Site 2), (![(1:ℤ), -1] : Site 2)) from Sym2.eq_swap]
    exact pc2_bdEdge_trom ((pc2_mem_tromino _ _).mpr (by tauto))
      (fun hmem => by rw [pc2_mem_tromino] at hmem; omega)


theorem pc2_trom_adj_3 :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(1:ℤ), -1] ![(1:ℤ), 0] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨?_, ?_⟩
  · have := latAdj_top (1) (-1); rwa [show (-1:ℤ) + 1 = 0 from by ring] at this
  · have h := sharedPrimalEdge_top (1) (-1)
    rw [show (-1:ℤ) + 1 = 0 from by ring] at h
    rw [h]; unfold faceCorner01 faceCorner11; rw [show (-1:ℤ) + 1 = 0 from by ring,
      show (1:ℤ) + 1 = 2 from by ring]
    exact pc2_bdEdge_trom ((pc2_mem_tromino _ _).mpr (by tauto))
      (fun hmem => by rw [pc2_mem_tromino] at hmem; omega)


theorem pc2_trom_adj_4 :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(1:ℤ), 0] ![(0:ℤ), 0] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨?_, ?_⟩
  · have := latAdj_left (1) (0); rwa [show (1:ℤ) - 1 = 0 from by ring] at this
  · have h := sharedPrimalEdge_left (1) (0)
    rw [show (1:ℤ) - 1 = 0 from by ring] at h
    rw [h]; unfold faceCorner00 faceCorner01; rw [show (0:ℤ) + 1 = 1 from by ring]
    exact pc2_bdEdge_trom ((pc2_mem_tromino _ _).mpr (by tauto))
      (fun hmem => by rw [pc2_mem_tromino] at hmem; omega)


theorem pc2_trom_adj_5 :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(0:ℤ), 0] ![(0:ℤ), 1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨?_, ?_⟩
  · have := latAdj_top (0) (0); rwa [show (0:ℤ) + 1 = 1 from by ring] at this
  · have h := sharedPrimalEdge_top (0) (0)
    rw [show (0:ℤ) + 1 = 1 from by ring] at h
    rw [h]; unfold faceCorner01 faceCorner11; rw [show (0:ℤ) + 1 = 1 from by ring]
    exact pc2_bdEdge_trom ((pc2_mem_tromino _ _).mpr (by tauto))
      (fun hmem => by rw [pc2_mem_tromino] at hmem; omega)


theorem pc2_trom_adj_6 :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(0:ℤ), 1] ![(-1:ℤ), 1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨?_, ?_⟩
  · have := latAdj_left (0) (1); rwa [show (0:ℤ) - 1 = -1 from by ring] at this
  · have h := sharedPrimalEdge_left (0) (1)
    rw [show (0:ℤ) - 1 = -1 from by ring] at h
    rw [h]; unfold faceCorner00 faceCorner01; rw [show (1:ℤ) + 1 = 2 from by ring]
    exact pc2_bdEdge_trom ((pc2_mem_tromino _ _).mpr (by tauto))
      (fun hmem => by rw [pc2_mem_tromino] at hmem; omega)


theorem pc2_trom_adj_7 :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(-1:ℤ), 1] ![(-1:ℤ), 0] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨?_, ?_⟩
  · have := latAdj_bottom (-1) (1); rwa [show (1:ℤ) - 1 = 0 from by ring] at this
  · have h := sharedPrimalEdge_bottom (-1) (1)
    rw [show (1:ℤ) - 1 = 0 from by ring] at h
    rw [h]; unfold faceCorner00 faceCorner10; rw [show (-1:ℤ) + 1 = 0 from by ring]
    
    rw [show s((![(-1:ℤ), 1] : Site 2), (![(0:ℤ), 1] : Site 2))
      = s((![(0:ℤ), 1] : Site 2), (![(-1:ℤ), 1] : Site 2)) from Sym2.eq_swap]
    exact pc2_bdEdge_trom ((pc2_mem_tromino _ _).mpr (by tauto))
      (fun hmem => by rw [pc2_mem_tromino] at hmem; omega)


theorem pc2_trom_adj_8 :
    (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Adj ![(-1:ℤ), 0] ![(-1:ℤ), -1] := by
  rw [faceBoundaryGraph_adj]
  refine ⟨?_, ?_⟩
  · have := latAdj_bottom (-1) (0); rwa [show (0:ℤ) - 1 = -1 from by ring] at this
  · have h := sharedPrimalEdge_bottom (-1) (0)
    rw [show (0:ℤ) - 1 = -1 from by ring] at h
    rw [h]; unfold faceCorner00 faceCorner10; rw [show (-1:ℤ) + 1 = 0 from by ring]
    
    rw [show s((![(-1:ℤ), 0] : Site 2), (![(0:ℤ), 0] : Site 2))
      = s((![(0:ℤ), 0] : Site 2), (![(-1:ℤ), 0] : Site 2)) from Sym2.eq_swap]
    exact pc2_bdEdge_trom ((pc2_mem_tromino _ _).mpr (by tauto))
      (fun hmem => by rw [pc2_mem_tromino] at hmem; omega)


theorem pc2_mem_tromFrame_corner : (![(-1:ℤ), -1] : Site 2) ∈ pc2_tromFrame := by
  unfold pc2_tromFrame; simp


theorem pc2_tromFrame_cases {v : Site 2} (hv : v ∈ pc2_tromFrame) :
    v = ![(-1:ℤ), -1] ∨ v = ![(0:ℤ), -1] ∨ v = ![(1:ℤ), -1] ∨ v = ![(1:ℤ), 0] ∨
      v = ![(0:ℤ), 0] ∨ v = ![(0:ℤ), 1] ∨ v = ![(-1:ℤ), 1] ∨ v = ![(-1:ℤ), 0] := by
  unfold pc2_tromFrame at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  tauto


theorem pc2_tromFrame_walk_from_corner {v : Site 2} (hv : v ∈ pc2_tromFrame) :
    ∃ p : (faceBoundaryGraph (↑pc2_tromino : Set (Site 2))).Walk ![(-1:ℤ), -1] v,
      ∀ w ∈ p.support, w ∈ pc2_tromFrame := by
  have mc : (![(-1:ℤ), -1] : Site 2) ∈ pc2_tromFrame := pc2_mem_tromFrame_corner
  have m1 : (![(0:ℤ), -1] : Site 2) ∈ pc2_tromFrame := by unfold pc2_tromFrame; simp
  have m2 : (![(1:ℤ), -1] : Site 2) ∈ pc2_tromFrame := by unfold pc2_tromFrame; simp
  have m3 : (![(1:ℤ), 0] : Site 2) ∈ pc2_tromFrame := by unfold pc2_tromFrame; simp
  have m4 : (![(0:ℤ), 0] : Site 2) ∈ pc2_tromFrame := by unfold pc2_tromFrame; simp
  have m5 : (![(0:ℤ), 1] : Site 2) ∈ pc2_tromFrame := by unfold pc2_tromFrame; simp
  have m6 : (![(-1:ℤ), 1] : Site 2) ∈ pc2_tromFrame := by unfold pc2_tromFrame; simp
  have m7 : (![(-1:ℤ), 0] : Site 2) ∈ pc2_tromFrame := by unfold pc2_tromFrame; simp
  
  rcases pc2_tromFrame_cases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨SimpleGraph.Walk.nil, ?_⟩
    intro w hw
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw; rw [hw]; exact mc
  · refine ⟨SimpleGraph.Walk.cons pc2_trom_adj_1 SimpleGraph.Walk.nil, ?_⟩
    intro w hw; simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl; exacts [mc, m1]
  · refine ⟨SimpleGraph.Walk.cons pc2_trom_adj_1
      (SimpleGraph.Walk.cons pc2_trom_adj_2 SimpleGraph.Walk.nil), ?_⟩
    intro w hw; simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl; exacts [mc, m1, m2]
  · refine ⟨SimpleGraph.Walk.cons pc2_trom_adj_1 (SimpleGraph.Walk.cons pc2_trom_adj_2
      (SimpleGraph.Walk.cons pc2_trom_adj_3 SimpleGraph.Walk.nil)), ?_⟩
    intro w hw; simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl; exacts [mc, m1, m2, m3]
  · refine ⟨SimpleGraph.Walk.cons pc2_trom_adj_1 (SimpleGraph.Walk.cons pc2_trom_adj_2
      (SimpleGraph.Walk.cons pc2_trom_adj_3 (SimpleGraph.Walk.cons pc2_trom_adj_4
        SimpleGraph.Walk.nil))), ?_⟩
    intro w hw; simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl; exacts [mc, m1, m2, m3, m4]
  · refine ⟨SimpleGraph.Walk.cons pc2_trom_adj_1 (SimpleGraph.Walk.cons pc2_trom_adj_2
      (SimpleGraph.Walk.cons pc2_trom_adj_3 (SimpleGraph.Walk.cons pc2_trom_adj_4
        (SimpleGraph.Walk.cons pc2_trom_adj_5 SimpleGraph.Walk.nil)))), ?_⟩
    intro w hw; simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl; exacts [mc, m1, m2, m3, m4, m5]
  · 
    refine ⟨SimpleGraph.Walk.cons pc2_trom_adj_8.symm
      (SimpleGraph.Walk.cons pc2_trom_adj_7.symm SimpleGraph.Walk.nil), ?_⟩
    intro w hw; simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl; exacts [mc, m7, m6]
  · 
    refine ⟨SimpleGraph.Walk.cons pc2_trom_adj_8.symm SimpleGraph.Walk.nil, ?_⟩
    intro w hw; simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl; exacts [mc, m7]


theorem pc2_tromino_faceBoundaryConnected :
    FaceBoundaryConnected (↑pc2_tromino : Set (Site 2)) pc2_tromFrame :=
  pc2_faceBoundaryConnected_of_anchor pc2_mem_tromFrame_corner
    (fun _ hf => pc2_tromFrame_walk_from_corner hf)


end Lattice
end StatMech
