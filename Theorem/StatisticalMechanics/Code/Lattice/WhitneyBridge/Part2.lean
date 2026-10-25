/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Def.StatisticalMechanics.Code.Lattice.WhitneyBridge
open SimpleGraph Set


namespace StatMech

namespace Lattice

@[simp] theorem whb_faceRegion_adj (G : SimpleGraph (Site 2)) (f g : Site 2) :
    (whb_faceRegion G).Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧ sharedPrimalEdge f g ∉ G.edgeSet := Iff.rfl


theorem whb_square_edge_mem {u v : Fin 4} (h : jbc_cyc4.Adj u v) :
    s(jbc_csq u, jbc_csq v) ∈ (imageGraph jbc_Pce).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, imageGraph_adj]
  exact ⟨u, v, h, rfl, rfl⟩


theorem whb_faceRegion_interior_isolated (g : Site 2) :
    ¬ (whb_faceRegion (imageGraph jbc_Pce)).Adj ![0, 0] g := by
  rintro ⟨hadj, hshared⟩
  apply hshared
  
  
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  have hg : g = ![g 0, g 1] := by funext i; fin_cases i <;> rfl
  
  have h00 : (![0, 0] : Site 2) 0 = 0 := rfl
  have h01 : (![0, 0] : Site 2) 1 = 0 := rfl
  rw [h00, h01] at hadj
  
  have : (g 0 = 1 ∧ g 1 = 0) ∨ (g 0 = -1 ∧ g 1 = 0) ∨
      (g 0 = 0 ∧ g 1 = 1) ∨ (g 0 = 0 ∧ g 1 = -1) := by omega
  rcases this with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [hg, hx, hy, show (![0, 0] : Site 2) = ![(0 : ℤ), 0] from rfl]
    rw [show (![1, 0] : Site 2) = ![(0 : ℤ) + 1, 0] by norm_num, sharedPrimalEdge_right]
    exact whb_square_edge_mem (u := 1) (v := 2) (by rw [jbc_cyc4_adj]; decide)
  · rw [hg, hx, hy, show (![0, 0] : Site 2) = ![(0 : ℤ), 0] from rfl]
    rw [show (![-1, 0] : Site 2) = ![(0 : ℤ) - 1, 0] by norm_num, sharedPrimalEdge_left]
    exact whb_square_edge_mem (u := 0) (v := 3) (by rw [jbc_cyc4_adj]; decide)
  · rw [hg, hx, hy, show (![0, 0] : Site 2) = ![(0 : ℤ), 0] from rfl]
    rw [show (![0, 1] : Site 2) = ![(0 : ℤ), 0 + 1] by norm_num, sharedPrimalEdge_top]
    exact whb_square_edge_mem (u := 3) (v := 2) (by rw [jbc_cyc4_adj]; decide)
  · rw [hg, hx, hy, show (![0, 0] : Site 2) = ![(0 : ℤ), 0] from rfl]
    rw [show (![0, -1] : Site 2) = ![(0 : ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
    exact whb_square_edge_mem (u := 0) (v := 1) (by rw [jbc_cyc4_adj]; decide)


theorem whb_faceRegion_interior_supp :
    ((whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![0, 0]).supp = {![0, 0]} := by
  ext x
  rw [ConnectedComponent.mem_supp_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    
    rw [ConnectedComponent.eq] at h
    obtain ⟨w⟩ := h.symm
    cases w with
    | nil => rfl
    | cons hadj _ => exact absurd hadj (whb_faceRegion_interior_isolated _)
  · rintro rfl; rfl


theorem whb_faceRegion_interior_bounded :
    ((whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![0, 0]).supp.Finite := by
  rw [whb_faceRegion_interior_supp]; exact Set.finite_singleton _


end Lattice
end StatMech
