/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsAnchorEncode.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsEulerParity
import Def.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part5
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch)

attribute [local instance] Classical.propDecidable


theorem circuit_image_eq_crossEdges {K : Finset (Site 2)} {n : ℕ}
    (hKbox : (↑K : Set (Site 2)) ⊆ box 2 n) {u : Site 2}
    (c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk u u)
    (hcov : ∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet, e ∈ c.edges) :
    Finset.image symPrimalSym c.edges.toFinset
      = crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) := by
  classical
  apply Finset.ext
  intro pe
  rw [Finset.mem_image, ← Finset.mem_coe, coe_crossEdges_eq_boundaryEdgeSet hKbox]
  constructor
  · rintro ⟨de, hde, rfl⟩
    rw [List.mem_toFinset] at hde
    exact symPrimalSym_mem_boundaryEdgeSet (c.edges_subset_edgeSet hde)
  · intro hpe
    obtain ⟨hedgemem, hsps⟩ := flankFacesSym_mem_edgeSet hpe
    exact ⟨flankFacesSym pe, by rw [List.mem_toFinset]; exact hcov _ hedgemem, hsps⟩


theorem circuit_decode_eq_contour {K : Finset (Site 2)} {n : ℕ}
    (hKbox : (↑K : Set (Site 2)) ⊆ box 2 n) {u : Site 2}
    (c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk u u)
    (hcov : ∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet, e ∈ c.edges) :
    dualWalkContour ⟨u, c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2)))⟩
      = crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) := by
  classical
  unfold dualWalkContour
  simp only
  rw [(c.edges_mapLe_eq_edges (faceBoundaryGraph_le (↑K : Set (Site 2))))]
  rw [show (c.edges.map symPrimalSym).toFinset = Finset.image symPrimalSym c.edges.toFinset by
    ext x; simp [List.mem_toFinset, List.mem_map]]
  exact circuit_image_eq_crossEdges hKbox c hcov


theorem circuit_length_eq_contourLen {K : Finset (Site 2)} {n : ℕ}
    (hKbox : (↑K : Set (Site 2)) ⊆ box 2 n) {u : Site 2}
    (c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk u u) (htrail : c.IsTrail)
    (hcov : ∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet, e ∈ c.edges) :
    (c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2)))).length
      = contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) := by
  classical
  
  have hml : (c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2)))).length = c.length := by
    unfold SimpleGraph.Walk.mapLe
    exact SimpleGraph.Walk.length_map (Hom.ofLE _) c
  rw [hml]
  
  rw [← SimpleGraph.Walk.length_edges, ← List.toFinset_card_of_nodup htrail.edges_nodup]
  
  rw [StatMech.Ising.contourLen, ← circuit_image_eq_crossEdges hKbox c hcov]
  symm
  apply Finset.card_image_of_injOn
  
  refine (symPrimalSym_injOn_edges (↑K : Set (Site 2))).mono ?_
  intro e he
  rw [Finset.mem_coe, List.mem_toFinset] at he
  exact c.edges_subset_edgeSet he


end Lattice
end StatMech
