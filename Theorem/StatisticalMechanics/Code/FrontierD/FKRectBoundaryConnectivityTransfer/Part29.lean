/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part31
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectCoordinateSeamEdge_eq_map
    {W : Nat} (hW : 0 < W) (n : Nat) (a : Bool × Fin W) :
    fkRectCoordinateSeamEdge (n := n) hW a =
      Sym2.map (fkRectStripVertexEquiv W n)
        s(fkRectStripBoundary n (fkRectBoundarySeamEdgeEndpoints hW a).1,
          fkRectStripBoundary n
            (fkRectBoundarySeamEdgeEndpoints hW a).2) := by
  rw [Sym2.map_pair_eq]
  rcases a with ⟨dir, x⟩
  cases dir <;> simp [fkRectCoordinateSeamEdge,
    fkRectBoundarySeamEdgeEndpoints]

theorem fkRectStripSeamGraph_adj_iff
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
    (eta : Bool × Fin W -> Bool) (u v : FKRectStripVertex W n) :
    (fkRectStripSeamGraph hW n layers eta).Adj u v ↔
      (fkRectStripGraph hW n layers).Adj u v ∨
      ∃ a : Bool × Fin W, eta a = true ∧
        (SimpleGraph.edge
          (fkRectStripBoundary n
            (fkRectBoundarySeamEdgeEndpoints hW a).1)
          (fkRectStripBoundary n
            (fkRectBoundarySeamEdgeEndpoints hW a).2)).Adj u v := by
  rw [fkRectStripSeamGraph, finiteBoundaryEdgeRun_adj_iff]
  unfold fkRectBoundaryOpenSeamEdges fkRectBoundaryOpenLayerIndices
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_univ, true_and]
  aesop

theorem fkRectStripSeamGraph_adj_iff_coordinateEdge
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
    (eta : Bool × Fin W -> Bool) (u v : FKRectStripVertex W n) :
    (fkRectStripSeamGraph hW n layers eta).Adj u v ↔
      u ≠ v ∧
        ((∃ i : Fin n, ∃ a : Bool × Fin W,
          (layers i).2 a = true ∧
            fkRectCoordinateLayerEdge hW i (layers i).1 a =
              s(fkRectStripVertexEquiv W n u,
                fkRectStripVertexEquiv W n v)) ∨
        ∃ a : Bool × Fin W, eta a = true ∧
          fkRectCoordinateSeamEdge (n := n) hW a =
            s(fkRectStripVertexEquiv W n u,
              fkRectStripVertexEquiv W n v)) := by
  rw [fkRectStripSeamGraph_adj_iff,
    fkRectStripGraph_adj_iff_coordinateEdge]
  constructor
  · rintro (⟨hne, hnonSeam⟩ | ⟨a, hopen, hedge⟩)
    · exact ⟨hne, Or.inl hnonSeam⟩
    · have hedge' := (SimpleGraph.adj_edge _ _).1 hedge
      refine ⟨hedge'.2, Or.inr ⟨a, hopen, ?_⟩⟩
      rw [fkRectCoordinateSeamEdge_eq_map]
      simpa only [Sym2.map_pair_eq] using
        congrArg (Sym2.map (fkRectStripVertexEquiv W n)) hedge'.1
  · rintro ⟨hne, hnonSeam | ⟨a, hopen, hcoord⟩⟩
    · exact Or.inl ⟨hne, hnonSeam⟩
    · refine Or.inr ⟨a, hopen, ?_⟩
      apply (SimpleGraph.adj_edge _ _).2
      refine ⟨?_, hne⟩
      rw [fkRectCoordinateSeamEdge_eq_map] at hcoord
      apply (sym2_map_eq_map_iff_of_injective
        (fkRectStripVertexEquiv W n)
        (fkRectStripVertexEquiv W n).injective _ _).1
      simpa only [Sym2.map_pair_eq] using hcoord

theorem fkRectStripSeamGraph_component_count
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
    (eta : Bool × Fin W -> Bool) :
    Nat.card (fkRectStripSeamGraph hW n layers eta).ConnectedComponent =
      fkRectStripClosedCount hW n layers +
        Nat.card (fkRectBoundarySeamGraph hW
          (fkRectStripState hW n layers) eta).ConnectedComponent := by
  have hcross := finiteBoundaryEdgeRun_component_cross_sum
    (fkRectStripBoundary n) (fkRectStripGraph hW n layers)
    (fkRectStripState hW n layers)
    (fun u v => fkRectStrip_boundary_reachable_iff hW n layers u v)
    (fkRectBoundaryOpenSeamEdges hW eta)
  have hstrip := fkRectStrip_component_count hW n layers
  have hseam := fkRectBoundarySeamGraph_eq_edgeRun hW
    (fkRectStripState hW n layers) eta
  have hstripSeam : finiteBoundaryEdgeRun (fkRectStripBoundary n)
      (fkRectStripGraph hW n layers) (fkRectBoundaryOpenSeamEdges hW eta) =
        fkRectStripSeamGraph hW n layers eta := rfl
  rw [← hseam, hstripSeam] at hcross
  have hcross' :
      (fkRectStripClosedCount hW n layers +
          Nat.card (fkRectStripState hW n layers).ConnectedComponent) +
        Nat.card (fkRectBoundarySeamGraph hW
          (fkRectStripState hW n layers) eta).ConnectedComponent =
      Nat.card (fkRectStripState hW n layers).ConnectedComponent +
        Nat.card (fkRectStripSeamGraph hW n layers eta).ConnectedComponent := by
    rw [← hstrip]
    exact hcross
  omega


end
end StatMech.FrontierD
