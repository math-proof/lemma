/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Def.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part3
open SimpleGraph Set


namespace StatMech.Lattice

attribute [instance] PlanarZ2Subgraph.finV PlanarZ2Subgraph.decV


theorem mem_box_compl_of_exterior {R : ℕ} {a : Site 2} (h : a ∈ exterior 2 R) :
    a ∉ box 2 R := by
  rw [mem_exterior] at h
  rw [mem_box]; push Not
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by omega⟩


theorem rot90Inv_mem_box (R : ℕ) {x : Site 2} (hx : x ∈ box 2 R) :
    rot90Inv x ∈ box 2 R := by
  intro i; fin_cases i
  · have h : (rot90Inv x) 0 = x 1 := by simp [rot90Inv]
    show ((rot90Inv x) 0).natAbs ≤ R; rw [h]; exact hx 1
  · have h : (rot90Inv x) 1 = - x 0 := by simp [rot90Inv]
    show ((rot90Inv x) 1).natAbs ≤ R; rw [h, Int.natAbs_neg]; exact hx 0


theorem rot90Fun_mem_box (R : ℕ) {x : Site 2} (hx : x ∈ box 2 R) :
    rot90Fun x ∈ box 2 R := by
  intro i; fin_cases i
  · have h : (rot90Fun x) 0 = - x 1 := by simp [rot90Fun]
    show ((rot90Fun x) 0).natAbs ≤ R; rw [h, Int.natAbs_neg]; exact hx 1
  · have h : (rot90Fun x) 1 = x 0 := by simp [rot90Fun]
    show ((rot90Fun x) 1).natAbs ≤ R; rw [h]; exact hx 0


theorem image_subset_box (P : PlanarZ2Subgraph) :
    ∃ R : ℕ, ∀ v : P.V, P.emb v ∈ box 2 R := by
  obtain ⟨R, hR⟩ := finite_subset_box (Set.range P.emb) (Set.finite_range P.emb)
  exact ⟨R, fun v => hR ⟨v, rfl⟩⟩


theorem exterior_dual_edge_not_deleted (P : PlanarZ2Subgraph) (R : ℕ)
    (hR : ∀ v : P.V, P.emb v ∈ box 2 R) {f g : Site 2} (hf : f ∉ box 2 R) :
    crossEdge.symm s(f, g) ∉ (imageGraph P).edgeSet := by
  intro hmem
  have hsymm : crossEdge.symm s(f, g) = s(rot90Inv f, rot90Inv g) := by
    simp [crossEdge, sym2Congr]
  rw [hsymm, SimpleGraph.mem_edgeSet] at hmem
  obtain ⟨x, y, _, hx, _⟩ := hmem
  have hrf : rot90Inv f ∈ box 2 R := hx ▸ hR x
  have hf_eq : f = rot90Fun (rot90Inv f) := by
    have := rot90Equiv.right_inv f
    simpa [rot90Equiv] using this.symm
  exact hf (hf_eq ▸ rot90Fun_mem_box R hrf)


theorem regionGraph_adj_of_exterior (P : PlanarZ2Subgraph) (R : ℕ)
    (hR : ∀ v : P.V, P.emb v ∈ box 2 R) {f g : Site 2}
    (hf : f ∉ box 2 R) (hadj : (hypercubicLattice 2).Adj f g) :
    (regionGraph (imageGraph P)).Adj f g :=
  ⟨hadj, exterior_dual_edge_not_deleted P R hR hf⟩


end StatMech.Lattice
