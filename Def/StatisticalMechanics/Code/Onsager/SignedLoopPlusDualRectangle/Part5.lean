/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualRectangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualContour.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle.Part3
open Finset SimpleGraph Set


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

noncomputable section

noncomputable def ons_plusDualFaceEdgeEquivGraphEdge (n : Nat) :
    {edge // edge ∈ ons_plusDualFaceEdgeSet n} ≃
      {edge // edge ∈ (ons_plusDualFaceGraph n).edgeFinset} where
  toFun edge := ⟨ons_plusDualFaceEdgeLift n edge,
    ons_plusDualFaceEdgeLift_mem_edgeFinset n edge⟩
  invFun edge := ⟨Sym2.map Subtype.val edge.1, by
    obtain ⟨⟨f, g⟩, hfg⟩ := edge.1.exists_rep
    have hedge : s(f, g) ∈ (ons_plusDualFaceGraph n).edgeFinset := by
      simpa only [← hfg] using edge.2
    have hadj : (ons_plusDualFaceGraph n).Adj f g := by
      rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeFinset]
      exact hedge
    rw [← hfg, Sym2.map_mk]
    constructor
    · rw [SimpleGraph.mem_edgeSet]
      exact hadj
    · intro x hx
      rw [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact f.2
      · exact g.2⟩
  left_inv edge := by
    apply Subtype.ext
    exact ons_plusDualFaceEdgeLift_map_val n edge
  right_inv edge := by
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    rw [ons_plusDualFaceEdgeLift_map_val]


noncomputable def ons_plusDualFaceGraphEdgeEquivRectEdge (n : Nat) :
    {edge // edge ∈ (ons_plusDualFaceGraph n).edgeFinset} ≃
      {edge // edge ∈
        (ons_rectDualGraph (2 * n + 1) (2 * n + 1)).edgeFinset} where
  toFun edge := ⟨Sym2.map (ons_plusDualFaceEquivRect n) edge.1, by
    obtain ⟨⟨f, g⟩, hfg⟩ := edge.1.exists_rep
    have hedge : (ons_plusDualFaceGraph n).Adj f g := by
      rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeFinset]
      simpa only [← hfg] using edge.2
    rw [← hfg, Sym2.map_mk, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet]
    exact (ons_plusDualFaceEquivRect_adj n f g).mp hedge⟩
  invFun edge := ⟨Sym2.map (ons_plusDualFaceEquivRect n).symm edge.1, by
    obtain ⟨⟨f, g⟩, hfg⟩ := edge.1.exists_rep
    have hedge :
        (ons_rectDualGraph (2 * n + 1) (2 * n + 1)).Adj f g := by
      rw [← SimpleGraph.mem_edgeSet, ← SimpleGraph.mem_edgeFinset]
      simpa only [← hfg] using edge.2
    rw [← hfg, Sym2.map_mk, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet]
    exact (ons_plusDualFaceEquivRect_adj n _ _).mpr (by simpa using hedge)⟩
  left_inv edge := by
    apply Subtype.ext
    change Sym2.map (ons_plusDualFaceEquivRect n).symm
      (Sym2.map (ons_plusDualFaceEquivRect n) edge.1) = edge.1
    obtain ⟨⟨f, g⟩, hfg⟩ := edge.1.exists_rep
    rw [← hfg, Sym2.map_mk, Sym2.map_mk]
    simp
  right_inv edge := by
    apply Subtype.ext
    change Sym2.map (ons_plusDualFaceEquivRect n)
      (Sym2.map (ons_plusDualFaceEquivRect n).symm edge.1) = edge.1
    obtain ⟨⟨f, g⟩, hfg⟩ := edge.1.exists_rep
    rw [← hfg, Sym2.map_mk, Sym2.map_mk]
    simp


noncomputable def ons_touchingBondEquivRectDualEdge (n : Nat) :
    {edge // edge ∈ bondFinsetTouch 2 n} ≃
      {edge // edge ∈
        (ons_rectDualGraph (2 * n + 1) (2 * n + 1)).edgeFinset} :=
  (ons_touchingBondEquivPlusDualEdge n).trans
    ((ons_plusDualFaceEdgeEquivGraphEdge n).trans
      (ons_plusDualFaceGraphEdgeEquivRectEdge n))


end
end StatMech.Onsager
