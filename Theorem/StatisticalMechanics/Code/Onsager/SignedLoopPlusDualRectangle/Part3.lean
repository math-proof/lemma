/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualRectangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualContour.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle.Part4
open Finset SimpleGraph Set


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

noncomputable section

@[simp] theorem ons_plusDualFaceEdgeLift_map_val (n : Nat)
    (edge : {edge // edge ∈ ons_plusDualFaceEdgeSet n}) :
    Sym2.map Subtype.val (ons_plusDualFaceEdgeLift n edge) = edge.1 := by
  rw [ons_plusDualFaceEdgeLift, Sym2.map_mk]
  exact edge.1.out_eq

theorem ons_plusDualFaceEdgeLift_mem_edgeFinset (n : Nat)
    (edge : {edge // edge ∈ ons_plusDualFaceEdgeSet n}) :
    ons_plusDualFaceEdgeLift n edge ∈ (ons_plusDualFaceGraph n).edgeFinset := by
  rw [ons_plusDualFaceEdgeLift, SimpleGraph.mem_edgeFinset]
  apply (SimpleGraph.mem_edgeSet _).mpr
  change (hypercubicLattice 2).Adj edge.1.out.1 edge.1.out.2
  apply (SimpleGraph.mem_edgeSet _).mp
  simpa only [edge.1.out_eq] using edge.2.1


end
end StatMech.Onsager
