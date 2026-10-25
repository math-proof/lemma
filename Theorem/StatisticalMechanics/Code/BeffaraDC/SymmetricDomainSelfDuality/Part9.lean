/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part10
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Def.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part13
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

theorem connectedVDomain_vertex_cases (x : connectedVDomain.Vertex) :
    x = connectedVAxis ∨ x = connectedVLeft ∨ x = connectedVRight := by
  have hx := x.2
  change x.1 ∈
    ({connectedVAxisPoint, disjointLeftPoint, disjointRightPoint} : Set (Site 2)) at hx
  rcases (by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx) with
    hx | hx | hx
  · exact Or.inl (Subtype.ext hx)
  · exact Or.inr (Or.inl (Subtype.ext hx))
  · exact Or.inr (Or.inr (Subtype.ext hx))


theorem connectedVDomain_left_axis_adj :
    connectedVDomain.finiteGraph.Adj connectedVLeft connectedVAxis := by
  simp [finiteGraph, hypercubicLattice_adj, Fin.sum_univ_two,
    connectedVLeft, connectedVAxis, connectedVAxisPoint, disjointLeftPoint]


theorem connectedVDomain_axis_right_adj :
    connectedVDomain.finiteGraph.Adj connectedVAxis connectedVRight := by
  simp [finiteGraph, hypercubicLattice_adj, Fin.sum_univ_two,
    connectedVRight, connectedVAxis, connectedVAxisPoint, disjointRightPoint]


theorem connectedVDomain_finiteGraph_connected :
    connectedVDomain.finiteGraph.Connected := by
  letI : Nonempty connectedVDomain.Vertex := ⟨connectedVAxis⟩
  refine SimpleGraph.Connected.mk ?_
  intro x y
  rcases connectedVDomain_vertex_cases x with rfl | rfl | rfl <;>
    rcases connectedVDomain_vertex_cases y with rfl | rfl | rfl
  · exact SimpleGraph.Reachable.rfl
  · exact connectedVDomain_left_axis_adj.symm.reachable
  · exact connectedVDomain_axis_right_adj.reachable
  · exact connectedVDomain_left_axis_adj.reachable
  · exact SimpleGraph.Reachable.rfl
  · exact connectedVDomain_left_axis_adj.reachable.trans
      connectedVDomain_axis_right_adj.reachable
  · exact connectedVDomain_axis_right_adj.symm.reachable
  · exact connectedVDomain_axis_right_adj.symm.reachable.trans
      connectedVDomain_left_axis_adj.symm.reachable
  · exact SimpleGraph.Reachable.rfl


theorem connectedVDomain_boundaryBlocksDisjoint :
    ¬connectedVDomain.BoundaryBlocksOverlap := by
  rintro ⟨x, hx₁, hx₂⟩
  have hleft : x.1 = disjointLeftPoint := by
    simpa [OnGammaOne, connectedVDomain] using hx₁
  have hright : x.1 = disjointRightPoint := by
    simpa [OnGammaTwo, connectedVDomain] using hx₂
  have := hleft.symm.trans hright
  simp [disjointLeftPoint, disjointRightPoint] at this


end SymmetricDomain
end
end BeffaraDC
end StatMech
