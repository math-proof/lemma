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
import Def.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part14
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

theorem connectedV_edges_ne : connectedVLeftEdge ≠ connectedVRightEdge := by
  intro h
  have hmem : connectedVLeft ∈ connectedVRightEdge := by
    rw [← h]
    simp [connectedVLeftEdge]
  simp [connectedVRightEdge, connectedVLeft, connectedVAxis, connectedVRight,
    connectedVAxisPoint, disjointLeftPoint, disjointRightPoint] at hmem


theorem connectedVDomain_mixedConnected_iff
    (omega : ConfigSpace (Sym2 connectedVDomain.Vertex)) :
    connectedVDomain.MixedConnected omega ↔
      omega connectedVLeftEdge = true ∧ omega connectedVRightEdge = true := by
  rw [mixedConnected_iff_openConnected]
  constructor
  · rintro ⟨x, y, hx, hy, hreach⟩
    have hxval : x.1 = disjointLeftPoint := by
      simpa [OnGammaOne, connectedVDomain] using hx
    have hyval : y.1 = disjointRightPoint := by
      simpa [OnGammaTwo, connectedVDomain] using hy
    have hxeq : x = connectedVLeft :=
      Subtype.ext hxval
    have hyeq : y = connectedVRight :=
      Subtype.ext hyval
    subst x
    subst y
    have hlr : connectedVLeft ≠ connectedVRight := by
      intro h
      have := congrArg Subtype.val h
      simp [connectedVLeft, connectedVRight, disjointLeftPoint,
        disjointRightPoint] at this
    constructor
    · by_contra hleft
      have hisolated :
          (FK.openSub connectedVDomain.finiteGraph omega).neighborSet
              connectedVLeft = ∅ := by
        ext z
        simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
        rcases connectedVDomain_vertex_cases z with rfl | rfl | rfl
        · intro hopen
          rw [FK.openSub_adj] at hopen
          exact hleft (by simpa [connectedVLeftEdge] using hopen.2)
        · exact
            (FK.openSub connectedVDomain.finiteGraph omega).loopless.irrefl _
        · simp [FK.openSub_adj, finiteGraph, hypercubicLattice_adj,
            Fin.sum_univ_two, connectedVLeft, connectedVRight,
            disjointLeftPoint, disjointRightPoint]
      exact (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
        hlr hisolated) hreach
    · by_contra hright
      have hisolated :
          (FK.openSub connectedVDomain.finiteGraph omega).neighborSet
              connectedVRight = ∅ := by
        ext z
        simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
        rcases connectedVDomain_vertex_cases z with rfl | rfl | rfl
        · intro hopen
          rw [FK.openSub_adj] at hopen
          exact hright (by
            simpa [connectedVRightEdge, Sym2.eq_swap] using hopen.2)
        · simp [FK.openSub_adj, finiteGraph, hypercubicLattice_adj,
            Fin.sum_univ_two, connectedVLeft, connectedVRight,
            disjointLeftPoint, disjointRightPoint]
        · exact
            (FK.openSub connectedVDomain.finiteGraph omega).loopless.irrefl _
      exact (SimpleGraph.not_reachable_of_neighborSet_right_eq_empty
        hlr hisolated) hreach
  · rintro ⟨hleft, hright⟩
    refine ⟨connectedVLeft, connectedVRight, ?_, ?_, ?_⟩
    · simp [OnGammaOne, connectedVDomain, connectedVLeft]
    · simp [OnGammaTwo, connectedVDomain, connectedVRight]
    · exact (SimpleGraph.Adj.reachable
          ((FK.openSub_adj _ _ _ _).mpr
            ⟨connectedVDomain_left_axis_adj, hleft⟩)).trans
        (SimpleGraph.Adj.reachable
          ((FK.openSub_adj _ _ _ _).mpr
            ⟨connectedVDomain_axis_right_adj, hright⟩))


end SymmetricDomain
end
end BeffaraDC
end StatMech
