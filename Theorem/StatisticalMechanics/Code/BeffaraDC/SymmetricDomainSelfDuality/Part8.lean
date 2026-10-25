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
import Def.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part12
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

theorem disjointDisconnectedDomain_boundaryBlocksDisjoint :
    ¬disjointDisconnectedDomain.BoundaryBlocksOverlap := by
  rintro ⟨x, hx₁, hx₂⟩
  have hleft : x.1 = disjointLeftPoint := by
    simpa [OnGammaOne, disjointDisconnectedDomain] using hx₁
  have hright : x.1 = disjointRightPoint := by
    simpa [OnGammaTwo, disjointDisconnectedDomain] using hx₂
  have := hleft.symm.trans hright
  simp [disjointLeftPoint, disjointRightPoint] at this


theorem disjointDisconnectedDomain_finiteGraph_no_adj
    (x y : disjointDisconnectedDomain.Vertex) :
    ¬disjointDisconnectedDomain.finiteGraph.Adj x y := by
  intro hxy
  have hx : x.1 = disjointLeftPoint ∨ x.1 = disjointRightPoint := by
    have hxmem := x.2
    change x.1 ∈ ({disjointLeftPoint, disjointRightPoint} : Set (Site 2)) at hxmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hxmem
  have hy : y.1 = disjointLeftPoint ∨ y.1 = disjointRightPoint := by
    have hymem := y.2
    change y.1 ∈ ({disjointLeftPoint, disjointRightPoint} : Set (Site 2)) at hymem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hymem
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    simp [finiteGraph, hypercubicLattice_adj, Fin.sum_univ_two, hx, hy,
      disjointLeftPoint, disjointRightPoint] at hxy


theorem disjointDisconnectedDomain_mixedWiring_no_adj
    (x y : disjointDisconnectedDomain.Vertex) :
    ¬disjointDisconnectedDomain.mixedWiring.Adj x y := by
  rw [mixedWiring, SimpleGraph.sup_adj]
  rintro (hgamma | hgamma)
  · rw [StatMech.Lattice.boundaryCliqueGraph_adj] at hgamma
    apply hgamma.1
    apply Subtype.ext
    have hx : x.1 = disjointLeftPoint := by
      simpa [OnGammaOne, disjointDisconnectedDomain] using hgamma.2.1
    have hy : y.1 = disjointLeftPoint := by
      simpa [OnGammaOne, disjointDisconnectedDomain] using hgamma.2.2
    exact hx.trans hy.symm
  · rw [StatMech.Lattice.boundaryCliqueGraph_adj] at hgamma
    apply hgamma.1
    apply Subtype.ext
    have hx : x.1 = disjointRightPoint := by
      simpa [OnGammaTwo, disjointDisconnectedDomain] using hgamma.2.1
    have hy : y.1 = disjointRightPoint := by
      simpa [OnGammaTwo, disjointDisconnectedDomain] using hgamma.2.2
    exact hx.trans hy.symm


theorem disjointDisconnectedDomain_not_mixedConnected
    (omega : ConfigSpace (Sym2 disjointDisconnectedDomain.Vertex)) :
    ¬disjointDisconnectedDomain.MixedConnected omega := by
  rintro ⟨x, y, hx, hy, hreach⟩
  have hgraph :
      FK.openSub disjointDisconnectedDomain.finiteGraph omega ⊔
          disjointDisconnectedDomain.mixedWiring = ⊥ := by
    ext u v
    simp only [SimpleGraph.sup_adj, SimpleGraph.bot_adj, iff_false, not_or]
    exact ⟨fun huv => disjointDisconnectedDomain_finiteGraph_no_adj u v
        (FK.openSub_le disjointDisconnectedDomain.finiteGraph omega huv),
      disjointDisconnectedDomain_mixedWiring_no_adj u v⟩
  rw [hgraph, SimpleGraph.reachable_bot] at hreach
  have hleft : x.1 = disjointLeftPoint := by
    simpa [OnGammaOne, disjointDisconnectedDomain] using hx
  have hright : y.1 = disjointRightPoint := by
    simpa [OnGammaTwo, disjointDisconnectedDomain] using hy
  have hpoints : disjointLeftPoint = disjointRightPoint :=
    hleft.symm.trans (congrArg Subtype.val hreach) |>.trans hright
  simp [disjointLeftPoint, disjointRightPoint] at hpoints


theorem disjointDisconnectedDomain_no_mixedDualComplementRN (q : Real) :
    MixedDualComplementRN disjointDisconnectedDomain q → False := by
  intro R
  let omega : ConfigSpace (Sym2 disjointDisconnectedDomain.Vertex) :=
    fun _ => false
  have hnot := disjointDisconnectedDomain_not_mixedConnected omega
  have hconnected :
      disjointDisconnectedDomain.MixedConnected (R.dual omega) :=
    (R.connected_dual_iff omega).mpr hnot
  exact disjointDisconnectedDomain_not_mixedConnected _ hconnected


end SymmetricDomain
end
end BeffaraDC
end StatMech
