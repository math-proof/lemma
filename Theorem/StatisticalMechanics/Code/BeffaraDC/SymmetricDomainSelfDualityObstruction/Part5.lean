/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part12
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Def.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDualityObstruction.Part5
open Set SimpleGraph
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

namespace SymmetricDomain

noncomputable section

@[simp] theorem connected_adj_one_bridge :
    connectedSymmetricDomain.finiteGraph.Adj
      connectedVertexOne connectedVertexBridge := by
  norm_num [finiteGraph, connectedVertexOne, connectedVertexBridge,
    separatedSiteOne, connectedBridgeSite, hypercubicLattice_adj,
    Fin.sum_univ_two]

@[simp] theorem connected_adj_two_bridge :
    connectedSymmetricDomain.finiteGraph.Adj
      connectedVertexTwo connectedVertexBridge := by
  norm_num [finiteGraph, connectedVertexTwo, connectedVertexBridge,
    separatedSiteTwo, connectedBridgeSite, hypercubicLattice_adj,
    Fin.sum_univ_two]


theorem bcProb_one_eq_fkProb_one {V : Type*} [Fintype V] [DecidableEq V]
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    (p : Real) (omega : ConfigSpace (Sym2 V)) :
    FK.bcProb G C p 1 omega = FK.fkProb G p 1 omega := by
  have hw : ∀ eta, FK.bcWeight G C p 1 eta = FK.fkWeight G p 1 eta := by
    intro eta
    simp [FK.bcWeight, FK.fkWeight]
  have hZ : FK.bcZ G C p 1 = FK.fkZ G p 1 := by
    rw [FK.bcZ, FK.fkZ]
    exact Finset.sum_congr rfl (fun eta _ => hw eta)
  rw [FK.bcProb, FK.fkProb, hw, hZ]

theorem connected_vertex_cases (z : connectedSymmetricDomain.Vertex) :
    z = connectedVertexOne ∨ z = connectedVertexTwo ∨
      z = connectedVertexBridge := by
  have hz := z.2
  change z.1 ∈ ({separatedSiteOne, separatedSiteTwo,
    connectedBridgeSite} : Set (Site 2)) at hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with hz | hz | hz
  · exact Or.inl (Subtype.ext hz)
  · exact Or.inr (Or.inl (Subtype.ext hz))
  · exact Or.inr (Or.inr (Subtype.ext hz))

theorem connected_vertex_one_ne_two :
    connectedVertexOne ≠ connectedVertexTwo := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num [connectedVertexOne, connectedVertexTwo,
    separatedSiteOne, separatedSiteTwo] at hv


theorem connected_finiteGraph_connected :
    connectedSymmetricDomain.finiteGraph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨connectedVertexOne, ?_⟩
  intro z
  rcases connected_vertex_cases z with rfl | rfl | rfl
  · exact SimpleGraph.Reachable.rfl
  · exact connected_adj_one_bridge.reachable.trans
      connected_adj_two_bridge.symm.reachable
  · exact connected_adj_one_bridge.reachable


theorem connected_boundary_paths_disjoint :
    connectedSymmetricDomain.γ₁.support ∩
      connectedSymmetricDomain.γ₂.support = ∅ := by
  ext z
  simp [connectedSymmetricDomain, separatedSiteOne, separatedSiteTwo]


theorem connected_openConnected_iff
    (omega : ConfigSpace (Sym2 connectedSymmetricDomain.Vertex)) :
    connectedSymmetricDomain.OpenConnected omega ↔
      omega s(connectedVertexOne, connectedVertexBridge) = true ∧
      omega s(connectedVertexTwo, connectedVertexBridge) = true := by
  constructor
  · rintro ⟨x, y, hx, hy, hreach⟩
    have hxEq : x = connectedVertexOne := by
      apply Subtype.ext
      simpa [OnGammaOne, connectedSymmetricDomain,
        connectedVertexOne] using hx
    have hyEq : y = connectedVertexTwo := by
      apply Subtype.ext
      simpa [OnGammaTwo, connectedSymmetricDomain,
        connectedVertexTwo] using hy
    subst x
    subst y
    constructor
    · by_contra hone
      apply (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
        connected_vertex_one_ne_two ?_) hreach
      ext z
      simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false,
        iff_false]
      intro haz
      rw [FK.openSub_adj] at haz
      rcases connected_vertex_cases z with rfl | rfl | rfl
      · exact haz.1.ne rfl
      · norm_num [finiteGraph, connectedVertexOne, connectedVertexTwo,
          separatedSiteOne, separatedSiteTwo, hypercubicLattice_adj,
          Fin.sum_univ_two] at haz
      · exact hone haz.2
    · by_contra htwo
      apply (SimpleGraph.not_reachable_of_neighborSet_right_eq_empty
        connected_vertex_one_ne_two ?_) hreach
      ext z
      simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false,
        iff_false]
      intro haz
      rw [FK.openSub_adj] at haz
      rcases connected_vertex_cases z with rfl | rfl | rfl
      · norm_num [finiteGraph, connectedVertexOne, connectedVertexTwo,
          separatedSiteOne, separatedSiteTwo, hypercubicLattice_adj,
          Fin.sum_univ_two] at haz
      · exact haz.1.ne rfl
      · apply htwo
        simpa only [Sym2.eq_swap] using haz.2
  · rintro ⟨hone, htwo⟩
    refine ⟨connectedVertexOne, connectedVertexTwo, ?_, ?_, ?_⟩
    · simp [OnGammaOne, connectedSymmetricDomain, connectedVertexOne]
    · simp [OnGammaTwo, connectedSymmetricDomain, connectedVertexTwo]
    · apply SimpleGraph.Reachable.trans
        ((FK.openSub_adj _ _ _ _).2 ⟨connected_adj_one_bridge, hone⟩).reachable
      apply ((FK.openSub_adj _ _ _ _).2
        ⟨connected_adj_two_bridge.symm, ?_⟩).reachable
      simpa only [Sym2.eq_swap] using htwo


end
end SymmetricDomain
end BeffaraDC
end StatMech
