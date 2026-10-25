/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedExplorationBridge
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Def.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part8
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_connectorExtendConfig_apply {n : Int}
    (psi : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n)) :
    rlc_connectorExtendConfig psi (e.map Subtype.val) = psi e := by
  exact (Sym2.map.injective Subtype.val_injective).extend_apply _ _ _


theorem rlc_extremalPairCandidateEdge_exists_connectorLift {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_extremalPairCandidateEdges (gamma, gamma')) :
    ∃ f : Sym2 (RlcConnectorVertex n), f.map Subtype.val = e := by
  have hexplored := rlc_extremalPairCandidateEdges_subset_explored
    gamma gamma' he
  rw [Finset.mem_union] at hexplored
  rcases hexplored with hright | hleft
  · rw [mem_edgesWithinFinset] at hright
    obtain ⟨x, hx, y, hy, rfl⟩ := hright
    have hx' : x ∈ rect (-2 * n) (2 * n) (-n) n := by
      rw [rlc_rightExploredVertices, Finset.mem_sdiff] at hx
      rw [rlc_mem_rectFinset, mem_rect] at hx
      rw [mem_rect]
      omega
    have hy' : y ∈ rect (-2 * n) (2 * n) (-n) n := by
      rw [rlc_rightExploredVertices, Finset.mem_sdiff] at hy
      rw [rlc_mem_rectFinset, mem_rect] at hy
      rw [mem_rect]
      omega
    exact ⟨s(⟨x, hx'⟩, ⟨y, hy'⟩), by simp⟩
  · rw [mem_edgesWithinFinset] at hleft
    obtain ⟨x, hx, y, hy, rfl⟩ := hleft
    have hx' : x ∈ rect (-2 * n) (2 * n) (-n) n := by
      rw [rlc_leftExploredVertices, Finset.mem_sdiff] at hx
      rw [rlc_mem_rectFinset, mem_rect] at hx
      rw [mem_rect]
      omega
    have hy' : y ∈ rect (-2 * n) (2 * n) (-n) n := by
      rw [rlc_leftExploredVertices, Finset.mem_sdiff] at hy
      rw [rlc_mem_rectFinset, mem_rect] at hy
      rw [mem_rect]
      omega
    exact ⟨s(⟨x, hx'⟩, ⟨y, hy'⟩), by simp⟩


end
end StatMech.Universality
