/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassObstruction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_mem_fourTraceWallGraph_edgeSet_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)} (hlat : e ∈ (hypercubicLattice 2).edgeSet) :
    e ∈ (rlc_connectorFourTraceWallGraph gamma gamma').edgeSet ↔
      e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at hlat ⊢
      exact and_iff_right hlat

theorem rlc_mem_connectorBarrier_of_mem_fourTraceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorFourTraceEdges gamma gamma')
    {z : Site 2} (hz : z ∈ e) :
    z ∈ rlc_connectorBarrier gamma gamma' := by
  rw [rlc_connectorFourTraceEdges, Finset.mem_union] at he
  rcases he with horiginal | hreflected
  · rw [Finset.mem_union] at horiginal
    rcases horiginal with hright | hleft
    · induction e using Sym2.inductionOn with
      | _ x y =>
          have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hright
          rw [Sym2.mem_iff] at hz
          rcases hz with rfl | rfl <;>
            simp [rlc_connectorBarrier, hends.1, hends.2]
    · induction e using Sym2.inductionOn with
      | _ x y =>
          have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft
          rw [Sym2.mem_iff] at hz
          rcases hz with rfl | rfl <;>
            simp [rlc_connectorBarrier, hends.1, hends.2]
  · rw [rlc_connectorReflectedTraceEdges, Finset.mem_union] at hreflected
    rcases hreflected with hright | hleft
    · obtain ⟨e0, he0, heq⟩ := Finset.mem_image.mp hright
      induction e0 using Sym2.inductionOn with
      | _ x y =>
          have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 he0
          have heq' : e = s(rlc_flipX x, rlc_flipX y) := by
            simpa [Sym2.map_mk] using heq.symm
          rw [heq', Sym2.mem_iff] at hz
          rcases hz with rfl | rfl
          · simp [rlc_connectorBarrier, hends.1]
          · simp [rlc_connectorBarrier, hends.2]
    · obtain ⟨e0, he0, heq⟩ := Finset.mem_image.mp hleft
      induction e0 using Sym2.inductionOn with
      | _ x y =>
          have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 he0
          have heq' : e = s(rlc_flipX x, rlc_flipX y) := by
            simpa [Sym2.map_mk] using heq.symm
          rw [heq', Sym2.mem_iff] at hz
          rcases hz with rfl | rfl
          · simp [rlc_connectorBarrier, hends.1]
          · simp [rlc_connectorBarrier, hends.2]


end
end StatMech.Universality
