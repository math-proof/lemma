/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part9
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_twoChannelFullPhysicalLiftVertexCut_mem {n : Int}
    (A : Set (RlcConnectorVertex n)) (x : RlcConnectorVertex n) :
    x.1 ∈ rlc_twoChannelFullPhysicalLiftVertexCut A ↔ x ∈ A := by
  constructor
  · rintro ⟨hx, hmem⟩
    have heq : (⟨x.1, hx⟩ : RlcConnectorVertex n) = x := Subtype.ext rfl
    simpa [heq] using hmem
  · intro hx
    exact ⟨x.2, by simpa using hx⟩


theorem rlc_twoChannel_traceWiring_not_crosses_staticCut {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {u v : RlcConnectorVertex n}
    (htrace : (rlc_connectorTraceWiring gamma gamma').Adj u v) :
    ¬((u ∈ A ∧ v ∉ A) ∨ (v ∈ A ∧ u ∉ A)) := by
  rcases Finset.mem_union.mp htrace.2 with hright | hleft
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hright
    have hu : rlc_connectorOnRight gamma u := hends.1
    have hv : rlc_connectorOnRight gamma v := hends.2
    have := hAright u hu
    have := hAright v hv
    tauto
  · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft
    have hu : rlc_connectorOnLeft gamma' u := hends.1
    have hv : rlc_connectorOnLeft gamma' v := hends.2
    have := hAleft u hu
    have := hAleft v hv
    tauto


theorem rlc_twoChannel_augmented_crossing_mem_twoChannel {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {u v : RlcConnectorVertex n}
    (haug : (rlc_connectorTwoChannelAugmentedPlanarDomain
      gamma gamma').G.Adj u v)
    (hcross : (u ∈ A ∧ v ∉ A) ∨ (v ∈ A ∧ u ∉ A)) :
    (rlc_connectorTwoChannelGraph gamma gamma').Adj u v := by
  rcases haug with htwo | htrace
  · exact htwo
  · exact (rlc_twoChannel_traceWiring_not_crosses_staticCut
      gamma gamma' A hAright hAleft htrace hcross).elim


theorem rlc_twoChannelFullPhysicalCutTargetGraphAt_adj_iff_faceBoundary
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n)) (x y : RlcConnectorVertex n) :
    (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Adj x y ↔
      ∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
        target.1.1 = s(x, y) ∧
          (faceBoundaryGraph
            (rlc_twoChannelFullPhysicalLiftVertexCut A)).Adj
              (rlc_dualReflect.symm x.1)
              (rlc_dualReflect.symm y.1) := by
  constructor
  · rintro ⟨target, htarget, u, v, hsource, hcross⟩
    refine ⟨target, htarget, ?_⟩
    rw [faceBoundaryGraph_adj]
    have hxy : (hypercubicLattice 2).Adj x.1 y.1 := by
      have hG : (rlc_connectorTwoChannelGraph gamma gamma').Adj x y := by
        rw [← SimpleGraph.mem_edgeSet, ← htarget]
        exact target.1.2
      exact hG.1.elim (fun h => h.1) (fun h => h.1)
    have hfg : (hypercubicLattice 2).Adj
        (rlc_dualReflect.symm x.1) (rlc_dualReflect.symm y.1) := by
      simpa using (rlc_adj_dualReflect
        (rlc_dualReflect.symm x.1) (rlc_dualReflect.symm y.1)).mpr
          (by simpa using hxy)
    refine ⟨hfg, ?_⟩
    have hpims : rlc_pimsEdgeEquiv (s(x.1, y.1)) =
        sharedPrimalEdge (rlc_dualReflect.symm x.1)
          (rlc_dualReflect.symm y.1) := by
      simpa using rlc_pimsEdgeEquiv_reflected_mk_of_adj hfg
    have hsourceSite :
        s(u.1, v.1) = sharedPrimalEdge (rlc_dualReflect.symm x.1)
          (rlc_dualReflect.symm y.1) := by
      calc
        s(u.1, v.1) =
            (rlc_twoChannelFullPhysicalSourceEdge target).1.map Subtype.val := by
          rw [hsource, Sym2.map_mk]
        _ = rlc_pimsEdgeEquiv (target.1.1.map Subtype.val) :=
          rlc_twoChannelFullPhysicalSourceEdge_map target
        _ = rlc_pimsEdgeEquiv (s(x.1, y.1)) := by
          rw [htarget, Sym2.map_mk]
        _ = _ := hpims
    rw [← hsourceSite, bdEdge_mk,
      rlc_twoChannelFullPhysicalLiftVertexCut_mem,
      rlc_twoChannelFullPhysicalLiftVertexCut_mem]
    rcases hcross with h | h <;> tauto
  · rintro ⟨target, htarget, hface⟩
    let source := rlc_twoChannelFullPhysicalSourceEdge target
    induction hsourceEdge : source.1 using Sym2.inductionOn with
    | _ u v =>
        refine ⟨target, htarget, u, v, hsourceEdge, ?_⟩
        rw [faceBoundaryGraph_adj] at hface
        have hpims : rlc_pimsEdgeEquiv (s(x.1, y.1)) =
            sharedPrimalEdge (rlc_dualReflect.symm x.1)
              (rlc_dualReflect.symm y.1) := by
          simpa using rlc_pimsEdgeEquiv_reflected_mk_of_adj hface.1
        have hsourceSite : s(u.1, v.1) =
            sharedPrimalEdge (rlc_dualReflect.symm x.1)
              (rlc_dualReflect.symm y.1) := by
          calc
            s(u.1, v.1) = source.1.map Subtype.val := by
              rw [hsourceEdge, Sym2.map_mk]
            _ = rlc_pimsEdgeEquiv (target.1.1.map Subtype.val) :=
              rlc_twoChannelFullPhysicalSourceEdge_map target
            _ = rlc_pimsEdgeEquiv (s(x.1, y.1)) := by
              rw [htarget, Sym2.map_mk]
            _ = _ := hpims
        have hbd := hface.2
        rw [← hsourceSite, bdEdge_mk,
          rlc_twoChannelFullPhysicalLiftVertexCut_mem,
          rlc_twoChannelFullPhysicalLiftVertexCut_mem] at hbd
        tauto


end
end StatMech.Universality
