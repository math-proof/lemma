/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part89
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorEvent_iff_finite {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    omega ∈ rlc_connectorEvent gamma gamma' ↔
      rlc_connectorRestrictConfig omega ∈
        rlc_finiteConnectorEvent gamma gamma' := by
  rw [rlc_connectorEvent, rlc_finiteConnectorEvent]
  constructor
  · rintro ⟨x, hx, y, hy, hxR, hyR, hxy⟩
    refine ⟨⟨x, hxR⟩, ⟨y, hyR⟩, hx, hy, ?_⟩
    rw [rlc_openSub_connectorFiniteGraph_restrict_eq]
    exact hxy
  · rintro ⟨x, y, hx, hy, hxy⟩
    refine ⟨x, hx, y, hy, x.2, y.2, ?_⟩
    rw [rlc_openSub_connectorFiniteGraph_restrict_eq] at hxy
    exact hxy


theorem rlc_connectorAmbientMixedConfig_mem_connectorEvent_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rlc_connectorAmbientMixedConfig gamma gamma' tau ∈
        rlc_connectorEvent gamma gamma' ↔
      tau ∈ rlc_finiteConnectorEvent gamma gamma' := by
  rw [rlc_connectorEvent_iff_finite]
  unfold rlc_finiteConnectorEvent
  simp only [Set.mem_setOf_eq]
  rw [rlc_openSub_restrict_ambientMixed_eq]


theorem rlc_finiteConnectorFailure_reflectedOpenDualCircuit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : tau ∉ rlc_finiteConnectorEvent gamma gamma') :
    ∃ (u : Site 2)
      (c : (openSubgraph 2 (rlc_dualReflectConfig
        (rlc_maskConfig (rlc_connectorEdges gamma gamma')
          (rlc_connectorAmbientMixedConfig gamma gamma' tau)))).Walk
          (rlc_dualReflect u) (rlc_dualReflect u)),
      c.IsCycle := by
  apply rlc_connectorReachSet_reflectedOpenDualCircuit gamma gamma'
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  intro hconn
  exact hno ((rlc_connectorAmbientMixedConfig_mem_connectorEvent_iff
    gamma gamma' tau).mp hconn)


theorem rlc_connectorReachSet_openWalk_lift {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    {u v : RlcConnectorVertex n}
    (hu : (u : Site 2) ∈ rlc_connectorReachSet gamma gamma' omega)
    (w : (openSubgraphInduce 2
      (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)
      (rect (-2 * n) (2 * n) (-n) n)).Walk u v) :
    ∃ hv : (v : Site 2) ∈ rlc_connectorReachSet gamma gamma' omega,
      ((hypercubicLattice 2).induce
        (rlc_connectorReachSet gamma gamma' omega)).Reachable
          ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction w with
  | nil => exact ⟨hu, Reachable.refl _⟩
  | @cons a b c hab p ih =>
      have habOpen : (openSubgraph 2
          (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega)).Adj
          (a : Site 2) (b : Site 2) := hab
      have hb : (b : Site 2) ∈
          rlc_connectorReachSet gamma gamma' omega :=
        rlc_connectorReachSet_extend gamma gamma' omega hu b.2
          habOpen.1 habOpen.2
      obtain ⟨hc, hbc⟩ := ih hb
      have habReach : ((hypercubicLattice 2).induce
          (rlc_connectorReachSet gamma gamma' omega)).Adj
          ⟨a, hu⟩ ⟨b, hb⟩ := habOpen.1
      exact ⟨hc, habReach.reachable.trans hbc⟩


theorem rlc_connectorReachSet_rightPath_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (hx : x ∈ rlc_pathVertices gamma.1)
    (hy : y ∈ rlc_pathVertices gamma.1) :
    ((hypercubicLattice 2).induce
      (rlc_connectorReachSet gamma gamma' omega)).Reachable
        ⟨x, rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega hx⟩
        ⟨y, rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega hy⟩ := by
  let W := rlc_ambientCrossingWalk gamma.1
  have hxW : x ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 x).2 hx
  have hyW : y ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 y).2 hy
  let wxy : (hypercubicLattice 2).Walk x y :=
    (W.takeUntil x hxW).reverse.append (W.takeUntil y hyW)
  have hwxy : ∀ z ∈ wxy.support,
      z ∈ rlc_connectorReachSet gamma gamma' omega := by
    intro z hz
    have hzW : z ∈ W.support := by
      dsimp only [wxy] at hz
      rw [SimpleGraph.Walk.mem_support_append_iff,
        SimpleGraph.Walk.support_reverse] at hz
      rcases hz with hz | hz
      · exact W.support_takeUntil_subset_support hxW (by simpa using hz)
      · exact W.support_takeUntil_subset_support hyW hz
    exact rlc_rightPathVertex_mem_connectorReachSet gamma gamma' omega
      ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).1 hzW)
  exact ⟨wxy.induce (rlc_connectorReachSet gamma gamma' omega) hwxy⟩


theorem rlc_connectorReachSet_reachable {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (hu : u ∈ rlc_connectorReachSet gamma gamma' omega)
    (hv : v ∈ rlc_connectorReachSet gamma gamma' omega) :
    ((hypercubicLattice 2).induce
      (rlc_connectorReachSet gamma gamma' omega)).Reachable
        ⟨u, hu⟩ ⟨v, hv⟩ := by
  have hu0 := hu
  have hv0 := hv
  obtain ⟨huBox, xu, hxu, hxuBox, hxuReach⟩ := hu
  obtain ⟨hvBox, xv, hxv, hxvBox, hxvReach⟩ := hv
  have hxuFill := rlc_rightPathVertex_mem_connectorReachSet
    gamma gamma' omega hxu
  have hxvFill := rlc_rightPathVertex_mem_connectorReachSet
    gamma gamma' omega hxv
  obtain ⟨hu', hxuToU⟩ := rlc_connectorReachSet_openWalk_lift
    gamma gamma' omega hxuFill hxuReach.some
  obtain ⟨hv', hxvToV⟩ := rlc_connectorReachSet_openWalk_lift
    gamma gamma' omega hxvFill hxvReach.some
  have hsources := rlc_connectorReachSet_rightPath_reachable
    gamma gamma' omega hxu hxv
  have huEq : (⟨u, hu'⟩ : rlc_connectorReachSet gamma gamma' omega) =
      ⟨u, hu0⟩ := rfl
  have hvEq : (⟨v, hv'⟩ : rlc_connectorReachSet gamma gamma' omega) =
      ⟨v, hv0⟩ := rfl
  rw [huEq] at hxuToU
  rw [hvEq] at hxvToV
  exact hxuToU.symm.trans (hsources.trans hxvToV)


theorem rlc_connectorReachSet_reachable_in_barrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (hu : u ∈ rlc_connectorReachSet gamma gamma' omega)
    (hv : v ∈ rlc_connectorReachSet gamma gamma' omega) :
    (latticeMinusBarrier
      (rlc_connectorReachSet gamma gamma' omega)).Reachable u v := by
  let hom : ((hypercubicLattice 2).induce
      (rlc_connectorReachSet gamma gamma' omega)) →g
      latticeMinusBarrier (rlc_connectorReachSet gamma gamma' omega) := {
    toFun z := (z : Site 2)
    map_rel' := by
      intro a b hab
      exact latticeMinusBarrier_adj_of_both_mem _ hab a.2 b.2
  }
  have h := (rlc_connectorReachSet_reachable
    gamma gamma' omega hu hv).map hom
  simpa [hom] using h


end
end StatMech.Universality
