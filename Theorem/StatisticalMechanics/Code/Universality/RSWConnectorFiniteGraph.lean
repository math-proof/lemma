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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorOriginRegionSet_mem_flipX {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2} (hz : z ∈ rlc_connectorOriginRegionSet gamma gamma') :
    rlc_flipX z ∈ rlc_connectorOriginRegionSet gamma gamma' := by
  obtain ⟨hzAllowed, hoAllowed, hreach⟩ := hz
  have hreach' := hreach.map (rlc_connectorFlipHom gamma gamma')
  have horigin : rlc_flipX (origin 2) = origin 2 :=
    rlc_flipX_eq_self_of_zero rfl
  have hzAllowed' : rlc_flipX z ∈ rlc_connectorAllowed gamma gamma' :=
    (rlc_connectorAllowed_mem_flipX_iff gamma gamma' z).mp hzAllowed
  let o : {x // x ∈ (rlc_connectorAllowed gamma gamma' : Set (Site 2))} :=
    ⟨origin 2, hoAllowed⟩
  let z' : {x // x ∈ (rlc_connectorAllowed gamma gamma' : Set (Site 2))} :=
    ⟨rlc_flipX z, hzAllowed'⟩
  have hoMap : rlc_connectorFlipHom gamma gamma' o = o := by
    apply Subtype.ext
    exact horigin
  have hzMap : rlc_connectorFlipHom gamma gamma' ⟨z, hzAllowed⟩ = z' := by
    rfl
  have hreach'' : ((hypercubicLattice 2).induce
      (rlc_connectorAllowed gamma gamma' : Set (Site 2))).Reachable o z' := by
    rw [← hoMap, ← hzMap]
    exact hreach'
  exact ⟨hzAllowed', hoAllowed, hreach''⟩

theorem rlc_connectorOriginRegionSet_mem_flipX_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (z : Site 2) :
    z ∈ rlc_connectorOriginRegionSet gamma gamma' ↔
      rlc_flipX z ∈ rlc_connectorOriginRegionSet gamma gamma' := by
  constructor
  · exact rlc_connectorOriginRegionSet_mem_flipX gamma gamma'
  · intro hz
    simpa using rlc_connectorOriginRegionSet_mem_flipX gamma gamma' hz

theorem rlc_connectorOriginRegion_mem_flipX_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (z : Site 2) :
    z ∈ rlc_connectorOriginRegion gamma gamma' ↔
      rlc_flipX z ∈ rlc_connectorOriginRegion gamma gamma' := by
  simpa [rlc_connectorOriginRegion] using
    rlc_connectorOriginRegionSet_mem_flipX_iff gamma gamma' z


theorem rlc_connectorEdges_mem_map_flipX {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorEdges gamma gamma') :
    e.map rlc_flipX ∈ rlc_connectorEdges gamma gamma' := by
    rw [rlc_connectorEdges, Finset.mem_filter] at he ⊢
    refine ⟨?_, ?_⟩
    · rw [mem_edgesWithinFinset] at he ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := he.1
      exact ⟨rlc_flipX x, (rlc_connectorBox_mem_flipX_iff x).mp hx,
        rlc_flipX y, (rlc_connectorBox_mem_flipX_iff y).mp hy,
        by simp [Sym2.map_mk]⟩
    · obtain ⟨z, hzRegion, hzEdge⟩ := he.2
      refine ⟨rlc_flipX z,
        (rlc_connectorOriginRegion_mem_flipX_iff gamma gamma' z).mp hzRegion, ?_⟩
      induction e using Sym2.inductionOn with
      | _ x y =>
          simp only [Sym2.map_mk]
          rw [Sym2.mem_iff] at hzEdge ⊢
          rcases hzEdge with rfl | rfl <;> simp

theorem rlc_connectorEdges_mem_map_flipX_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : Sym2 (Site 2)) :
    e ∈ rlc_connectorEdges gamma gamma' ↔
      e.map rlc_flipX ∈ rlc_connectorEdges gamma gamma' := by
  constructor
  · exact rlc_connectorEdges_mem_map_flipX gamma gamma'
  · intro he
    have h := rlc_connectorEdges_mem_map_flipX gamma gamma' he
    simpa using h


theorem rlc_connectorReachSet_reflectedOpenDualCircuit {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_connectorEvent gamma gamma') :
    ∃ (u : Site 2)
      (c : (openSubgraph 2 (rlc_dualReflectConfig
        (rlc_maskConfig (rlc_connectorEdges gamma gamma') omega))).Walk
          (rlc_dualReflect u) (rlc_dualReflect u)),
      c.IsCycle := by
  obtain ⟨u, c, hcyc⟩ :=
    rlc_connectorReachSet_openFaceDualCircuit gamma gamma' omega hno
  exact ⟨u, rlc_dualReflectOpenWalk _ c,
    rlc_dualReflectOpenWalk_isCycle _ hcyc⟩


end
end StatMech.Universality
