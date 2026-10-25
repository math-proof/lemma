/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassObstruction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier.Part7
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_fci_faceEdgeEquiv_symm_mk_of_adj
    {x y : Site 2} (hxy : (hypercubicLattice 2).Adj x y) :
    fci_faceEdgeEquiv.symm s(x, y) = flankFaces x y := by
  obtain ⟨f, g, hfg, hfgAdj⟩ := flankFaces_latAdj hxy
  apply fci_faceEdgeEquiv.injective
  rw [fci_faceEdgeEquiv.apply_symm_apply, hfg,
    fci_faceEdgeEquiv_mk_of_adj hfgAdj, ← symPrimal_eq_shared hfgAdj,
    ← symPrimalSym_mk, ← hfg, symPrimalSym_flankFaces hxy]


theorem rlc_mem_connectorCentralFaceClosureEdges_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : Site 2} (hxy : (hypercubicLattice 2).Adj x y) :
    s(x, y) ∈ rlc_connectorCentralFaceClosureEdges gamma gamma' ↔
      x ∈ rlc_connectorBox n ∧ y ∈ rlc_connectorBox n ∧
        ∃ f ∈ rlc_connectorCentralFaceRegion gamma gamma',
          f ∈ flankFaces x y := by
  rw [rlc_connectorCentralFaceClosureEdges, Finset.mem_filter]
  constructor
  · rintro ⟨hbox, f, hf, hfe⟩
    rw [mem_edgesWithinFinset] at hbox
    obtain ⟨u, hu, v, hv, huv⟩ := hbox
    have huv' : s(u, v) = s(x, y) := huv.symm
    have hends : (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
      simpa [Sym2.eq_iff] using huv'
    rcases hends with huvEq | huvEq
    · rcases huvEq with ⟨huv1, huv2⟩
      subst u
      subst v
      refine ⟨hu, hv, f, hf, ?_⟩
      rwa [rlc_fci_faceEdgeEquiv_symm_mk_of_adj hxy] at hfe
    · rcases huvEq with ⟨huv1, huv2⟩
      subst u
      subst v
      refine ⟨hv, hu, f, hf, ?_⟩
      rw [rlc_fci_faceEdgeEquiv_symm_mk_of_adj hxy] at hfe
      exact hfe
  · rintro ⟨hx, hy, f, hf, hflank⟩
    refine ⟨?_, f, hf, ?_⟩
    · rw [mem_edgesWithinFinset]
      exact ⟨x, hx, y, hy, rfl⟩
    · rw [rlc_fci_faceEdgeEquiv_symm_mk_of_adj hxy]
      exact hflank


theorem rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : Site 2} (hxy : (hypercubicLattice 2).Adj x y)
    (hx : x ∈ rlc_connectorBox n) (hy : y ∈ rlc_connectorBox n)
    {f : Site 2}
    (hf : f ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hflank : f ∈ flankFaces x y) :
    s(x, y) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  apply Finset.mem_union_left
  exact (rlc_mem_connectorCentralFaceClosureEdges_iff
    gamma gamma' hxy).2 ⟨hx, hy, f, hf, hflank⟩

theorem rlc_mem_connectorCentralFacePlanarEdges_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : Site 2} (hxy : (hypercubicLattice 2).Adj x y) :
    s(x, y) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ↔
      s(x, y) ∈ rlc_connectorFourTraceEdges gamma gamma' ∨
        (x ∈ rlc_connectorBox n ∧ y ∈ rlc_connectorBox n ∧
          ∃ f ∈ rlc_connectorCentralFaceRegion gamma gamma',
            f ∈ flankFaces x y) := by
  rw [rlc_connectorCentralFacePlanarEdges, Finset.mem_union,
    rlc_mem_connectorCentralFaceClosureEdges_iff gamma gamma' hxy]
  exact or_comm

theorem rlc_connectorCentralFaceEdges_eq_sdiff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_connectorCentralFaceEdges gamma gamma' =
      rlc_connectorCentralFaceClosureEdges gamma gamma' \
        rlc_connectorFourTraceEdges gamma gamma' := rfl

theorem rlc_connectorCentralFaceEdges_disjoint_fourTrace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Disjoint (rlc_connectorCentralFaceEdges gamma gamma')
      (rlc_connectorFourTraceEdges gamma gamma') := by
  rw [Finset.disjoint_left]
  intro e heFace heTrace
  exact (Finset.mem_sdiff.mp heFace).2 heTrace

theorem rlc_connectorCentralFaceEdge_endpoints_mem_box {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)} (he : e ∈
      rlc_connectorCentralFaceEdges gamma gamma') {z : Site 2}
    (hz : z ∈ e) : z ∈ rlc_connectorBox n := by
  have heClosure := (Finset.mem_sdiff.mp he).1
  have heBox := (Finset.mem_filter.mp heClosure).1
  rw [mem_edgesWithinFinset] at heBox
  obtain ⟨x, hx, y, hy, hxy⟩ := heBox
  subst e
  rw [Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · exact hx
  · exact hy

theorem rlc_connectorCentralFaceClosureEdge_endpoints_mem_box {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)} (he : e ∈
      rlc_connectorCentralFaceClosureEdges gamma gamma') {z : Site 2}
    (hz : z ∈ e) : z ∈ rlc_connectorBox n := by
  have heBox := (Finset.mem_filter.mp he).1
  rw [mem_edgesWithinFinset] at heBox
  obtain ⟨x, hx, y, hy, hxy⟩ := heBox
  subst e
  rw [Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · exact hx
  · exact hy


theorem rlc_connectorCentralFacePlanarEdge_endpoints_mem_box {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma')
    {z : Site 2} (hz : z ∈ e) : z ∈ rlc_connectorBox n := by
  rw [rlc_connectorCentralFacePlanarEdges, Finset.mem_union] at he
  rcases he with hclosure | htrace
  · exact rlc_connectorCentralFaceClosureEdge_endpoints_mem_box
      gamma gamma' hclosure hz
  · rw [rlc_connectorFourTraceEdges, Finset.mem_union] at htrace
    rcases htrace with hexposed | hreflected
    · induction e using Sym2.inductionOn with
      | _ x y =>
          have hends := rlc_exposedPathEdges_endpoints_mem_box
            (gamma := gamma) (gamma' := gamma') (v := x) (w := y) hexposed
          rw [Sym2.mem_iff] at hz
          rcases hz with rfl | rfl
          · simpa [rlc_connectorBox] using hends.1
          · simpa [rlc_connectorBox] using hends.2
    · rw [rlc_connectorReflectedTraceEdges, Finset.mem_union] at hreflected
      rcases hreflected with hright | hleft
      · simpa [rlc_connectorBox] using
          rlc_reflectedRightPathEdge_endpoint_mem_box gamma hright hz
      · simpa [rlc_connectorBox] using
          rlc_reflectedLeftPathEdge_endpoint_mem_box gamma' hleft hz


end
end StatMech.Universality
