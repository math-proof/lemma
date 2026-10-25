/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_faceBoundaryEdge_exists_reflectedFilledCutEdge {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g) :
    ∃ e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n),
      Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e =
          sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) ∧
        e ∈ rlc_connectorReflectedFilledCut gamma gamma' rho := by
  obtain ⟨p, q, hpq, hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hbd : bdEdge
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) s(p, q) := by
    rw [← hpq]
    exact hfg.2
  obtain ⟨hpBox, hqBox⟩ :=
    rlc_reflectedFilledBoundary_endpoints_mem_crossedBox
      hn gamma gamma' rho hpqAdj hbd
  let rp : (rlc_connectorCrossedBoxPlanar n).V :=
    ⟨rlc_primalDualReflect p, hpBox⟩
  let rq : (rlc_connectorCrossedBoxPlanar n).V :=
    ⟨rlc_primalDualReflect q, hqBox⟩
  have hrpqAdj : (hypercubicLattice 2).Adj
      (rlc_primalDualReflect p) (rlc_primalDualReflect q) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpqAdj ⊢
    simp only [rlc_primalDualReflect_zero, rlc_primalDualReflect_one]
    omega
  have hrprq : (rlc_connectorCrossedBoxPlanar n).G.Adj rp rq :=
    hrpqAdj
  let e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n) :=
    ⟨s(rp, rq), (SimpleGraph.mem_edgeSet _).mpr hrprq⟩
  refine ⟨e, ?_, ?_⟩
  · calc
      Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e =
          s(rlc_primalDualReflect p, rlc_primalDualReflect q) := by
            rfl
      _ = Sym2.map rlc_primalDualReflect (sharedPrimalEdge f g) := by
        rw [hpq]
        rfl
      _ = sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) :=
        rlc_sharedPrimalEdge_dualReflect hfg.1
  · rw [rlc_connectorReflectedFilledCut, Ising.kwg_mem_cutSet]
    change Ising.kwg_isSplit
      (rlc_connectorReflectedFilledColour gamma gamma' rho) s(rp, rq)
    rw [Ising.kwg_isSplit_mk]
    rw [bdEdge_mk] at hbd
    by_cases hp : p ∈
        rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
    · have hq : q ∉
          rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := hbd.mp hp
      simp [rlc_connectorReflectedFilledColour, rp, rq, hp, hq]
    · have hq : q ∈
          rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
        by_contra hq
        exact hp (hbd.mpr hq)
      simp [rlc_connectorReflectedFilledColour, rp, rq, hp, hq]


theorem rlc_reflectedFilledCutEdge_dualEnds_eq_carrierComponents {n : Int}
    {f g : Site 2} (hfg : (hypercubicLattice 2).Adj f g)
    (e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n))
    (he : Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e =
      sharedPrimalEdge f g) :
    Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e =
      s((whb_faceRegion
          (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk f,
        (whb_faceRegion
          (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk g) := by
  let P := rlc_connectorCrossedBoxPlanar n
  have hpair : s(Ising.kwg_flankLeft P e, Ising.kwg_flankRight P e) =
      s(f, g) :=
    (jce_sharedPrimalEdge_inj (Ising.kwg_flanks_adj P e) hfg).mpr
      ((Ising.kwg_flanks_shared P e).trans he)
  unfold Ising.kwg_dualEnds
  rw [Sym2.eq_iff] at hpair ⊢
  rcases hpair with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · exact Or.inl ⟨congrArg _ hleft, congrArg _ hright⟩
  · exact Or.inr ⟨congrArg _ hleft, congrArg _ hright⟩


end
end StatMech.Universality
