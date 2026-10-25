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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part4
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_connectorReflectedFilledCut_isEven {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    Ising.kwg_IsEven
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n))
      (rlc_connectorReflectedFilledCut gamma gamma' rho) := by
  exact Ising.kwg_primalCut_isEven (rlc_connectorCrossedBoxPlanar n)
    (rlc_connectorReflectedFilledColour gamma gamma' rho)


theorem rlc_mem_reflectedFilledCut_iff_bdEdge_embedded {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)) :
    e ∈ rlc_connectorReflectedFilledCut gamma gamma' rho ↔
      bdEdge
        (rlc_reflectedPrimalRegion
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))
        (Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e) := by
  classical
  rw [rlc_connectorReflectedFilledCut, Ising.kwg_mem_cutSet]
  rcases e with ⟨ep, hep⟩
  induction ep using Sym2.inductionOn with
  | _ x y =>
      change
        ((decide (x.1 ∈ rlc_reflectedPrimalRegion
              (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)) : Bool) ≠
            decide (y.1 ∈ rlc_reflectedPrimalRegion
              (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))) ↔
          bdEdge
            (rlc_reflectedPrimalRegion
              (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))
            s(x.1, y.1)
      rw [bdEdge_mk]
      by_cases hx : x.1 ∈ rlc_reflectedPrimalRegion
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) <;>
        by_cases hy : y.1 ∈ rlc_reflectedPrimalRegion
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) <;>
        simp [hx, hy]


theorem rlc_reflectedFilledBoundary_endpoints_mem_crossedBox {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {p q : Site 2}
    (hpq : (hypercubicLattice 2).Adj p q)
    (hbd : bdEdge
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) s(p, q)) :
    rlc_primalDualReflect p ∈
        rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2) ∧
      rlc_primalDualReflect q ∈
        rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2) := by
  have near_of_mem {x y : Site 2}
      (hxy : (hypercubicLattice 2).Adj x y)
      (hx : x ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) :
      rlc_primalDualReflect x ∈
          rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2) ∧
        rlc_primalDualReflect y ∈
          rect (-2 * n - 1) (2 * n + 1) (-n) (n + 2) := by
    have hxBox :=
      rlc_connectorCentralFaceFilledReachSet_subset_connectorRect
        hn gamma gamma' rho hx
    rw [mem_rect] at hxBox
    change
      ((-2 * n - 1 ≤ -x 0 ∧ -x 0 ≤ 2 * n + 1 ∧
          -n ≤ x 1 + 1 ∧ x 1 + 1 ≤ n + 2) ∧
        (-2 * n - 1 ≤ -y 0 ∧ -y 0 ≤ 2 * n + 1 ∧
          -n ≤ y 1 + 1 ∧ y 1 + 1 ≤ n + 2))
    rcases adj_cases hxy with ⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩
    all_goals omega
  rw [bdEdge_mk] at hbd
  by_cases hp : p ∈
      rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  · exact near_of_mem hpq hp
  · have hq : q ∈
        rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
      by_contra hq
      exact hp (hbd.mpr hq)
    exact (near_of_mem hpq.symm hq).symm


theorem rlc_reflectedFaceBoundary_endpoints_mem_crossedBoxInterior {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g) :
    rlc_dualReflect f ∈
        rect (-2 * n - 1) (2 * n) (-n) (n + 1) ∧
      rlc_dualReflect g ∈
        rect (-2 * n - 1) (2 * n) (-n) (n + 1) := by
  obtain ⟨p, q, hpq, _hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hbd : bdEdge
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) s(p, q) := by
    rw [← hpq]
    exact hfg.2
  rw [bdEdge_mk] at hbd
  by_cases hp : p ∈
      rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  · apply rlc_reflectedCarrierFaces_mem_crossedBoxInterior hfg.1
    · rw [hpq, Sym2.mem_iff]
      exact Or.inl rfl
    · exact rlc_connectorCentralFaceFilledReachSet_subset_connectorRect
        hn gamma gamma' rho hp
  · have hq : q ∈
        rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
      by_contra hq
      exact hp (hbd.mpr hq)
    apply rlc_reflectedCarrierFaces_mem_crossedBoxInterior hfg.1
    · rw [hpq, Sym2.mem_iff]
      exact Or.inr rfl
    · exact rlc_connectorCentralFaceFilledReachSet_subset_connectorRect
        hn gamma gamma' rho hq


theorem rlc_sharedPrimalEdge_dualReflect {f g : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g) :
    Sym2.map rlc_primalDualReflect (sharedPrimalEdge f g) =
      sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) := by
  rcases face_adj_dir hfg with rfl | rfl | rfl | rfl <;>
    simp [sharedPrimalEdge, rlc_primalDualReflect,
      rlc_primalDualReflectFun, rlc_dualReflect, rlc_dualReflectFun]
  all_goals try split_ifs <;> try omega
  all_goals try simp [Sym2.eq_iff]
  all_goals ring


theorem rlc_reflectedFilledCutEdge_exists_faceBoundaryCarrier {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n))
    (heCut : e ∈ rlc_connectorReflectedFilledCut gamma gamma' rho) :
    ∃ f g : Site 2,
      (faceBoundaryGraph
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g ∧
        Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e =
          sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) := by
  let P := rlc_connectorCrossedBoxPlanar n
  let F := Ising.kwg_flankLeft P e
  let G := Ising.kwg_flankRight P e
  let f := rlc_dualReflect.symm F
  let g := rlc_dualReflect.symm G
  have hFG : (hypercubicLattice 2).Adj F G := Ising.kwg_flanks_adj P e
  have hfg : (hypercubicLattice 2).Adj f g := by
    apply (rlc_adj_dualReflect f g).mpr
    simpa [f, g, F, G]
  have hsharedFG : sharedPrimalEdge F G =
      Ising.kwg_embeddedEdge P e := Ising.kwg_flanks_shared P e
  have hmap : Sym2.map rlc_primalDualReflect (sharedPrimalEdge f g) =
      Ising.kwg_embeddedEdge P e := by
    calc
      Sym2.map rlc_primalDualReflect (sharedPrimalEdge f g) =
          sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) :=
        rlc_sharedPrimalEdge_dualReflect hfg
      _ = sharedPrimalEdge F G := by simp [f, g, F, G]
      _ = Ising.kwg_embeddedEdge P e := hsharedFG
  have hbdRef :=
    (rlc_mem_reflectedFilledCut_iff_bdEdge_embedded gamma gamma' rho e).mp
      heCut
  have hbd : bdEdge
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)
      (sharedPrimalEdge f g) := by
    rw [← hmap] at hbdRef
    exact (rlc_bdEdge_reflectedPrimalRegion_map _ _).mp hbdRef
  refine ⟨f, g, ⟨hfg, hbd⟩, ?_⟩
  calc
    Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e =
        sharedPrimalEdge F G := hsharedFG.symm
    _ = sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) := by
      simp [f, g, F, G]


end
end StatMech.Universality
