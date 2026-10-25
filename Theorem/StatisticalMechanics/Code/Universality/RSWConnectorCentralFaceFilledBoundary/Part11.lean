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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part7
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_reflectedFilledCut_incident_component_ne_outer {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)}
    (heCut : e ∈ rlc_connectorReflectedFilledCut gamma gamma' rho)
    {C : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n)}
    (hinc : Ising.kwg_incidentMod2 C
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e)) :
    C ≠ rlc_crossedBoxOuterFace n := by
  have hCInt := rlc_reflectedFilledCut_incident_component_out_mem_interior
    hn gamma gamma' rho heCut hinc
  intro houter
  have hcomp : (whb_faceRegion
        (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk C.out =
      (whb_faceRegion
        (imageGraph (rlc_connectorCrossedBoxPlanar n))).connectedComponentMk
          (![-2 * n - 2, -n - 1] : Site 2) := by
    calc
      _ = C := C.out_eq
      _ = rlc_crossedBoxOuterFace n := houter
      _ = _ := rfl
  have hout := rlc_crossedBox_interiorFace_component_singleton hCInt hcomp
  have h0 := congrArg (fun x : Site 2 => x 0) hout
  rw [mem_rect] at hCInt
  simp only [Matrix.cons_val_zero] at h0
  omega


theorem rlc_minimalReflectedCutPiece_carrierReachable {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (S : Finset (Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)))
    (hSsub : S ⊆ rlc_connectorReflectedFilledCut gamma gamma' rho)
    (hSmin : RlcCentralFaceMinimalReflectedCutPiece S)
    {C D : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n)}
    (hCinc : ∃ e ∈ S, Ising.kwg_incidentMod2 C
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e))
    (hDinc : ∃ e ∈ S, Ising.kwg_incidentMod2 D
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e)) :
    (rlc_reflectedFilledBoundaryGraph gamma gamma' rho).Reachable C.out D.out := by
  obtain ⟨eC, heCS, heCinc⟩ := hCinc
  obtain ⟨eD, heDS, heDinc⟩ := hDinc
  have hCout : C ≠ rlc_crossedBoxOuterFace n :=
    rlc_reflectedFilledCut_incident_component_ne_outer
      hn gamma gamma' rho (hSsub heCS) heCinc
  have hDout : D ≠ rlc_crossedBoxOuterFace n :=
    rlc_reflectedFilledCut_incident_component_ne_outer
      hn gamma gamma' rho (hSsub heDS) heDinc
  have hdual := Ising.kwg_minimalEvenFinset_nonOuter_reachable
    (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n)) S
      (rlc_crossedBoxOuterFace n) hSmin.1 hSmin.2.1 hSmin.2.2
      hCout hDout ⟨eC, heCS, heCinc⟩ ⟨eD, heDS, heDinc⟩
  let forgetOuter : Ising.kwg_deleteVertexGraph
        (Ising.kwg_faceSupportGraph
          (fun e : ↑S => Ising.kwg_dualEnds
            (rlc_connectorCrossedBoxPlanar n) e.1))
        (rlc_crossedBoxOuterFace n) →g
      Ising.kwg_faceSupportGraph
        (fun e : ↑S => Ising.kwg_dualEnds
          (rlc_connectorCrossedBoxPlanar n) e.1) :=
    { toFun := id
      map_rel' := fun {_ _} h => h.1 }
  have hsupport := hdual.map forgetOuter
  simpa [forgetOuter] using hsupport.map
    (rlc_reflectedCutSupportHom hn gamma gamma' rho S hSsub)


theorem rlc_minimalReflectedCutPiece_boundaryCarriers_reachable {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (S : Finset (Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)))
    (hSsub : S ⊆ rlc_connectorReflectedFilledCut gamma gamma' rho)
    (hSmin : RlcCentralFaceMinimalReflectedCutPiece S)
    {f g p q : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g)
    (hpq : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj p q)
    {e e' : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n)}
    (heS : e ∈ S) (he'S : e' ∈ S)
    (he : Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e =
      sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g))
    (he' : Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e' =
      sharedPrimalEdge (rlc_dualReflect p) (rlc_dualReflect q)) :
    (rlc_reflectedFilledBoundaryGraph gamma gamma' rho).Reachable
      (rlc_dualReflect f) (rlc_dualReflect p) := by
  let R := whb_faceRegion (imageGraph (rlc_connectorCrossedBoxPlanar n))
  let Cf : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n) :=
    R.connectedComponentMk (rlc_dualReflect f)
  let Cg : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n) :=
    R.connectedComponentMk (rlc_dualReflect g)
  let Cp : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n) :=
    R.connectedComponentMk (rlc_dualReflect p)
  let Cq : Ising.kwg_Face (rlc_connectorCrossedBoxPlanar n) :=
    R.connectedComponentMk (rlc_dualReflect q)
  obtain ⟨hfInt, hgInt⟩ :=
    rlc_reflectedFaceBoundary_endpoints_mem_crossedBoxInterior
      hn gamma gamma' rho hfg
  obtain ⟨hpInt, hqInt⟩ :=
    rlc_reflectedFaceBoundary_endpoints_mem_crossedBoxInterior
      hn gamma gamma' rho hpq
  have hCfCg : Cf ≠ Cg := by
    intro hEq
    have hrefEq : rlc_dualReflect f = rlc_dualReflect g :=
      rlc_crossedBox_interiorFace_component_singleton hfInt hEq
    exact hfg.1.ne (rlc_dualReflect.injective hrefEq)
  have hCpCq : Cp ≠ Cq := by
    intro hEq
    have hrefEq : rlc_dualReflect p = rlc_dualReflect q :=
      rlc_crossedBox_interiorFace_component_singleton hpInt hEq
    exact hpq.1.ne (rlc_dualReflect.injective hrefEq)
  have heEnds : Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e =
      s(Cf, Cg) := by
    exact rlc_reflectedFilledCutEdge_dualEnds_eq_carrierComponents
      ((rlc_adj_dualReflect f g).mp hfg.1) e he
  have he'Ends : Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e' =
      s(Cp, Cq) := by
    exact rlc_reflectedFilledCutEdge_dualEnds_eq_carrierComponents
      ((rlc_adj_dualReflect p q).mp hpq.1) e' he'
  have hCfInc : Ising.kwg_incidentMod2 Cf
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e) := by
    rw [heEnds, Ising.kwg_incidentMod2_mk]
    exact Or.inl ⟨rfl, hCfCg.symm⟩
  have hCpInc : Ising.kwg_incidentMod2 Cp
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n) e') := by
    rw [he'Ends, Ising.kwg_incidentMod2_mk]
    exact Or.inl ⟨rfl, hCpCq.symm⟩
  have hreach := rlc_minimalReflectedCutPiece_carrierReachable
    hn gamma gamma' rho S hSsub hSmin
      (C := Cf) (D := Cp) ⟨e, heS, hCfInc⟩ ⟨e', he'S, hCpInc⟩
  have hCfOut : Cf.out = rlc_dualReflect f := by
    symm
    apply rlc_crossedBox_interiorFace_component_singleton hfInt
    exact Cf.out_eq.symm
  have hCpOut : Cp.out = rlc_dualReflect p := by
    symm
    apply rlc_crossedBox_interiorFace_component_singleton hpInt
    exact Cp.out_eq.symm
  simpa [hCfOut, hCpOut] using hreach


theorem rlc_faceBoundaryEdge_exists_minimalReflectedCutPeel {n : Int}
    (hn : 0 < n) (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g) :
    ∃ (e : Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n))
      (S R : Finset (Ising.kwg_Edge (rlc_connectorCrossedBoxPlanar n))),
      Ising.kwg_embeddedEdge (rlc_connectorCrossedBoxPlanar n) e =
          sharedPrimalEdge (rlc_dualReflect f) (rlc_dualReflect g) ∧
        S ⊆ rlc_connectorReflectedFilledCut gamma gamma' rho ∧
        e ∈ S ∧ RlcCentralFaceMinimalReflectedCutPiece S ∧
        R = rlc_connectorReflectedFilledCut gamma gamma' rho \ S ∧
        Ising.kwg_IsEven
          (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n)) R ∧
        Disjoint S R ∧
        S ∪ R = rlc_connectorReflectedFilledCut gamma gamma' rho := by
  obtain ⟨e, heEmbedded, heCut⟩ :=
    rlc_faceBoundaryEdge_exists_reflectedFilledCutEdge
      hn gamma gamma' rho hfg
  obtain ⟨S, R, hSCut, heS, hSne, hSeven, hSmin,
      hR, hReven, hdisjoint, hunion⟩ :=
    Ising.kwg_exists_minimalEvenFinset_peel_mem
      (Ising.kwg_dualEnds (rlc_connectorCrossedBoxPlanar n)) heCut
      (rlc_connectorReflectedFilledCut_isEven gamma gamma' rho)
  exact ⟨e, S, R, heEmbedded, hSCut, heS,
    ⟨hSne, hSeven, hSmin⟩, hR, hReven, hdisjoint, hunion⟩


theorem rlc_sharedPrimalEdge_eq_unshift_flankFaces {x y : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y) :
    sharedPrimalEdge x y =
      Sym2.map phb_doubleDualEquiv.symm (flankFaces x y) := by
  rcases face_adj_dir hxy with rfl | rfl | rfl | rfl <;>
    simp [sharedPrimalEdge, flankFaces, phb_doubleDualEquiv]
  all_goals try split_ifs <;> try omega
  all_goals try simp [Sym2.eq_iff]
  all_goals ring


theorem rlc_map_flankFaces_primalDualReflect_symm {p q : Site 2}
    (hpq : (hypercubicLattice 2).Adj p q) :
    Sym2.map rlc_dualReflect
        (flankFaces (rlc_primalDualReflect.symm p)
          (rlc_primalDualReflect.symm q)) =
      flankFaces p q := by
  rcases face_adj_dir hpq with rfl | rfl | rfl | rfl <;>
    simp [flankFaces, rlc_dualReflect, rlc_dualReflectFun,
      rlc_primalDualReflect, rlc_primalDualReflectInvFun, Sym2.eq_iff]
  all_goals try split_ifs <;> try omega
  all_goals
    rw [Sym2.map_mk, Sym2.eq_iff]
    left
    constructor <;> ext i <;> fin_cases i <;>
      simp [rlc_dualReflect, rlc_dualReflectFun]


theorem rlc_sharedPrimalEdge_endpoint_mem_connectorBox_of_faceBox
    {n : Int} {f g x : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g)
    (hfBox : f ∈ rlc_connectorFaceBox n)
    (_hgBox : g ∈ rlc_connectorFaceBox n)
    (hx : x ∈ sharedPrimalEdge f g) :
    x ∈ rlc_connectorBox n := by
  have hfRect : f ∈ rect (-2 * n) (2 * n - 1) (-n) (n - 1) := by
    simpa [rlc_connectorFaceBox] using hfBox
  obtain ⟨p, q, hshared, _hpq, hpBox, hqBox⟩ :=
    rlc_faceInterior_sharedPrimalEdge_endpoints_mem_rect hfRect hfg
  rw [hshared, Sym2.mem_iff] at hx
  rcases hx with rfl | rfl
  · simpa [rlc_connectorBox] using hpBox
  · simpa [rlc_connectorBox] using hqBox


theorem RlcCentralFaceRetainedAnchoredBoundary.reflectedContour_covers_leftRegionBoundary
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    {p q : Site 2} (hpq : (hypercubicLattice 2).Adj p q)
    (hbd : bdEdge
      (jec_leftRegion ((B.contour.mapLe
        (faceBoundaryGraph_le
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
            rlc_dualReflectLatticeHom)) s(p, q)) :
    flankFaces p q ∈
      ((B.contour.mapLe
        (faceBoundaryGraph_le
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
            rlc_dualReflectLatticeHom).edges := by
  let p0 := rlc_primalDualReflect.symm p
  let q0 := rlc_primalDualReflect.symm q
  have hpq0 : (hypercubicLattice 2).Adj p0 q0 := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpq ⊢
    simp only [p0, q0, rlc_primalDualReflect_symm_zero,
      rlc_primalDualReflect_symm_one]
    omega
  have hbdRef : bdEdge
      (rlc_reflectedPrimalRegion
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))
      s(p, q) := by
    rwa [B.reflectedFilledReachSet_eq_leftRegion]
  have hmap : Sym2.map rlc_primalDualReflect s(p0, q0) = s(p, q) := by
    simp [p0, q0]
  have hbd0 : bdEdge
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) s(p0, q0) := by
    apply (rlc_bdEdge_reflectedPrimalRegion_map
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) s(p0, q0)).mp
    rwa [hmap]
  have hflankEdge : flankFaces p0 q0 ∈
      (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).edgeSet :=
    (phb_flankFaces_mem_faceBoundaryGraph_iff hpq0).2 hbd0
  have hflankContour : flankFaces p0 q0 ∈ B.contour.edges :=
    B.contour_covers _ hflankEdge
  rw [SimpleGraph.Walk.edges_map, List.mem_map]
  refine ⟨flankFaces p0 q0, ?_, ?_⟩
  · simpa [SimpleGraph.Walk.edges_mapLe_eq_edges] using hflankContour
  · simpa [p0, q0] using rlc_map_flankFaces_primalDualReflect_symm hpq


theorem RlcCentralFaceRetainedAnchoredBoundary.reflectedContour_edge_sideToggle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    {f g : Site 2} (hfg : s(f, g) ∈ B.contour.edges) :
    let C := (B.contour.mapLe
      (faceBoundaryGraph_le
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
          rlc_dualReflectLatticeHom
    ∃ p q : Site 2,
      sharedPrimalEdge f g = s(p, q) ∧
        (hypercubicLattice 2).Adj p q ∧
        (((rlc_primalDualReflect p ∈ jec_leftRegion C) ∧
            rlc_primalDualReflect q ∉ jec_leftRegion C) ∨
          (rlc_primalDualReflect p ∉ jec_leftRegion C ∧
            rlc_primalDualReflect q ∈ jec_leftRegion C)) := by
  dsimp only
  have hfgAdj := B.contour.adj_of_mem_edges hfg
  obtain ⟨p, q, hpq, hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hfgAdj.1
  refine ⟨p, q, hpq, hpqAdj, ?_⟩
  have hpqBoundary : bdEdge
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) s(p, q) := by
    rw [← hpq]
    exact hfgAdj.2
  rw [bdEdge_mk] at hpqBoundary
  have hregion := B.reflectedFilledReachSet_eq_leftRegion
  have hp_mem : rlc_primalDualReflect p ∈
      rlc_reflectedPrimalRegion
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) ↔
      p ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
    rw [rlc_mem_reflectedPrimalRegion_iff]
    simp
  have hq_mem : rlc_primalDualReflect q ∈
      rlc_reflectedPrimalRegion
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho) ↔
      q ∈ rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
    rw [rlc_mem_reflectedPrimalRegion_iff]
    simp
  rw [hregion] at hp_mem hq_mem
  by_cases hp : p ∈
      rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  · left
    refine ⟨hp_mem.mpr hp, ?_⟩
    intro hq
    exact (hpqBoundary.mp hp) (hq_mem.mp hq)
  · right
    have hq : q ∈
        rlc_connectorCentralFaceFilledReachSet gamma gamma' rho := by
      by_contra hq
      exact hp (hpqBoundary.mpr hq)
    exact ⟨fun hp' => hp (hp_mem.mp hp'), hq_mem.mpr hq⟩


theorem RlcCentralFaceRetainedAnchoredBoundary.reflectedContour_edge_shiftedFlank_sideToggle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    {f g : Site 2} (hfg : s(f, g) ∈ B.contour.edges) :
    let C := (B.contour.mapLe
      (faceBoundaryGraph_le
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
          rlc_dualReflectLatticeHom
    ∃ h k : Site 2,
      flankFaces (rlc_dualReflect f) (rlc_dualReflect g) = s(h, k) ∧
        (((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C) ∧
            phb_doubleDualEquiv.symm k ∉ jec_leftRegion C) ∨
          (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧
            phb_doubleDualEquiv.symm k ∈ jec_leftRegion C)) := by
  dsimp only
  obtain ⟨p, q, hpq, _hpqAdj, hside⟩ :=
    B.reflectedContour_edge_sideToggle hfg
  have hfgAdj := B.contour.adj_of_mem_edges hfg
  have hrefAdj : (hypercubicLattice 2).Adj
      (rlc_dualReflect f) (rlc_dualReflect g) :=
    (rlc_adj_dualReflect f g).mp hfgAdj.1
  obtain ⟨h, k, hflank, _hkAdj⟩ := flankFaces_latAdj hrefAdj
  refine ⟨h, k, hflank, ?_⟩
  have hsites : s(rlc_primalDualReflect p, rlc_primalDualReflect q) =
      s(phb_doubleDualEquiv.symm h,
        phb_doubleDualEquiv.symm k) := by
    calc
      s(rlc_primalDualReflect p, rlc_primalDualReflect q) =
          Sym2.map rlc_primalDualReflect (sharedPrimalEdge f g) := by
            rw [hpq]
            rfl
      _ = sharedPrimalEdge (rlc_dualReflect f)
          (rlc_dualReflect g) := rlc_sharedPrimalEdge_dualReflect hfgAdj.1
      _ = Sym2.map phb_doubleDualEquiv.symm
          (flankFaces (rlc_dualReflect f) (rlc_dualReflect g)) :=
            rlc_sharedPrimalEdge_eq_unshift_flankFaces hrefAdj
      _ = s(phb_doubleDualEquiv.symm h,
          phb_doubleDualEquiv.symm k) := by rw [hflank]; rfl
  rw [Sym2.eq_iff] at hsites
  rcases hsites with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · simpa [← hp, ← hq] using hside
  · rcases hside with hside | hside
    · exact Or.inr ⟨by simpa [← hq] using hside.2,
        by simpa [← hp] using hside.1⟩
    · exact Or.inl ⟨by simpa [← hq] using hside.2,
        by simpa [← hp] using hside.1⟩


theorem RlcCentralFaceRetainedAnchoredBoundary.reflectedBoundaryEdge_namedFlank_sideToggle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    {f g h : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g)
    (hh : h ∈ flankFaces (rlc_dualReflect f) (rlc_dualReflect g)) :
    let C := (B.contour.mapLe
      (faceBoundaryGraph_le
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
          rlc_dualReflectLatticeHom
    ∃ k : Site 2,
      flankFaces (rlc_dualReflect f) (rlc_dualReflect g) = s(h, k) ∧
        (((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C) ∧
            phb_doubleDualEquiv.symm k ∉ jec_leftRegion C) ∨
          (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧
            phb_doubleDualEquiv.symm k ∈ jec_leftRegion C)) := by
  dsimp only
  have hfgContour : s(f, g) ∈ B.contour.edges :=
    B.contour_covers _ (by
      rw [SimpleGraph.mem_edgeSet]
      exact hfg)
  obtain ⟨a, b, hab, hside⟩ :=
    B.reflectedContour_edge_shiftedFlank_sideToggle hfgContour
  rw [hab, Sym2.mem_iff] at hh
  rcases hh with ha | hb
  · subst a
    exact ⟨b, hab, hside⟩
  · subst b
    refine ⟨a, ?_, ?_⟩
    · simpa [Sym2.eq_swap] using hab
    · rcases hside with hside | hside
      · exact Or.inr ⟨hside.2, hside.1⟩
      · exact Or.inl ⟨hside.2, hside.1⟩


theorem rlc_connectorCentralFaceRegion_reachable
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n} {h k : Site 2}
    (hh : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hk : k ∈ rlc_connectorCentralFaceRegion gamma gamma') :
    ∃ (hhBox : h ∈ rlc_connectorFaceBox n)
      (hkBox : k ∈ rlc_connectorFaceBox n),
      (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
        ⟨h, hhBox⟩ ⟨k, hkBox⟩ := by
  have hhSet : h ∈ rlc_connectorCentralFaceRegionSet gamma gamma' := by
    simpa [rlc_connectorCentralFaceRegion] using hh
  have hkSet : k ∈ rlc_connectorCentralFaceRegionSet gamma gamma' := by
    simpa [rlc_connectorCentralFaceRegion] using hk
  obtain ⟨hhBox, hsBox, hhReach⟩ := hhSet
  obtain ⟨hkBox, hsBox', hkReach⟩ := hkSet
  have hsEq : (⟨rlc_connectorCentralFace, hsBox⟩ :
      RlcConnectorFaceVertex n) = ⟨rlc_connectorCentralFace, hsBox'⟩ := rfl
  rw [hsEq] at hhReach
  exact ⟨hhBox, hkBox, hhReach.symm.trans hkReach⟩


theorem RlcCentralFaceRetainedAnchoredBoundary.pairedCentralIncomingFlanks_cutReachable_and_sideToggle
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    {t u h t' u' h' : Site 2}
    (htu : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj t u)
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hhFlank : h ∈ flankFaces (rlc_dualReflect t) (rlc_dualReflect u))
    (ht'u' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj t' u')
    (hh'Region : h' ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh'Flank : h' ∈ flankFaces
      (rlc_dualReflect t') (rlc_dualReflect u')) :
    ∃ (hhBox : h ∈ rlc_connectorFaceBox n)
      (hh'Box : h' ∈ rlc_connectorFaceBox n),
      (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
          ⟨h, hhBox⟩ ⟨h', hh'Box⟩ ∧
        ∃ k k' : Site 2,
          flankFaces (rlc_dualReflect t) (rlc_dualReflect u) = s(h, k) ∧
          flankFaces (rlc_dualReflect t') (rlc_dualReflect u') = s(h', k') ∧
          (let C := (B.contour.mapLe
            (faceBoundaryGraph_le
              (rlc_connectorCentralFaceFilledReachSet
                gamma gamma' rho))).map rlc_dualReflectLatticeHom
           (((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C) ∧
                phb_doubleDualEquiv.symm k ∉ jec_leftRegion C) ∨
              (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧
                phb_doubleDualEquiv.symm k ∈ jec_leftRegion C))) ∧
          (let C := (B.contour.mapLe
            (faceBoundaryGraph_le
              (rlc_connectorCentralFaceFilledReachSet
                gamma gamma' rho))).map rlc_dualReflectLatticeHom
           (((phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C) ∧
                phb_doubleDualEquiv.symm k' ∉ jec_leftRegion C) ∨
              (phb_doubleDualEquiv.symm h' ∉ jec_leftRegion C ∧
                phb_doubleDualEquiv.symm k' ∈ jec_leftRegion C))) := by
  obtain ⟨hhBox, hh'Box, hreach⟩ :=
    rlc_connectorCentralFaceRegion_reachable hhRegion hh'Region
  obtain ⟨k, hkFlank, hkSide⟩ :=
    B.reflectedBoundaryEdge_namedFlank_sideToggle htu hhFlank
  obtain ⟨k', hk'Flank, hk'Side⟩ :=
    B.reflectedBoundaryEdge_namedFlank_sideToggle ht'u' hh'Flank
  exact ⟨hhBox, hh'Box, hreach, k, k', hkFlank, hk'Flank,
    hkSide, hk'Side⟩


theorem RlcCentralFaceRetainedAnchoredBoundary.centralCutPath_hits_reflectedContour_of_oppositeSide
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    {h h' : Site 2} (hhBox : h ∈ rlc_connectorFaceBox n)
    (hh'Box : h' ∈ rlc_connectorFaceBox n)
    (hreach : (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
      ⟨h, hhBox⟩ ⟨h', hh'Box⟩)
    (hopposite :
      let C := (B.contour.mapLe
        (faceBoundaryGraph_le
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
            rlc_dualReflectLatticeHom
      ((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ∧
          phb_doubleDualEquiv.symm h' ∉ jec_leftRegion C) ∨
        (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧
          phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C))) :
    ∃ (z : RlcConnectorFaceVertex n) (f : Site 2),
      f ∈ B.contour.support ∧
        phb_doubleDualEquiv.symm z.1 = rlc_dualReflect f := by
  let C := (B.contour.mapLe
    (faceBoundaryGraph_le
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
        rlc_dualReflectLatticeHom
  let cutToLattice : rlc_connectorFiniteFaceCutGraph gamma gamma' →g
      hypercubicLattice 2 :=
    { toFun := fun z : RlcConnectorFaceVertex n => z.1
      map_rel' := fun {x y} hxy =>
        ((rlc_connectorFourTraceFaceCutGraph_adj
          gamma gamma' x.1 y.1).mp hxy).1 }
  let shiftUp : hypercubicLattice 2 →g hypercubicLattice 2 :=
    { toFun := phb_doubleDualEquiv.symm
      map_rel' := by
        intro x y hxy
        apply phb_doubleDualShift_latAdj.mp
        simpa [phb_doubleDualEquiv, phb_doubleDualShift] using hxy }
  obtain ⟨w⟩ := hreach
  let wShift := (w.map cutToLattice).map shiftUp
  have recover {x : Site 2} (hxC : x ∈ C.support)
      (hxW : x ∈ wShift.support) :
      ∃ (z : RlcConnectorFaceVertex n) (f : Site 2),
        f ∈ B.contour.support ∧
          phb_doubleDualEquiv.symm z.1 = rlc_dualReflect f := by
    change x ∈ ((B.contour.mapLe
      (faceBoundaryGraph_le
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
          rlc_dualReflectLatticeHom).support at hxC
    rw [SimpleGraph.Walk.support_map, List.mem_map,
      SimpleGraph.Walk.support_mapLe_eq_support] at hxC
    obtain ⟨f, hf, hfx⟩ := hxC
    change x ∈ ((w.map cutToLattice).map shiftUp).support at hxW
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hxW
    obtain ⟨y, hyW, hyx⟩ := hxW
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hyW
    obtain ⟨z, _hz, hzy⟩ := hyW
    refine ⟨z, f, hf, ?_⟩
    calc
      phb_doubleDualEquiv.symm z.1 = shiftUp (cutToLattice z) := rfl
      _ = shiftUp y := congrArg shiftUp hzy
      _ = x := hyx
      _ = rlc_dualReflect f := hfx.symm
  dsimp only at hopposite
  rcases hopposite with hopposite | hopposite
  · obtain ⟨p, q, hpq, hpqW⟩ := rlc_walk_mem_edgeBoundary_edges
      (jec_leftRegion C) wShift hopposite.1 hopposite.2
    have hon := jec_leftRegion_bdEdge_support C hpq.1 hpq.2
    rcases hon with hpC | hqC
    · exact recover hpC (wShift.fst_mem_support_of_mem_edges hpqW)
    · exact recover hqC (wShift.snd_mem_support_of_mem_edges hpqW)
  · obtain ⟨p, q, hpq, hpqW⟩ := rlc_walk_mem_edgeBoundary_edges
      (jec_leftRegion C) wShift.reverse (by simpa [wShift] using hopposite.2)
        (by simpa [wShift] using hopposite.1)
    have hon := jec_leftRegion_bdEdge_support C hpq.1 hpq.2
    have hpqForward : s(p, q) ∈ wShift.edges := by
      simpa [SimpleGraph.Walk.edges_reverse] using hpqW
    rcases hon with hpC | hqC
    · exact recover hpC (wShift.fst_mem_support_of_mem_edges hpqForward)
    · exact recover hqC (wShift.snd_mem_support_of_mem_edges hpqForward)


theorem RlcCentralFaceRetainedAnchoredBoundary.centralCutPath_goodContourEdge_of_oppositeSide
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    {h h' : Site 2}
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hhBox : h ∈ rlc_connectorFaceBox n)
    (hh'Box : h' ∈ rlc_connectorFaceBox n)
    (hreach : (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
      ⟨h, hhBox⟩ ⟨h', hh'Box⟩)
    (hopposite :
      let C := (B.contour.mapLe
        (faceBoundaryGraph_le
          (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
            rlc_dualReflectLatticeHom
      ((phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ∧
          phb_doubleDualEquiv.symm h' ∉ jec_leftRegion C) ∨
        (phb_doubleDualEquiv.symm h ∉ jec_leftRegion C ∧
          phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C))) :
    ∃ (f g : Site 2) (z z' : RlcConnectorFaceVertex n),
      s(f, g) ∈ B.contour.edges ∧
        (rlc_connectorFiniteFaceCutGraph gamma gamma').Adj z z' ∧
        z.1 ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
        z'.1 ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
        flankFaces (rlc_dualReflect f) (rlc_dualReflect g) = s(z.1, z'.1) ∧
        rlc_dualReflect f ∈ rlc_connectorBox n ∧
        rlc_dualReflect g ∈ rlc_connectorBox n ∧
        s(rlc_dualReflect f, rlc_dualReflect g) ∉
          rlc_connectorFourTraceEdges gamma gamma' := by
  let C := (B.contour.mapLe
    (faceBoundaryGraph_le
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
        rlc_dualReflectLatticeHom
  let cutToLattice : rlc_connectorFiniteFaceCutGraph gamma gamma' →g
      hypercubicLattice 2 :=
    { toFun := fun z : RlcConnectorFaceVertex n => z.1
      map_rel' := fun {x y} hxy =>
        ((rlc_connectorFourTraceFaceCutGraph_adj
          gamma gamma' x.1 y.1).mp hxy).1 }
  let shiftUp : hypercubicLattice 2 →g hypercubicLattice 2 :=
    { toFun := phb_doubleDualEquiv.symm
      map_rel' := by
        intro x y hxy
        apply phb_doubleDualShift_latAdj.mp
        simpa [phb_doubleDualEquiv, phb_doubleDualShift] using hxy }
  obtain ⟨w⟩ := hreach
  let wShift := (w.map cutToLattice).map shiftUp
  have recover {p q : Site 2}
      (hpqW : s(p, q) ∈ wShift.edges)
      (hpqBoundary : bdEdge (jec_leftRegion C) s(p, q)) :
      ∃ (f g : Site 2) (z z' : RlcConnectorFaceVertex n),
        s(f, g) ∈ B.contour.edges ∧
          (rlc_connectorFiniteFaceCutGraph gamma gamma').Adj z z' ∧
          z.1 ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
          z'.1 ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
          flankFaces (rlc_dualReflect f) (rlc_dualReflect g) = s(z.1, z'.1) ∧
          rlc_dualReflect f ∈ rlc_connectorBox n ∧
          rlc_dualReflect g ∈ rlc_connectorBox n ∧
          s(rlc_dualReflect f, rlc_dualReflect g) ∉
            rlc_connectorFourTraceEdges gamma gamma' := by
    have hpqAdj : (hypercubicLattice 2).Adj p q :=
      wShift.adj_of_mem_edges hpqW
    change s(p, q) ∈ ((w.map cutToLattice).map shiftUp).edges at hpqW
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at hpqW
    obtain ⟨e, heW, heShift⟩ := hpqW
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at heW
    obtain ⟨e0, he0W, heCut⟩ := heW
    induction e0 using Sym2.inductionOn with
    | _ z z' =>
        have hzzCut : (rlc_connectorFiniteFaceCutGraph gamma gamma').Adj z z' :=
          w.adj_of_mem_edges he0W
        have hzzData := (rlc_connectorFourTraceFaceCutGraph_adj
          gamma gamma' z.1 z'.1).mp hzzCut
        have hmapped : s(shiftUp (cutToLattice z),
            shiftUp (cutToLattice z')) = s(p, q) := by
          calc
            s(shiftUp (cutToLattice z), shiftUp (cutToLattice z')) =
                Sym2.map shiftUp (Sym2.map cutToLattice s(z, z')) := rfl
            _ = Sym2.map shiftUp e := congrArg (Sym2.map shiftUp) heCut
            _ = s(p, q) := heShift
        have hshift : flankFaces (shiftUp (cutToLattice z))
            (shiftUp (cutToLattice z')) = sharedPrimalEdge z.1 z'.1 := by
          have h := phb_sharedPrimalEdge_shift_eq_flankFaces
            (shiftUp.map_rel hzzData.1)
          calc
            flankFaces (shiftUp (cutToLattice z))
                (shiftUp (cutToLattice z')) =
                sharedPrimalEdge
                  (phb_doubleDualShift (shiftUp (cutToLattice z)))
                  (phb_doubleDualShift (shiftUp (cutToLattice z'))) := h.symm
            _ = sharedPrimalEdge z.1 z'.1 := by
              have hz : phb_doubleDualShift (shiftUp (cutToLattice z)) = z.1 := by
                change phb_doubleDualEquiv (phb_doubleDualEquiv.symm z.1) = z.1
                exact Equiv.apply_symm_apply _ _
              have hz' : phb_doubleDualShift (shiftUp (cutToLattice z')) = z'.1 := by
                change phb_doubleDualEquiv (phb_doubleDualEquiv.symm z'.1) = z'.1
                exact Equiv.apply_symm_apply _ _
              rw [hz, hz']
        have hflankCut : flankFaces p q = sharedPrimalEdge z.1 z'.1 := by
          calc
            flankFaces p q = flankFacesSym s(p, q) := by rw [flankFacesSym_mk]
            _ = flankFacesSym
                s(shiftUp (cutToLattice z), shiftUp (cutToLattice z')) :=
              congrArg flankFacesSym hmapped.symm
            _ = flankFaces (shiftUp (cutToLattice z))
                (shiftUp (cutToLattice z')) := flankFacesSym_mk _ _
            _ = sharedPrimalEdge z.1 z'.1 := hshift
        have hcontour := B.reflectedContour_covers_leftRegionBoundary
          hpqAdj hpqBoundary
        change flankFaces p q ∈ C.edges at hcontour
        dsimp only [C] at hcontour
        rw [SimpleGraph.Walk.edges_map, List.mem_map,
          SimpleGraph.Walk.edges_mapLe_eq_edges] at hcontour
        obtain ⟨e1, he1Contour, he1Map⟩ := hcontour
        induction e1 using Sym2.inductionOn with
        | _ f g =>
            have hcarrier : s(rlc_dualReflect f, rlc_dualReflect g) =
                sharedPrimalEdge z.1 z'.1 := by
              calc
                s(rlc_dualReflect f, rlc_dualReflect g) = flankFaces p q := by
                  simpa using he1Map
                _ = sharedPrimalEdge z.1 z'.1 := hflankCut
            have hflank : flankFaces (rlc_dualReflect f)
                (rlc_dualReflect g) = s(z.1, z'.1) := by
              calc
                flankFaces (rlc_dualReflect f) (rlc_dualReflect g) =
                    flankFacesSym s(rlc_dualReflect f,
                      rlc_dualReflect g) := by rw [flankFacesSym_mk]
                _ = flankFacesSym (sharedPrimalEdge z.1 z'.1) :=
                  congrArg flankFacesSym hcarrier
                _ = flankFacesSym (symPrimal z.1 z'.1) := by
                  rw [symPrimal_eq_shared hzzData.1]
                _ = s(z.1, z'.1) := flankFacesSym_symPrimal hzzData.1
            have hzW := w.fst_mem_support_of_mem_edges he0W
            have hz'W := w.snd_mem_support_of_mem_edges he0W
            have hzRegion := rlc_connectorCentralFaceRegion_of_cut_reachable
              gamma gamma' hhRegion hhBox z.2 ⟨w.takeUntil z hzW⟩
            have hz'Region := rlc_connectorCentralFaceRegion_of_cut_reachable
              gamma gamma' hhRegion hhBox z'.2 ⟨w.takeUntil z' hz'W⟩
            have hfShared : rlc_dualReflect f ∈
                sharedPrimalEdge z.1 z'.1 := by
              rw [← hcarrier, Sym2.mem_iff]
              exact Or.inl rfl
            have hgShared : rlc_dualReflect g ∈
                sharedPrimalEdge z.1 z'.1 := by
              rw [← hcarrier, Sym2.mem_iff]
              exact Or.inr rfl
            refine ⟨f, g, z, z', he1Contour, hzzCut, hzRegion,
              hz'Region, hflank, ?_, ?_, ?_⟩
            · exact rlc_sharedPrimalEdge_endpoint_mem_connectorBox_of_faceBox
                hzzData.1 z.2 z'.2 hfShared
            · exact rlc_sharedPrimalEdge_endpoint_mem_connectorBox_of_faceBox
                hzzData.1 z.2 z'.2 hgShared
            · rw [hcarrier]
              exact hzzData.2
  dsimp only at hopposite
  rcases hopposite with hopposite | hopposite
  · obtain ⟨p, q, hpq, hpqW⟩ := rlc_walk_mem_edgeBoundary_edges
      (jec_leftRegion C) wShift hopposite.1 hopposite.2
    exact recover hpqW hpq.2
  · obtain ⟨p, q, hpq, hpqW⟩ := rlc_walk_mem_edgeBoundary_edges
      (jec_leftRegion C) wShift.reverse (by simpa [wShift] using hopposite.2)
        (by simpa [wShift] using hopposite.1)
    have hpqForward : s(p, q) ∈ wShift.edges := by
      simpa [SimpleGraph.Walk.edges_reverse] using hpqW
    exact recover hpqForward hpq.2


theorem rlc_flank_mem_vertexLoop_support
    {x z h : Site 2} (hxz : (hypercubicLattice 2).Adj x z)
    (hh : h ∈ flankFaces x z) :
    h ∈ (jwc_vertexLoop (x 0) (x 1)).support := by
  rcases adj_cases hxz with ⟨hx0, hx1⟩ | ⟨hx1, hx0⟩
  · rcases hx1 with hx1 | hx1
    · unfold flankFaces at hh
      simp [hx0, hx1] at hh
      simp [jwc_vertexLoop]
      rcases hh with rfl | rfl <;> simp <;> omega
    · unfold flankFaces at hh
      simp [hx0, hx1] at hh
      simp [jwc_vertexLoop]
      rcases hh with rfl | rfl <;> simp <;> omega
  · rcases hx0 with hx0 | hx0
    · unfold flankFaces at hh
      simp [hx1, hx0] at hh
      simp [jwc_vertexLoop]
      rcases hh with rfl | rfl <;> simp <;> omega
    · unfold flankFaces at hh
      simp [hx1, hx0] at hh
      simp [jwc_vertexLoop]
      rcases hh with rfl | rfl <;> simp <;> omega


theorem rlc_vertexLoop_edges_mem_fourTraceFaceCutGraph
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) (x : Site 2)
    (hx : x ∉ rlc_connectorBarrier gamma gamma') :
    ∀ e ∈ (jwc_vertexLoop (x 0) (x 1)).edges,
      e ∈ (rlc_connectorFourTraceFaceCutGraph gamma gamma').edgeSet := by
  intro e he
  simp only [jwc_vertexLoop, SimpleGraph.Walk.edges_cons,
    SimpleGraph.Walk.edges_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [SimpleGraph.mem_edgeSet,
      rlc_connectorFourTraceFaceCutGraph_adj]
    refine ⟨jwc_faceAdj_NE_NW _ _, ?_⟩
    rw [jwc_shared_NE_NW]
    intro hwall
    apply hx
    exact rlc_mem_connectorBarrier_of_mem_fourTraceEdge gamma gamma'
      hwall (by
        rw [Sym2.mem_iff]
        left
        ext i
        fin_cases i <;> simp)
  · rw [SimpleGraph.mem_edgeSet,
      rlc_connectorFourTraceFaceCutGraph_adj]
    refine ⟨jwc_faceAdj_NW_SW _ _, ?_⟩
    rw [jwc_shared_NW_SW]
    intro hwall
    apply hx
    exact rlc_mem_connectorBarrier_of_mem_fourTraceEdge gamma gamma'
      hwall (by
        rw [Sym2.mem_iff]
        right
        ext i
        fin_cases i <;> simp)
  · rw [SimpleGraph.mem_edgeSet,
      rlc_connectorFourTraceFaceCutGraph_adj]
    refine ⟨jwc_faceAdj_SW_SE _ _, ?_⟩
    rw [jwc_shared_SW_SE]
    intro hwall
    apply hx
    exact rlc_mem_connectorBarrier_of_mem_fourTraceEdge gamma gamma'
      hwall (by
        rw [Sym2.mem_iff]
        right
        ext i
        fin_cases i <;> simp)
  · rw [SimpleGraph.mem_edgeSet,
      rlc_connectorFourTraceFaceCutGraph_adj]
    refine ⟨jwc_faceAdj_SE_NE _ _, ?_⟩
    rw [jwc_shared_SE_NE]
    intro hwall
    apply hx
    exact rlc_mem_connectorBarrier_of_mem_fourTraceEdge gamma gamma'
      hwall (by
        rw [Sym2.mem_iff]
        left
        ext i
        fin_cases i <;> simp)


theorem rlc_centralFaceRegion_flank_transfer_interior
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {x z y h k : Site 2}
    (hxz : (hypercubicLattice 2).Adj x z)
    (hxy : (hypercubicLattice 2).Adj x y)
    (hxInterior : -2 * n < x 0 ∧ x 0 < 2 * n ∧
      -n < x 1 ∧ x 1 < n)
    (hxNot : x ∉ rlc_connectorBarrier gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces x z) (hk : k ∈ flankFaces x y) :
    k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  let loop := jwc_vertexLoop (x 0) (x 1)
  have hloopBox : ∀ f ∈ loop.support, f ∈ rlc_connectorFaceBox n := by
    intro f hf
    dsimp only [loop] at hf
    simp only [jwc_vertexLoop, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;>
      simp [rlc_connectorFaceBox, mem_rect] <;> omega
  let cutLoop := loop.transfer
    (rlc_connectorFourTraceFaceCutGraph gamma gamma')
      (rlc_vertexLoop_edges_mem_fourTraceFaceCutGraph
        gamma gamma' x hxNot)
  have hhLoop : h ∈ loop.support := rlc_flank_mem_vertexLoop_support hxz hh
  have hkLoop : k ∈ loop.support := rlc_flank_mem_vertexLoop_support hxy hk
  have hhCut : h ∈ cutLoop.support := by
    simpa [cutLoop, SimpleGraph.Walk.support_transfer] using hhLoop
  have hkCut : k ∈ cutLoop.support := by
    simpa [cutLoop, SimpleGraph.Walk.support_transfer] using hkLoop
  let a := rlc_centralFaceContactSubwalk cutLoop hhCut hkCut
  have haBox : ∀ f ∈ a.support, f ∈ rlc_connectorFaceBox n := by
    intro f hf
    dsimp only [a] at hf
    rw [rlc_centralFaceContactSubwalk,
      SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse] at hf
    rcases hf with hf | hf
    · have hfCut := cutLoop.support_takeUntil_subset_support hhCut
          (by simpa using hf)
      exact hloopBox f (by
        simpa [cutLoop, SimpleGraph.Walk.support_transfer] using hfCut)
    · have hfCut := cutLoop.support_takeUntil_subset_support hkCut hf
      exact hloopBox f (by
        simpa [cutLoop, SimpleGraph.Walk.support_transfer] using hfCut)
  let aFinite := a.induce (rlc_connectorFaceBox n : Set (Site 2)) haBox
  have hhBox := hloopBox h hhLoop
  have hkBox := hloopBox k hkLoop
  have hreach : (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
      ⟨h, hhBox⟩ ⟨k, hkBox⟩ := ⟨aFinite⟩
  exact rlc_connectorCentralFaceRegion_of_cut_reachable
    gamma gamma' hhRegion hhBox hkBox hreach


theorem rlc_centralFaceRegion_other_flank_of_nonwall {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y h k : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y)
    (hnot : s(x, y) ∉ rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces x y) (hk : k ∈ flankFaces x y)
    (hkBox : k ∈ rlc_connectorFaceBox n) :
    k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  by_cases heq : h = k
  · simpa [heq] using hhRegion
  obtain ⟨f, g, hfg, hfgAdj⟩ := flankFaces_latAdj hxy
  have hshared : sharedPrimalEdge f g = s(x, y) := by
    rw [← symPrimal_eq_shared hfgAdj, ← symPrimalSym_mk,
      ← hfg, symPrimalSym_flankFaces hxy]
  rw [hfg, Sym2.mem_iff] at hh hk
  rcases hh with rfl | rfl <;> rcases hk with rfl | rfl
  · exact False.elim (heq rfl)
  · apply rlc_connectorCentralFaceRegion_of_cut_adj gamma gamma'
      hhRegion hkBox
    rw [rlc_connectorFourTraceFaceCutGraph_adj, hshared]
    exact ⟨hfgAdj, hnot⟩
  · apply rlc_connectorCentralFaceRegion_of_cut_adj gamma gamma'
      hhRegion hkBox
    rw [rlc_connectorFourTraceFaceCutGraph_adj,
      sharedPrimalEdge_comm_of_adj hfgAdj.symm, hshared]
    exact ⟨hfgAdj.symm, hnot⟩
  · exact False.elim (heq rfl)

set_option maxRecDepth 2000 in


theorem rlc_incident_flank_intersection_of_not_opposite
    {x a b : Site 2}
    (hxa : (hypercubicLattice 2).Adj x a)
    (hxb : (hypercubicLattice 2).Adj x b)
    (hab : a ≠ b)
    (hopp : ¬ (a 0 + b 0 = 2 * x 0 ∧
      a 1 + b 1 = 2 * x 1)) :
    ∃ k : Site 2, k ∈ flankFaces x a ∧ k ∈ flankFaces x b := by
  rcases face_adj_dir hxa with rfl | rfl | rfl | rfl <;>
    rcases face_adj_dir hxb with rfl | rfl | rfl | rfl
  all_goals
    simp [flankFaces] at hab hopp ⊢ <;>
    try omega
  all_goals
    rw [if_neg (by omega)] <;> simp


theorem rlc_flank_mem_connectorFaceBox_of_interior
    {n : Int} {x y h : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y)
    (hxInterior : -2 * n < x 0 ∧ x 0 < 2 * n ∧
      -n < x 1 ∧ x 1 < n)
    (hh : h ∈ flankFaces x y) :
    h ∈ rlc_connectorFaceBox n := by
  have hhLoop := rlc_flank_mem_vertexLoop_support hxy hh
  simp only [jwc_vertexLoop, SimpleGraph.Walk.support_cons,
    SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hhLoop
  rcases hhLoop with rfl | rfl | rfl | rfl | rfl <;>
    simp [rlc_connectorFaceBox, mem_rect] <;> omega


theorem rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x a b h : Site 2}
    (hxa : (hypercubicLattice 2).Adj x a)
    (hxb : (hypercubicLattice 2).Adj x b)
    (hab : a ≠ b)
    (hopp : ¬ (a 0 + b 0 = 2 * x 0 ∧
      a 1 + b 1 = 2 * x 1))
    (hxInterior : -2 * n < x 0 ∧ x 0 < 2 * n ∧
      -n < x 1 ∧ x 1 < n)
    (hnot : s(x, a) ∉ rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces x a) :
    s(x, b) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  obtain ⟨k, hkIn, hkOut⟩ :=
    rlc_incident_flank_intersection_of_not_opposite hxa hxb hab hopp
  have hkBox := rlc_flank_mem_connectorFaceBox_of_interior
    hxa hxInterior hkIn
  have hkRegion := rlc_centralFaceRegion_other_flank_of_nonwall
    gamma gamma' hxa hnot hhRegion hh hkIn hkBox
  apply rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank
    gamma gamma' hxb
  · simp [rlc_connectorBox, mem_rect]
    omega
  · simp [rlc_connectorBox, mem_rect]
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hxb
    omega
  · exact hkRegion
  · exact hkOut


theorem rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident_boxed
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x a b h : Site 2}
    (hxa : (hypercubicLattice 2).Adj x a)
    (hxb : (hypercubicLattice 2).Adj x b)
    (hab : a ≠ b)
    (hopp : ¬ (a 0 + b 0 = 2 * x 0 ∧
      a 1 + b 1 = 2 * x 1))
    (hxBox : x ∈ rlc_connectorBox n)
    (hbBox : b ∈ rlc_connectorBox n)
    (hnot : s(x, a) ∉ rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces x a)
    (hcommonBox : ∀ k : Site 2,
      k ∈ flankFaces x a → k ∈ flankFaces x b →
        k ∈ rlc_connectorFaceBox n) :
    s(x, b) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  obtain ⟨k, hkIn, hkOut⟩ :=
    rlc_incident_flank_intersection_of_not_opposite hxa hxb hab hopp
  have hkRegion := rlc_centralFaceRegion_other_flank_of_nonwall
    gamma gamma' hxa hnot hhRegion hh hkIn (hcommonBox k hkIn hkOut)
  exact rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank
    gamma gamma' hxb hxBox hbBox hkRegion hkOut


theorem rlc_mem_connectorCentralFacePlanarEdges_of_opposite_incident_side
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x a b h : Site 2}
    (hxa : (hypercubicLattice 2).Adj x a)
    (hxb : (hypercubicLattice 2).Adj x b)
    (hxInterior : -2 * n < x 0 ∧ x 0 < 2 * n ∧
      -n < x 1 ∧ x 1 < n)
    (hnotIn : s(x, a) ∉ rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces x a)
    (hside : ∃ y : Site 2,
      (hypercubicLattice 2).Adj x y ∧
      y ≠ a ∧ y ≠ b ∧
      ¬ (a 0 + y 0 = 2 * x 0 ∧ a 1 + y 1 = 2 * x 1) ∧
      ¬ (y 0 + b 0 = 2 * x 0 ∧ y 1 + b 1 = 2 * x 1) ∧
      s(x, y) ∉ rlc_connectorFourTraceEdges gamma gamma') :
    s(x, b) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  obtain ⟨y, hxy, hya, hyb, hay, hybOpp, hnotSide⟩ := hside
  obtain ⟨k, hkIn, hkSide⟩ :=
    rlc_incident_flank_intersection_of_not_opposite hxa hxy hya.symm hay
  have hkBox := rlc_flank_mem_connectorFaceBox_of_interior
    hxa hxInterior hkIn
  have hkRegion := rlc_centralFaceRegion_other_flank_of_nonwall
    gamma gamma' hxa hnotIn hhRegion hh hkIn hkBox
  obtain ⟨l, hlSide, hlOut⟩ :=
    rlc_incident_flank_intersection_of_not_opposite hxy hxb hyb hybOpp
  have hlBox := rlc_flank_mem_connectorFaceBox_of_interior
    hxy hxInterior hlSide
  have hlRegion := rlc_centralFaceRegion_other_flank_of_nonwall
    gamma gamma' hxy hnotSide hkRegion hkSide hlSide hlBox
  apply rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank
    gamma gamma' hxb
  · simp [rlc_connectorBox, mem_rect]
    omega
  · simp [rlc_connectorBox, mem_rect]
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hxb
    omega
  · exact hlRegion
  · exact hlOut


end
end StatMech.Universality
