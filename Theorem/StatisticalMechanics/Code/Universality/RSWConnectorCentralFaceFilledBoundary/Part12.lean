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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part8
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

@[simp] theorem rlc_doubleDualShift_flipX_eq_dualReflect_symm
    (z : Site 2) :
    phb_doubleDualShift (rlc_flipX z) = rlc_dualReflect.symm z := by
  ext i
  fin_cases i <;>
    simp [phb_doubleDualShift, rlc_flipX, rlc_flipXFun,
      rlc_dualReflect, rlc_dualReflectInvFun]


theorem rlc_doubleDualShift_endpoint_mem_flankFaces {p q : Site 2}
    (hpq : (hypercubicLattice 2).Adj p q) :
    phb_doubleDualShift p ∈ flankFaces p q ∨
      phb_doubleDualShift q ∈ flankFaces p q := by
  classical
  rcases adj_cases hpq with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · unfold flankFaces
    rw [if_pos h0]
    rcases h1 with hpq | hqp
    · left
      rw [Sym2.mem_iff]
      left
      ext i
      fin_cases i <;> simp [phb_doubleDualShift] <;> omega
    · right
      rw [Sym2.mem_iff]
      left
      ext i
      fin_cases i <;> simp [phb_doubleDualShift] <;> omega
  · unfold flankFaces
    rw [if_neg (by intro heq; omega)]
    rcases h0 with hpq | hqp
    · left
      rw [Sym2.mem_iff]
      left
      ext i
      fin_cases i <;> simp [phb_doubleDualShift] <;> omega
    · right
      rw [Sym2.mem_iff]
      left
      ext i
      fin_cases i <;> simp [phb_doubleDualShift] <;> omega


theorem rlc_fourTrace_axis_vertex_height_eq_endpoint {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') (k : Int)
    (hk : (![0, k] : Site 2) ∈ rlc_connectorBarrier gamma gamma') :
    k = (gamma.1.1 : Site 2) 1 ∨
      k = (gamma'.1.2.1 : Site 2) 1 := by
  rw [rlc_axis_mem_connectorBarrier_iff] at hk
  rcases hk with hright | hleft
  · left
    have heq := hfaith.right_axis_unique hright (by simp)
    exact congrArg (fun z : Site 2 => z 1) heq
  · right
    have heq := hfaith.left_axis_unique hleft (by simp)
    exact congrArg (fun z : Site 2 => z 1) heq


theorem rlc_axisCrossEdge_not_mem_fourTrace_of_between {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {k : Int}
    (hlower : (gamma.1.1 : Site 2) 1 < k)
    (hupper : k < (gamma'.1.2.1 : Site 2) 1) :
    s((![-1, k] : Site 2), ![0, k]) ∉
      rlc_connectorFourTraceEdges gamma gamma' := by
  intro he
  have hkBarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
    gamma gamma' he (Sym2.mem_mk_right _ _)
  rcases rlc_fourTrace_axis_vertex_height_eq_endpoint
      gamma gamma' hfaith k hkBarrier with hk | hk <;> omega


theorem rlc_axisGapFace_mem_connectorCentralFaceRegion {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {t : Int}
    (htLower : (gamma.1.1 : Site 2) 1 ≤ t)
    (htUpper : t < (gamma'.1.2.1 : Site 2) 1) :
    (![-1, t] : Site 2) ∈
      rlc_connectorCentralFaceRegion gamma gamma' := by
  classical
  let S : Int := (gamma.1.1 : Site 2) 1
  let U : Int := (gamma'.1.2.1 : Site 2) 1
  have hSBounds : -n ≤ S ∧ S < 0 := by
    have hbox := gamma.1.1.2.1
    rw [mem_rect] at hbox
    exact ⟨hbox.2.2.1, hfaith.right_axis_strict⟩
  have hUBounds : 0 < U ∧ U ≤ n := by
    have hbox := gamma'.1.2.1.2.1
    rw [mem_rect] at hbox
    exact ⟨hfaith.left_axis_strict, hbox.2.2.2⟩
  have hn : 0 < n := by omega
  have hcentralBox := rlc_connectorCentralFace_mem_faceBox hn
  have hleftZeroBox : (![-1, 0] : Site 2) ∈
      rlc_connectorFaceBox n := by
    simp [rlc_connectorFaceBox, mem_rect]
    omega
  have htBox : (![-1, t] : Site 2) ∈ rlc_connectorFaceBox n := by
    simp [rlc_connectorFaceBox, mem_rect]
    omega
  have hbaseLat : (hypercubicLattice 2).Adj
      rlc_connectorCentralFace (![-1, 0] : Site 2) := by
    simp [rlc_connectorCentralFace, hypercubicLattice_adj,
      Fin.sum_univ_two]
  have hbaseShared : sharedPrimalEdge rlc_connectorCentralFace ![-1, 0] =
      s((![0, 0] : Site 2), ![0, 1]) := by
    simp [rlc_connectorCentralFace, sharedPrimalEdge]
  have hbaseNotWall : sharedPrimalEdge rlc_connectorCentralFace ![-1, 0] ∉
      rlc_connectorFourTraceEdges gamma gamma' := by
    rw [hbaseShared]
    intro he
    have hzBarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
      gamma gamma' he (Sym2.mem_mk_left _ _)
    rcases rlc_fourTrace_axis_vertex_height_eq_endpoint
        gamma gamma' hfaith 0 (by simpa using hzBarrier) with h0 | h0
    · change 0 = S at h0
      omega
    · change 0 = U at h0
      omega
  have hbase : (rlc_connectorFourTraceFaceCutGraph gamma gamma').Adj
      rlc_connectorCentralFace ![-1, 0] := by
    rw [rlc_connectorFourTraceFaceCutGraph_adj]
    exact ⟨hbaseLat, hbaseNotWall⟩
  let vertical : (hypercubicLattice 2).Walk
      (![-1, 0] : Site 2) ![-1, t] := sw_vertSeg (-1) 0 t
  have hverticalEdges : ∀ e ∈ vertical.edges,
      e ∈ (rlc_connectorFourTraceFaceCutGraph gamma gamma').edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ f g =>
        have hfg := vertical.adj_of_mem_edges he
        have hfSupp := vertical.fst_mem_support_of_mem_edges he
        have hgSupp := vertical.snd_mem_support_of_mem_edges he
        change f ∈ (sw_vertSeg (-1) 0 t).support at hfSupp
        change g ∈ (sw_vertSeg (-1) 0 t).support at hgSupp
        rw [sw_vertSeg_mem_support] at hfSupp hgSupp
        obtain ⟨a, ha, rfl⟩ := hfSupp
        obtain ⟨b, hb, rfl⟩ := hgSupp
        rw [Set.mem_uIcc] at ha hb
        have hab : a = b + 1 ∨ b = a + 1 := by
          rcases adj_cases hfg with hvert | hhoriz
          · exact hvert.2
          · simp at hhoriz
        let k := max a b
        have hkLower : S < k := by
          rcases hab with hab | hab
          · have hk : k = a := by simp [k, hab]
            rw [hk]
            rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega
          · have hk : k = b := by simp [k, hab]
            rw [hk]
            rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega
        have hkUpper : k < U := by
          rcases hab with hab | hab
          · have hk : k = a := by simp [k, hab]
            rw [hk]
            rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega
          · have hk : k = b := by simp [k, hab]
            rw [hk]
            rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega
        rw [SimpleGraph.mem_edgeSet,
          rlc_connectorFourTraceFaceCutGraph_adj]
        refine ⟨hfg, ?_⟩
        have hshared : sharedPrimalEdge (![-1, a] : Site 2) ![-1, b] =
            s((![-1, k] : Site 2), ![0, k]) := by
          simp [sharedPrimalEdge, k]
        rw [hshared]
        exact rlc_axisCrossEdge_not_mem_fourTrace_of_between
          gamma gamma' hfaith (by simpa [S] using hkLower)
            (by simpa [U] using hkUpper)
  let verticalCut := vertical.transfer
    (rlc_connectorFourTraceFaceCutGraph gamma gamma') hverticalEdges
  let full : (rlc_connectorFourTraceFaceCutGraph gamma gamma').Walk
      rlc_connectorCentralFace ![-1, t] :=
    (Walk.cons hbase Walk.nil).append verticalCut
  have hfullBox : ∀ z ∈ full.support, z ∈ rlc_connectorFaceBox n := by
    intro z hz
    dsimp only [full] at hz
    rw [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hzBase | hzVertical
    · simp only [SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_nil, List.mem_cons,
        List.mem_singleton] at hzBase
      rcases hzBase with rfl | hzBase
      · exact hcentralBox
      · rcases hzBase with rfl | hzNil
        · exact hleftZeroBox
        · simp at hzNil
    · have hzVertical : z ∈ vertical.support := by
        simpa [verticalCut, SimpleGraph.Walk.support_transfer] using hzVertical
      change z ∈ (sw_vertSeg (-1) 0 t).support at hzVertical
      rw [sw_vertSeg_mem_support] at hzVertical
      obtain ⟨a, ha, rfl⟩ := hzVertical
      rw [Set.mem_uIcc] at ha
      simp [rlc_connectorFaceBox, mem_rect]
      rcases ha with ha | ha <;> omega
  let finiteWalk := full.induce
    (rlc_connectorFaceBox n : Set (Site 2)) hfullBox
  have hset : (![-1, t] : Site 2) ∈
      rlc_connectorCentralFaceRegionSet gamma gamma' := by
    refine ⟨htBox, hcentralBox, ?_⟩
    exact ⟨finiteWalk⟩
  simpa [rlc_connectorCentralFaceRegion] using hset


theorem rlc_axisGapHorizontal_mem_connectorCentralFacePlanarEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') {k : Int}
    (hkLower : (gamma.1.1 : Site 2) 1 < k)
    (hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1) :
    s((![-1, k] : Site 2), ![0, k]) ∈
      rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  apply rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank
    gamma gamma'
  · simp [hypercubicLattice_adj, Fin.sum_univ_two]
  · simp [rlc_connectorBox, mem_rect]
    have hsbox := gamma.1.1.2.1
    rw [mem_rect] at hsbox
    have hubox := gamma'.1.2.1.2.1
    rw [mem_rect] at hubox
    omega
  · simp [rlc_connectorBox, mem_rect]
    have hsbox := gamma.1.1.2.1
    rw [mem_rect] at hsbox
    have hubox := gamma'.1.2.1.2.1
    rw [mem_rect] at hubox
    omega
  · exact rlc_axisGapFace_mem_connectorCentralFaceRegion
      gamma gamma' hfaith (t := k - 1) (by omega) (by omega)
  · simp [flankFaces]


theorem RlcCentralFaceRetainedAnchoredBoundary.anchor_reflected_mem_planar
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma') :
    s(rlc_dualReflect B.firstFace, rlc_dualReflect B.secondFace) ∈
      rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  have hn : 0 < n := by
    have hbox := gamma.1.1.2.1
    rw [mem_rect] at hbox
    have hs := hfaith.right_axis_strict
    omega
  have hcanonicalAdj : (hypercubicLattice 2).Adj
      (![-1, B.height] : Site 2) ![0, B.height] := by
    simp [hypercubicLattice_adj, Fin.sum_univ_two]
  have hcanonicalShared :
      sharedPrimalEdge (![-1, B.height] : Site 2) ![0, B.height] =
        s((![0, B.height] : Site 2), ![0, B.height + 1]) := by
    simp [sharedPrimalEdge]
  have hedge : s(B.firstFace, B.secondFace) =
      s((![-1, B.height] : Site 2), ![0, B.height]) := by
    exact sharedPrimalEdge_uncrossInj B.anchor_adj.1 hcanonicalAdj
      (B.anchor_shared.trans hcanonicalShared.symm)
  have htarget :
      s(rlc_dualReflect B.firstFace, rlc_dualReflect B.secondFace) =
        s((![-1, B.height + 1] : Site 2), ![0, B.height + 1]) := by
    have hmap := congrArg (Sym2.map rlc_dualReflect) hedge
    simpa [Sym2.map_mk, rlc_dualReflect, rlc_dualReflectFun,
      Sym2.eq_swap] using hmap
  have htLower := B.height_lower
  have htUpper := B.height_upper
  rw [htarget]
  apply rlc_mem_connectorCentralFacePlanarEdges_of_box_region_flank
    gamma gamma'
  · simp [hypercubicLattice_adj, Fin.sum_univ_two]
  · simp [rlc_connectorBox, mem_rect]
    have hsbox := gamma.1.1.2.1
    rw [mem_rect] at hsbox
    have hubox := gamma'.1.2.1.2.1
    rw [mem_rect] at hubox
    omega
  · simp [rlc_connectorBox, mem_rect]
    have hsbox := gamma.1.1.2.1
    rw [mem_rect] at hsbox
    have hubox := gamma'.1.2.1.2.1
    rw [mem_rect] at hubox
    omega
  · exact rlc_axisGapFace_mem_connectorCentralFaceRegion
      gamma gamma' hfaith B.height_lower B.height_upper
  · simp [flankFaces]


theorem rlc_faceBoundary_contact_of_flippedTrace_exit
    {a b c d : Int} (tau : RlcCrossingPath a b c d)
    (H : Set (Site 2))
    {u : Site 2} (huPath : u ∈ rlc_pathVertices tau)
    (huIn : rlc_flipX u ∈ H)
    {z : Site 2} (hzPath : z ∈ rlc_pathVertices tau)
    (hzOut : rlc_flipX z ∉ H) :
    ∃ x : Site 2, x ∈ (faceBoundaryGraph H).support ∧
      rlc_dualReflect x ∈ rlc_pathVertices tau := by
  classical
  let W := rlc_ambientCrossingWalk tau
  let Wf : (hypercubicLattice 2).Walk
      (rlc_flipX (tau.1 : Site 2)) (rlc_flipX (tau.2.1 : Site 2)) :=
    W.map rlc_flipXLatticeHom
  have hzW : z ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices tau z).2 hzPath
  have huW : u ∈ W.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices tau u).2 huPath
  have huWf : rlc_flipX u ∈ Wf.support := by
    change rlc_flipX u ∈ (W.map rlc_flipXLatticeHom).support
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨u, huW, rfl⟩
  have hzWf : rlc_flipX z ∈ Wf.support := by
    change rlc_flipX z ∈ (W.map rlc_flipXLatticeHom).support
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨z, hzW, rfl⟩
  let q : (hypercubicLattice 2).Walk (rlc_flipX u) (rlc_flipX z) :=
    (Wf.takeUntil (rlc_flipX u) huWf).reverse.append
      (Wf.takeUntil (rlc_flipX z) hzWf)
  obtain ⟨p, r, hprBoundary, hprEdge⟩ :=
    rlc_walk_mem_edgeBoundary_edges H q huIn hzOut
  have hqWf : ∀ v ∈ q.support, v ∈ Wf.support := by
    intro v hv
    dsimp only [q] at hv
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse] at hv
    rcases hv with hv | hv
    · exact Wf.support_takeUntil_subset_support huWf (by simpa using hv)
    · exact Wf.support_takeUntil_subset_support hzWf hv
  have hpWf : p ∈ Wf.support :=
    hqWf p (q.fst_mem_support_of_mem_edges hprEdge)
  have hrWf : r ∈ Wf.support :=
    hqWf r (q.snd_mem_support_of_mem_edges hprEdge)
  change p ∈ (W.map rlc_flipXLatticeHom).support at hpWf
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hpWf
  obtain ⟨p0, hp0W, hp0Eq⟩ := hpWf
  change rlc_flipX p0 = p at hp0Eq
  change r ∈ (W.map rlc_flipXLatticeHom).support at hrWf
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hrWf
  obtain ⟨r0, hr0W, hr0Eq⟩ := hrWf
  change rlc_flipX r0 = r at hr0Eq
  have hp0Path : p0 ∈ rlc_pathVertices tau :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices tau p0).1 hp0W
  have hr0Path : r0 ∈ rlc_pathVertices tau :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices tau r0).1 hr0W
  have hflankEdge : flankFaces p r ∈ (faceBoundaryGraph H).edgeSet := by
    rw [phb_flankFaces_mem_faceBoundaryGraph_iff hprBoundary.1,
      bdEdge_mk]
    exact hprBoundary.2
  obtain ⟨f, g, hflank, hfgLat⟩ := flankFaces_latAdj hprBoundary.1
  have hfg : (faceBoundaryGraph H).Adj f g := by
    rw [← SimpleGraph.mem_edgeSet, ← hflank]
    exact hflankEdge
  rcases rlc_doubleDualShift_endpoint_mem_flankFaces hprBoundary.1 with
      hpShift | hrShift
  · rw [hflank, Sym2.mem_iff] at hpShift
    rcases hpShift with hpShift | hpShift
    · refine ⟨f, hfg.mem_support_left, ?_⟩
      have hpf : phb_doubleDualShift (rlc_flipX p0) = f := by
        rw [hp0Eq]
        exact hpShift
      rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm] at hpf
      rw [← hpf]
      simpa using hp0Path
    · refine ⟨g, hfg.mem_support_right, ?_⟩
      have hpg : phb_doubleDualShift (rlc_flipX p0) = g := by
        rw [hp0Eq]
        exact hpShift
      rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm] at hpg
      rw [← hpg]
      simpa using hp0Path
  · rw [hflank, Sym2.mem_iff] at hrShift
    rcases hrShift with hrShift | hrShift
    · refine ⟨f, hfg.mem_support_left, ?_⟩
      have hrf : phb_doubleDualShift (rlc_flipX r0) = f := by
        rw [hr0Eq]
        exact hrShift
      rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm] at hrf
      rw [← hrf]
      simpa using hr0Path
    · refine ⟨g, hfg.mem_support_right, ?_⟩
      have hrg : phb_doubleDualShift (rlc_flipX r0) = g := by
        rw [hr0Eq]
        exact hrShift
      rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm] at hrg
      rw [← hrg]
      simpa using hr0Path


end
end StatMech.Universality
