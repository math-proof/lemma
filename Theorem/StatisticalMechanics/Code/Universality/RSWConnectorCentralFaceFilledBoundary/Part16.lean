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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part12
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_reflectedEdgeCarrierGeometry_iff_planarEdges {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {f g : Site 2} (hfg : (hypercubicLattice 2).Adj f g) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ↔
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  symm
  exact rlc_mem_connectorCentralFacePlanarEdges_iff gamma gamma'
    ((rlc_adj_dualReflect f g).mp hfg)


theorem RlcCentralFaceRetainedAnchoredBoundary.centralCutPath_nonwallGoodContourEdge_of_oppositeSide
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
    ∃ f g : Site 2,
      s(f, g) ∈ B.contour.edges ∧
        RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧
        s(rlc_dualReflect f, rlc_dualReflect g) ∉
          rlc_connectorFourTraceEdges gamma gamma' := by
  obtain ⟨f, g, z, z', hfgContour, _hzz, hzRegion, _hz'Region,
    hflank, hfBox, hgBox, hnonwall⟩ :=
    B.centralCutPath_goodContourEdge_of_oppositeSide
      hhRegion hhBox hh'Box hreach hopposite
  refine ⟨f, g, hfgContour, Or.inr ⟨hfBox, hgBox, z.1, hzRegion, ?_⟩,
    hnonwall⟩
  rw [hflank, Sym2.mem_iff]
  exact Or.inl rfl


theorem rlc_reflected_axisCrossing_carrier_of_between {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {f g : Site 2} {k : Int}
    (hfg : (hypercubicLattice 2).Adj f g)
    (hreflected : s(rlc_dualReflect f, rlc_dualReflect g) =
      s((![-1, k] : Site 2), ![0, k]))
    (hkLower : (gamma.1.1 : Site 2) 1 < k)
    (hkUpper : k ≤ (gamma'.1.2.1 : Site 2) 1) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g := by
  apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    gamma gamma' hfg).2
  rw [hreflected]
  exact rlc_axisGapHorizontal_mem_connectorCentralFacePlanarEdges
    gamma gamma' hfaith hkLower hkUpper


theorem rlc_reflected_axisCrossing_carrier_of_right_contact {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {f g : Site 2} {k : Int}
    (hfNeg : (rlc_dualReflect f) 0 < 0)
    (hreflected : s(rlc_dualReflect f, rlc_dualReflect g) =
      s((![-1, k] : Site 2), ![0, k]))
    (hgPath : rlc_dualReflect g ∈ rlc_pathVertices gamma.1) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g := by
  have hgEq : rlc_dualReflect g = (![0, k] : Site 2) := by
    rw [Sym2.eq_iff] at hreflected
    rcases hreflected with ⟨_hf, hg⟩ | ⟨hg, _hf⟩
    · exact hg
    · have h0 := congrArg (fun z : Site 2 => z 0) hg
      have h0' : (rlc_dualReflect f) 0 = 0 := by
        simpa only [Matrix.cons_val_zero] using h0
      omega
  have hgStart : rlc_dualReflect g = (gamma.1.1 : Site 2) :=
    hfaith.right_axis_unique hgPath (by rw [hgEq]; simp)
  have hstartEq : (gamma.1.1 : Site 2) = (![0, k] : Site 2) := by
    rw [← hgStart, hgEq]
  let W := rlc_ambientCrossingWalk gamma.1
  have hn : 0 < n := by
    have hsbox := gamma.1.1.2.1
    rw [mem_rect] at hsbox
    have hsneg := hfaith.right_axis_strict
    omega
  have hstartEnd : (gamma.1.1 : Site 2) ≠
      (gamma.1.2.1 : Site 2) := by
    intro heq
    have h0 := congrArg (fun z : Site 2 => z 0) heq
    change (gamma.1.1 : Site 2) 0 =
      (gamma.1.2.1 : Site 2) 0 at h0
    have hs0 : (gamma.1.1 : Site 2) 0 = 0 := gamma.1.1.2.2
    have he0 : (gamma.1.2.1 : Site 2) 0 = 2 * n :=
      gamma.1.2.1.2.2
    rw [hs0, he0] at h0
    omega
  have hWnil : ¬ W.Nil := W.not_nil_of_ne hstartEnd
  have hsndSupport : W.snd ∈ W.support :=
    List.mem_of_mem_tail (W.snd_mem_tail_support hWnil)
  have hsndPath : W.snd ∈ rlc_pathVertices gamma.1 :=
    rlc_ambientCrossingWalk_support_mem_pathVertices gamma.1 hsndSupport
  have hsndNe : W.snd ≠ (gamma.1.1 : Site 2) :=
    (W.adj_snd hWnil).ne.symm
  have hsndPos : 0 < W.snd 0 :=
    hfaith.right_vertex_strict hsndPath hsndNe
  have hsndEq : W.snd = (![1, k] : Site 2) := by
    have hadj := W.adj_snd hWnil
    rcases adj_cases hadj with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · have hs0 := gamma.1.1.2.2
      omega
    · ext i
      fin_cases i
      · have hs0 := gamma.1.1.2.2
        rcases h0 with h0 | h0 <;> simp <;> omega
      · have hstart1 := congrArg (fun z : Site 2 => z 1) hstartEq
        simpa only [Matrix.cons_val_one] using h1.symm.trans hstart1
  have hfirst : s((gamma.1.1 : Site 2), W.snd) ∈
      rlc_pathEdges gamma.1 :=
    rlc_ambientCrossingWalk_edge_mem_pathEdges gamma.1
      (W.mk_start_snd_mem_edges hWnil)
  have hreflectedFirst : s((![-1, k] : Site 2), ![0, k]) ∈
      rlc_reflectedPathEdges gamma.1 := by
    rw [rlc_reflectedPathEdges, Finset.mem_image]
    refine ⟨s((gamma.1.1 : Site 2), W.snd), hfirst, ?_⟩
    have hedgeEq : s((gamma.1.1 : Site 2), W.snd) =
        s((![0, k] : Site 2), ![1, k]) :=
      congrArg₂ Sym2.mk hstartEq hsndEq
    have hmapped := congrArg (Sym2.map rlc_flipX) hedgeEq
    simpa [Sym2.map_mk, rlc_flipX, rlc_flipXFun,
      Sym2.eq_swap] using hmapped
  unfold RlcCentralFaceReflectedEdgeCarrierGeometry
  left
  rw [hreflected]
  simp [rlc_connectorFourTraceEdges,
    rlc_connectorReflectedTraceEdges, hreflectedFirst]


theorem rlc_axisCrossing_carrier_of_left_contact {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {f g : Site 2} {k : Int}
    (hfNeg : (rlc_dualReflect f) 0 < 0)
    (hreflected : s(rlc_dualReflect f, rlc_dualReflect g) =
      s((![-1, k] : Site 2), ![0, k]))
    (hgPath : rlc_dualReflect g ∈ rlc_pathVertices gamma'.1) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g := by
  have hgEq : rlc_dualReflect g = (![0, k] : Site 2) := by
    rw [Sym2.eq_iff] at hreflected
    rcases hreflected with ⟨_hf, hg⟩ | ⟨hg, _hf⟩
    · exact hg
    · have h0 := congrArg (fun z : Site 2 => z 0) hg
      have h0' : (rlc_dualReflect f) 0 = 0 := by
        simpa only [Matrix.cons_val_zero] using h0
      omega
  have hgEnd : rlc_dualReflect g = (gamma'.1.2.1 : Site 2) :=
    hfaith.left_axis_unique hgPath (by rw [hgEq]; simp)
  have hendEq : (gamma'.1.2.1 : Site 2) = (![0, k] : Site 2) := by
    rw [← hgEnd, hgEq]
  let W := rlc_ambientCrossingWalk gamma'.1
  have hn : 0 < n := by
    have hebox := gamma'.1.2.1.2.1
    rw [mem_rect] at hebox
    have hepos := hfaith.left_axis_strict
    omega
  have hstartEnd : (gamma'.1.1 : Site 2) ≠
      (gamma'.1.2.1 : Site 2) := by
    intro heq
    have h0 := congrArg (fun z : Site 2 => z 0) heq
    change (gamma'.1.1 : Site 2) 0 =
      (gamma'.1.2.1 : Site 2) 0 at h0
    have hs0 : (gamma'.1.1 : Site 2) 0 = -2 * n :=
      gamma'.1.1.2.2
    have he0 : (gamma'.1.2.1 : Site 2) 0 = 0 :=
      gamma'.1.2.1.2.2
    rw [hs0, he0] at h0
    omega
  have hWnil : ¬ W.Nil := W.not_nil_of_ne hstartEnd
  have hpenSupport : W.penultimate ∈ W.support :=
    List.mem_of_mem_dropLast (W.penultimate_mem_dropLast_support hWnil)
  have hpenPath : W.penultimate ∈ rlc_pathVertices gamma'.1 :=
    rlc_ambientCrossingWalk_support_mem_pathVertices gamma'.1 hpenSupport
  have hpenNe : W.penultimate ≠ (gamma'.1.2.1 : Site 2) :=
    (W.adj_penultimate hWnil).ne
  have hpenNeg : W.penultimate 0 < 0 :=
    hfaith.left_vertex_strict hpenPath hpenNe
  have hpenEq : W.penultimate = (![-1, k] : Site 2) := by
    have hadj := W.adj_penultimate hWnil
    rcases adj_cases hadj with ⟨h0, h1⟩ | ⟨h1, h0⟩
    · have he0 := gamma'.1.2.1.2.2
      omega
    · ext i
      fin_cases i
      · have he0 := gamma'.1.2.1.2.2
        rcases h0 with h0 | h0 <;> simp <;> omega
      · have hend1 := congrArg (fun z : Site 2 => z 1) hendEq
        simpa only [Matrix.cons_val_one] using h1.trans hend1
  have hlast : s(W.penultimate, (gamma'.1.2.1 : Site 2)) ∈
      rlc_pathEdges gamma'.1 :=
    rlc_ambientCrossingWalk_edge_mem_pathEdges gamma'.1
      (W.mk_penultimate_end_mem_edges hWnil)
  have haxisEdge : s((![-1, k] : Site 2), ![0, k]) ∈
      rlc_pathEdges gamma'.1 := by
    have hedgeEq : s(W.penultimate, (gamma'.1.2.1 : Site 2)) =
        s((![-1, k] : Site 2), ![0, k]) :=
      congrArg₂ Sym2.mk hpenEq hendEq
    rwa [← hedgeEq]
  unfold RlcCentralFaceReflectedEdgeCarrierGeometry
  left
  rw [hreflected]
  simp [rlc_connectorFourTraceEdges, haxisEdge]


theorem rlc_reflectedLeft_opposite_continuation_carrier
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v b w h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
    (hub : u ≠ b)
    (hvflip : rlc_dualReflect v = rlc_flipX w)
    (hw : w ∈ rlc_pathVertices gamma'.1)
    (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
    (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
    (hvFlipRight : ¬ ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect v = rlc_flipX r)
    (hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 =
        2 * (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 =
        2 * (rlc_dualReflect v) 1)
    (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    gamma gamma' hvb.1).2
  let x := rlc_dualReflect v
  let a := rlc_dualReflect u
  let c := rlc_dualReflect b
  have hxa : (hypercubicLattice 2).Adj x a :=
    (rlc_adj_dualReflect u v).mp huv.1 |>.symm
  have hxc : (hypercubicLattice 2).Adj x c :=
    (rlc_adj_dualReflect v b).mp hvb.1
  have hac : a ≠ c := by
    intro hac
    apply hub
    apply rlc_dualReflect.injective
    exact hac
  have sideTransfer (y : Site 2)
      (hxy : (hypercubicLattice 2).Adj x y)
      (hya : y ≠ a) (hyc : y ≠ c)
      (hay : ¬ (a 0 + y 0 = 2 * x 0 ∧ a 1 + y 1 = 2 * x 1))
      (hycOpp : ¬ (y 0 + c 0 = 2 * x 0 ∧ y 1 + c 1 = 2 * x 1))
      (hnot : s(x, y) ∉ rlc_connectorFourTraceEdges gamma gamma') :
      s(x, c) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
    exact rlc_mem_connectorCentralFacePlanarEdges_of_opposite_incident_side
      gamma gamma' hxa hxc hvInterior hnotIn hhRegion hh
        ⟨y, hxy, hya, hyc, hay, hycOpp, hnot⟩
  have hpreNot :=
    rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
      gamma gamma' rho hno huv
  rcases face_adj_dir hxa with ha | ha | ha | ha
  · have hc : c = ![x 0 - 1, x 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yd : Site 2 := ![x 0, x 1 - 1]
    let yu : Site 2 := ![x 0, x 1 + 1]
    by_cases hd : s(x, yd) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hu : s(x, yu) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hdLeft := rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
          gamma gamma' hd (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipRight
        have hsouth : s((![w 0, w 1 - 1] : Site 2), w) ∈
            rlc_pathEdges gamma'.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma'.1
          simpa [yd, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap] using hdLeft
        have hb : b = ![v 0 + 1, v 1] := by
          apply rlc_dualReflect.injective
          change c = rlc_dualReflect ![v 0 + 1, v 1]
          rw [hc]
          ext i
          fin_cases i <;> simp [x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        have hvbNot :=
          rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
            gamma gamma' rho hno hvb
        exfalso
        apply hvbNot
        rw [hb, rlc_reflectedHit_sharedPrimalEdge_right hvflip]
        exact Finset.mem_union_right _ hsouth
      · exact sideTransfer yu
          (by simp [yu, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yu, a, ha]) (by simp [yu, c, hc])
          (by simp [yu, a, ha] <;> omega)
          (by simp [yu, c, hc] <;> omega) hu
    · exact sideTransfer yd
        (by simp [yd, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yd, a, ha]) (by simp [yd, c, hc])
        (by simp [yd, a, ha] <;> omega)
        (by simp [yd, c, hc] <;> omega) hd
  · have hc : c = ![x 0 + 1, x 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yd : Site 2 := ![x 0, x 1 - 1]
    let yu : Site 2 := ![x 0, x 1 + 1]
    by_cases hd : s(x, yd) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hu : s(x, yu) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hdLeft := rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
          gamma gamma' hd (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipRight
        have hsouth : s((![w 0, w 1 - 1] : Site 2), w) ∈
            rlc_pathEdges gamma'.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma'.1
          simpa [yd, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap] using hdLeft
        have huSource : u = ![v 0 + 1, v 1] := by
          apply rlc_dualReflect.injective
          change a = rlc_dualReflect ![v 0 + 1, v 1]
          rw [ha]
          ext i
          fin_cases i <;> simp [a, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        exfalso
        apply hpreNot
        rw [sharedPrimalEdge_comm_of_adj huv.1, huSource,
          rlc_reflectedHit_sharedPrimalEdge_right hvflip]
        exact Finset.mem_union_right _ hsouth
      · exact sideTransfer yu
          (by simp [yu, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yu, a, ha]) (by simp [yu, c, hc])
          (by simp [yu, a, ha] <;> omega)
          (by simp [yu, c, hc] <;> omega) hu
    · exact sideTransfer yd
        (by simp [yd, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yd, a, ha]) (by simp [yd, c, hc])
        (by simp [yd, a, ha] <;> omega)
        (by simp [yd, c, hc] <;> omega) hd
  · have hc : c = ![x 0, x 1 - 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yl : Site 2 := ![x 0 - 1, x 1]
    let yr : Site 2 := ![x 0 + 1, x 1]
    by_cases hl : s(x, yl) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hr : s(x, yr) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hrLeft := rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
          gamma gamma' hr (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipRight
        have hwest : s((![w 0 - 1, w 1] : Site 2), w) ∈
            rlc_pathEdges gamma'.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma'.1
          simpa [yr, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap, sub_eq_add_neg, add_comm] using hrLeft
        have huSource : u = ![v 0, v 1 + 1] := by
          apply rlc_dualReflect.injective
          change a = rlc_dualReflect ![v 0, v 1 + 1]
          rw [ha]
          ext i
          fin_cases i <;> simp [a, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        exfalso
        apply hpreNot
        rw [sharedPrimalEdge_comm_of_adj huv.1, huSource,
          rlc_reflectedHit_sharedPrimalEdge_top hvflip]
        exact Finset.mem_union_right _ hwest
      · exact sideTransfer yr
          (by simp [yr, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yr, a, ha]) (by simp [yr, c, hc])
          (by simp [yr, a, ha] <;> omega)
          (by simp [yr, c, hc] <;> omega) hr
    · exact sideTransfer yl
        (by simp [yl, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yl, a, ha]) (by simp [yl, c, hc])
        (by simp [yl, a, ha] <;> omega)
        (by simp [yl, c, hc] <;> omega) hl
  · have hc : c = ![x 0, x 1 + 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yl : Site 2 := ![x 0 - 1, x 1]
    let yr : Site 2 := ![x 0 + 1, x 1]
    by_cases hl : s(x, yl) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hr : s(x, yr) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hrLeft := rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
          gamma gamma' hr (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipRight
        have hwest : s((![w 0 - 1, w 1] : Site 2), w) ∈
            rlc_pathEdges gamma'.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma'.1
          simpa [yr, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap, sub_eq_add_neg, add_comm] using hrLeft
        have hb : b = ![v 0, v 1 + 1] := by
          apply rlc_dualReflect.injective
          change c = rlc_dualReflect ![v 0, v 1 + 1]
          rw [hc]
          ext i
          fin_cases i <;> simp [c, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        have hvbNot :=
          rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
            gamma gamma' rho hno hvb
        exfalso
        apply hvbNot
        rw [hb, rlc_reflectedHit_sharedPrimalEdge_top hvflip]
        exact Finset.mem_union_right _ hwest
      · exact sideTransfer yr
          (by simp [yr, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yr, a, ha]) (by simp [yr, c, hc])
          (by simp [yr, a, ha] <;> omega)
          (by simp [yr, c, hc] <;> omega) hr
    · exact sideTransfer yl
        (by simp [yl, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yl, a, ha]) (by simp [yl, c, hc])
        (by simp [yl, a, ha] <;> omega)
        (by simp [yl, c, hc] <;> omega) hl


theorem rlc_reflectedRight_opposite_continuation_carrier
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v b w h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
    (hub : u ≠ b)
    (hvflip : rlc_dualReflect v = rlc_flipX w)
    (hw : w ∈ rlc_pathVertices gamma.1)
    (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
    (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
    (hvFlipLeft : ¬ ∃ r ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect v = rlc_flipX r)
    (hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 =
        2 * (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 =
        2 * (rlc_dualReflect v) 1)
    (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
    gamma gamma' hvb.1).2
  let x := rlc_dualReflect v
  let a := rlc_dualReflect u
  let c := rlc_dualReflect b
  have hxa : (hypercubicLattice 2).Adj x a :=
    (rlc_adj_dualReflect u v).mp huv.1 |>.symm
  have hxc : (hypercubicLattice 2).Adj x c :=
    (rlc_adj_dualReflect v b).mp hvb.1
  have hac : a ≠ c := by
    intro hac
    apply hub
    apply rlc_dualReflect.injective
    exact hac
  have sideTransfer (y : Site 2)
      (hxy : (hypercubicLattice 2).Adj x y)
      (hya : y ≠ a) (hyc : y ≠ c)
      (hay : ¬ (a 0 + y 0 = 2 * x 0 ∧ a 1 + y 1 = 2 * x 1))
      (hycOpp : ¬ (y 0 + c 0 = 2 * x 0 ∧ y 1 + c 1 = 2 * x 1))
      (hnot : s(x, y) ∉ rlc_connectorFourTraceEdges gamma gamma') :
      s(x, c) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
    exact rlc_mem_connectorCentralFacePlanarEdges_of_opposite_incident_side
      gamma gamma' hxa hxc hvInterior hnotIn hhRegion hh
        ⟨y, hxy, hya, hyc, hay, hycOpp, hnot⟩
  have hpreNot :=
    rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
      gamma gamma' rho hno huv
  rcases face_adj_dir hxa with ha | ha | ha | ha
  · have hc : c = ![x 0 - 1, x 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yd : Site 2 := ![x 0, x 1 - 1]
    let yu : Site 2 := ![x 0, x 1 + 1]
    by_cases hd : s(x, yd) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hu : s(x, yu) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hdLeft := rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
          gamma gamma' hd (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipLeft
        have hsouth : s((![w 0, w 1 - 1] : Site 2), w) ∈
            rlc_pathEdges gamma.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma.1
          simpa [yd, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap] using hdLeft
        have hb : b = ![v 0 + 1, v 1] := by
          apply rlc_dualReflect.injective
          change c = rlc_dualReflect ![v 0 + 1, v 1]
          rw [hc]
          ext i
          fin_cases i <;> simp [x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        have hvbNot :=
          rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
            gamma gamma' rho hno hvb
        exfalso
        apply hvbNot
        rw [hb, rlc_reflectedHit_sharedPrimalEdge_right hvflip]
        exact Finset.mem_union_left _ hsouth
      · exact sideTransfer yu
          (by simp [yu, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yu, a, ha]) (by simp [yu, c, hc])
          (by simp [yu, a, ha] <;> omega)
          (by simp [yu, c, hc] <;> omega) hu
    · exact sideTransfer yd
        (by simp [yd, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yd, a, ha]) (by simp [yd, c, hc])
        (by simp [yd, a, ha] <;> omega)
        (by simp [yd, c, hc] <;> omega) hd
  · have hc : c = ![x 0 + 1, x 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yd : Site 2 := ![x 0, x 1 - 1]
    let yu : Site 2 := ![x 0, x 1 + 1]
    by_cases hd : s(x, yd) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hu : s(x, yu) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hdLeft := rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
          gamma gamma' hd (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipLeft
        have hsouth : s((![w 0, w 1 - 1] : Site 2), w) ∈
            rlc_pathEdges gamma.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma.1
          simpa [yd, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap] using hdLeft
        have huSource : u = ![v 0 + 1, v 1] := by
          apply rlc_dualReflect.injective
          change a = rlc_dualReflect ![v 0 + 1, v 1]
          rw [ha]
          ext i
          fin_cases i <;> simp [a, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        exfalso
        apply hpreNot
        rw [sharedPrimalEdge_comm_of_adj huv.1, huSource,
          rlc_reflectedHit_sharedPrimalEdge_right hvflip]
        exact Finset.mem_union_left _ hsouth
      · exact sideTransfer yu
          (by simp [yu, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yu, a, ha]) (by simp [yu, c, hc])
          (by simp [yu, a, ha] <;> omega)
          (by simp [yu, c, hc] <;> omega) hu
    · exact sideTransfer yd
        (by simp [yd, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yd, a, ha]) (by simp [yd, c, hc])
        (by simp [yd, a, ha] <;> omega)
        (by simp [yd, c, hc] <;> omega) hd
  · have hc : c = ![x 0, x 1 - 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yl : Site 2 := ![x 0 - 1, x 1]
    let yr : Site 2 := ![x 0 + 1, x 1]
    by_cases hl : s(x, yl) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hr : s(x, yr) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hrLeft := rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
          gamma gamma' hr (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipLeft
        have hwest : s((![w 0 - 1, w 1] : Site 2), w) ∈
            rlc_pathEdges gamma.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma.1
          simpa [yr, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap, sub_eq_add_neg, add_comm] using hrLeft
        have huSource : u = ![v 0, v 1 + 1] := by
          apply rlc_dualReflect.injective
          change a = rlc_dualReflect ![v 0, v 1 + 1]
          rw [ha]
          ext i
          fin_cases i <;> simp [a, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        exfalso
        apply hpreNot
        rw [sharedPrimalEdge_comm_of_adj huv.1, huSource,
          rlc_reflectedHit_sharedPrimalEdge_top hvflip]
        exact Finset.mem_union_left _ hwest
      · exact sideTransfer yr
          (by simp [yr, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yr, a, ha]) (by simp [yr, c, hc])
          (by simp [yr, a, ha] <;> omega)
          (by simp [yr, c, hc] <;> omega) hr
    · exact sideTransfer yl
        (by simp [yl, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yl, a, ha]) (by simp [yl, c, hc])
        (by simp [yl, a, ha] <;> omega)
        (by simp [yl, c, hc] <;> omega) hl
  · have hc : c = ![x 0, x 1 + 1] := by
      have ha0 := congrArg (fun z : Site 2 => z 0) ha
      have ha1 := congrArg (fun z : Site 2 => z 1) ha
      ext i
      fin_cases i <;> simp [a, c, x] at ha0 ha1 hopp ⊢ <;> omega
    let yl : Site 2 := ![x 0 - 1, x 1]
    let yr : Site 2 := ![x 0 + 1, x 1]
    by_cases hl : s(x, yl) ∈ rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hr : s(x, yr) ∈ rlc_connectorFourTraceEdges gamma gamma'
      · have hrLeft := rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
          gamma gamma' hr (Sym2.mem_mk_left _ _) hvRight hvLeft hvFlipLeft
        have hwest : s((![w 0 - 1, w 1] : Site 2), w) ∈
            rlc_pathEdges gamma.1 := by
          apply rlc_mem_pathEdges_of_reflected_mk gamma.1
          simpa [yr, x, hvflip, rlc_flipX, rlc_flipXFun,
            Sym2.eq_swap, sub_eq_add_neg, add_comm] using hrLeft
        have hb : b = ![v 0, v 1 + 1] := by
          apply rlc_dualReflect.injective
          change c = rlc_dualReflect ![v 0, v 1 + 1]
          rw [hc]
          ext i
          fin_cases i <;> simp [c, x, rlc_dualReflect, rlc_dualReflectFun] <;> omega
        have hvbNot :=
          rlc_connectorCentralFaceFilledBoundary_preimage_not_exposed_of_failure
            gamma gamma' rho hno hvb
        exfalso
        apply hvbNot
        rw [hb, rlc_reflectedHit_sharedPrimalEdge_top hvflip]
        exact Finset.mem_union_left _ hwest
      · exact sideTransfer yr
          (by simp [yr, hypercubicLattice_adj, Fin.sum_univ_two])
          (by simp [yr, a, ha]) (by simp [yr, c, hc])
          (by simp [yr, a, ha] <;> omega)
          (by simp [yr, c, hc] <;> omega) hr
    · exact sideTransfer yl
        (by simp [yl, hypercubicLattice_adj, Fin.sum_univ_two])
        (by simp [yl, a, ha]) (by simp [yl, c, hc])
        (by simp [yl, a, ha] <;> omega)
        (by simp [yl, c, hc] <;> omega) hl


theorem rlc_reflectedLeft_continuation_carrier
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v b w h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
    (hub : u ≠ b)
    (hvflip : rlc_dualReflect v = rlc_flipX w)
    (hw : w ∈ rlc_pathVertices gamma'.1)
    (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
    (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
    (hvFlipRight : ¬ ∃ r ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect v = rlc_flipX r)
    (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  by_cases hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 =
        2 * (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 =
        2 * (rlc_dualReflect v) 1
  · exact rlc_reflectedLeft_opposite_continuation_carrier
      gamma gamma' rho hno huv hvb hub hvflip hw hvRight hvLeft
        hvFlipRight hopp hvInterior hnotIn hhRegion hh
  · apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma' hvb.1).2
    apply rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident
      gamma gamma'
        ((rlc_adj_dualReflect u v).mp huv.1).symm
        ((rlc_adj_dualReflect v b).mp hvb.1)
    · intro heq
      apply hub
      apply rlc_dualReflect.injective
      exact heq
    · exact hopp
    · exact hvInterior
    · simpa [Sym2.eq_swap] using hnotIn
    · exact hhRegion
    · simpa [flankFaces_comm] using hh


theorem rlc_reflectedRight_continuation_carrier
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v b w h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
    (hub : u ≠ b)
    (hvflip : rlc_dualReflect v = rlc_flipX w)
    (hw : w ∈ rlc_pathVertices gamma.1)
    (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
    (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
    (hvFlipLeft : ¬ ∃ r ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect v = rlc_flipX r)
    (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  by_cases hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 =
        2 * (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 =
        2 * (rlc_dualReflect v) 1
  · exact rlc_reflectedRight_opposite_continuation_carrier
      gamma gamma' rho hno huv hvb hub hvflip hw hvRight hvLeft
        hvFlipLeft hopp hvInterior hnotIn hhRegion hh
  · apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma' hvb.1).2
    apply rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident
      gamma gamma'
        ((rlc_adj_dualReflect u v).mp huv.1).symm
        ((rlc_adj_dualReflect v b).mp hvb.1)
    · intro heq
      apply hub
      apply rlc_dualReflect.injective
      exact heq
    · exact hopp
    · exact hvInterior
    · simpa [Sym2.eq_swap] using hnotIn
    · exact hhRegion
    · simpa [flankFaces_comm] using hh


theorem rlc_positiveBarrier_continuation_or_right_contact
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v b h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
    (hub : u ≠ b)
    (hvPos : 0 < (rlc_dualReflect v) 0)
    (hvBarrier : rlc_dualReflect v ∈ rlc_connectorBarrier gamma gamma')
    (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    rlc_dualReflect v ∈ rlc_pathVertices gamma.1 ∨
      RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  by_cases hvRight : rlc_dualReflect v ∈ rlc_pathVertices gamma.1
  · exact Or.inl hvRight
  · right
    rcases rlc_connectorBarrier_positive_classify gamma gamma' hvPos hvBarrier with
      hvRight' | ⟨w, hw, hvflip⟩
    · exact False.elim (hvRight hvRight')
    · have hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1 := by
        intro hv
        have hvRect := rlc_pathVertex_mem_rect gamma'.1 hv
        rw [mem_rect] at hvRect
        omega
      have hvFlipRight : ¬ ∃ r ∈ rlc_pathVertices gamma.1,
          rlc_dualReflect v = rlc_flipX r := by
        rintro ⟨r, hr, heq⟩
        have hvPosCoord := hvPos
        have hrRect := rlc_pathVertex_mem_rect gamma.1 hr
        rw [mem_rect] at hrRect
        have heq0 := congrArg (fun z : Site 2 => z 0) heq
        simp [rlc_dualReflect, rlc_dualReflectFun,
          rlc_flipX, rlc_flipXFun] at hvPosCoord heq0
        omega
      exact rlc_reflectedLeft_continuation_carrier
        gamma gamma' rho hno huv hvb hub hvflip hw hvRight hvLeft
          hvFlipRight hvInterior hnotIn hhRegion hh


theorem rlc_negativeBarrier_continuation_or_left_contact
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v b h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
    (hub : u ≠ b)
    (hvNeg : (rlc_dualReflect v) 0 < 0)
    (hvBarrier : rlc_dualReflect v ∈ rlc_connectorBarrier gamma gamma')
    (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧
      (rlc_dualReflect v) 0 < 2 * n ∧
      -n < (rlc_dualReflect v) 1 ∧
      (rlc_dualReflect v) 1 < n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    rlc_dualReflect v ∈ rlc_pathVertices gamma'.1 ∨
      RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  by_cases hvLeft : rlc_dualReflect v ∈ rlc_pathVertices gamma'.1
  · exact Or.inl hvLeft
  · right
    rcases rlc_connectorBarrier_negative_classify gamma gamma' hvNeg hvBarrier with
      hvLeft' | ⟨w, hw, hvflip⟩
    · exact False.elim (hvLeft hvLeft')
    · have hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1 := by
        intro hv
        have hvRect := rlc_pathVertex_mem_rect gamma.1 hv
        rw [mem_rect] at hvRect
        omega
      have hvFlipLeft : ¬ ∃ r ∈ rlc_pathVertices gamma'.1,
          rlc_dualReflect v = rlc_flipX r := by
        rintro ⟨r, hr, heq⟩
        have hvNegCoord := hvNeg
        have hrRect := rlc_pathVertex_mem_rect gamma'.1 hr
        rw [mem_rect] at hrRect
        have heq0 := congrArg (fun z : Site 2 => z 0) heq
        simp [rlc_dualReflect, rlc_dualReflectFun,
          rlc_flipX, rlc_flipXFun] at hvNegCoord heq0
        omega
      exact rlc_reflectedRight_continuation_carrier
        gamma gamma' rho hno huv hvb hub hvflip hw hvRight hvLeft
          hvFlipLeft hvInterior hnotIn hhRegion hh


theorem rlc_positiveBarrier_bad_exit_forces_right_contact
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {a u v : Site 2}
    (hau : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj a u)
    (hauCarrier : RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' a u)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hav : a ≠ v)
    (hnotWall : s(rlc_dualReflect a, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huBarrier : rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma')
    (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    rlc_dualReflect u ∈ rlc_pathVertices gamma.1 := by
  rcases hauCarrier with hwall | ⟨_haBox, _huBox, h, hhRegion, hh⟩
  · exact False.elim (hnotWall hwall)
  · rcases rlc_positiveBarrier_continuation_or_right_contact
      gamma gamma' rho hno hau huv hav huPos huBarrier huInterior
        (by simpa [Sym2.eq_swap] using hnotWall) hhRegion
        (by simpa [flankFaces_comm] using hh) with huRight | hcarrier
    · exact huRight
    · exact False.elim (hbad hcarrier)


theorem rlc_negativeBarrier_bad_exit_forces_left_contact
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {a u v : Site 2}
    (hau : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj a u)
    (hauCarrier : RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' a u)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hav : a ≠ v)
    (hnotWall : s(rlc_dualReflect a, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huBarrier : rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma')
    (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    rlc_dualReflect u ∈ rlc_pathVertices gamma'.1 := by
  rcases hauCarrier with hwall | ⟨_haBox, _huBox, h, hhRegion, hh⟩
  · exact False.elim (hnotWall hwall)
  · rcases rlc_negativeBarrier_continuation_or_left_contact
      gamma gamma' rho hno hau huv hav huNeg huBarrier huInterior
        (by simpa [Sym2.eq_swap] using hnotWall) hhRegion
        (by simpa [flankFaces_comm] using hh) with huLeft | hcarrier
    · exact huLeft
    · exact False.elim (hbad hcarrier)


theorem rlc_reflectedLeft_rightBoundary_continuation_carrier
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v b w h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
    (hub : u ≠ b)
    (hvflip : rlc_dualReflect v = rlc_flipX w)
    (hw : w ∈ rlc_pathVertices gamma'.1)
    (hvRightBoundary : (rlc_dualReflect v) 0 = 2 * n)
    (hvBox : rlc_dualReflect v ∈ rlc_connectorBox n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  have hHRect : H ⊆ rect (-2 * n) (2 * n) (-n) n :=
    rlc_connectorCentralFaceFilledReachSet_subset_connectorRect
      hn gamma gamma' rho
  have hv0 : v 0 = -2 * n - 1 := by
    simp [rlc_dualReflect, rlc_dualReflectFun] at hvRightBoundary
    omega
  have hne : (![v 0 + 1, v 1 + 1] : Site 2) ∉ H :=
    rlc_reflectedLeft_hit_sourceNE_not_filled
      gamma gamma' hfaith rho hno hw hvflip
  have neighborDir {t : Site 2}
      (hvt : (faceBoundaryGraph H).Adj v t) :
      t = ![v 0 + 1, v 1] ∨ t = ![v 0, v 1 - 1] := by
    rcases rlc_faceBoundary_step_of_NE_not_mem H hvt hne with
      ⟨ht, _⟩ | ht | ⟨ht, htH⟩ | ht
    · exact Or.inl ht
    · exfalso
      subst t
      have hp : (![v 0, v 1] : Site 2) ∉ H := by
        intro hp
        have hpRect := hHRect hp
        rw [mem_rect] at hpRect
        simp at hpRect
        omega
      have hq : (![v 0, v 1 + 1] : Site 2) ∉ H := by
        intro hq
        have hqRect := hHRect hq
        rw [mem_rect] at hqRect
        simp at hqRect
        omega
      have hshared : sharedPrimalEdge v ![v 0 - 1, v 1] =
          s((![v 0, v 1] : Site 2), ![v 0, v 1 + 1]) := by
        simp [sharedPrimalEdge]
        omega
      have hbd := hvt.2
      rw [hshared, bdEdge_mk] at hbd
      simp [hp, hq] at hbd
    · exfalso
      subst t
      have htRect := hHRect htH
      rw [mem_rect] at htRect
      simp at htRect
      omega
    · exact Or.inr ht
  have huDir := neighborDir huv.symm
  have hbDir := neighborDir hvb
  have bottomLower {t : Site 2}
      (hvt : (faceBoundaryGraph H).Adj v t)
      (ht : t = ![v 0, v 1 - 1]) : -n ≤ v 1 := by
    subst t
    by_contra hv1
    have hp : (![v 0, v 1] : Site 2) ∉ H := by
      intro hp
      have hpRect := hHRect hp
      rw [mem_rect] at hpRect
      simp at hpRect
      omega
    have hq : (![v 0 + 1, v 1] : Site 2) ∉ H := by
      intro hq
      have hqRect := hHRect hq
      rw [mem_rect] at hqRect
      simp at hqRect
      omega
    have hshared : sharedPrimalEdge v ![v 0, v 1 - 1] =
        s((![v 0, v 1] : Site 2), ![v 0 + 1, v 1]) := by
      simp [sharedPrimalEdge]
    have hbd := hvt.2
    rw [hshared, bdEdge_mk] at hbd
    simp [hp, hq] at hbd
  have hvRect : rlc_dualReflect v ∈
      rect (-2 * n) (2 * n) (-n) n := by
    simpa [rlc_connectorBox] using hvBox
  rw [mem_rect] at hvRect
  simp [rlc_dualReflect, rlc_dualReflectFun] at hvRect
  rcases huDir with huDir | huDir <;>
    rcases hbDir with hbDir | hbDir
  · exact False.elim (hub (huDir.trans hbDir.symm))
  · have hv1Lower := bottomLower hvb hbDir
    apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma' hvb.1).2
    apply rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident_boxed
      gamma gamma'
        ((rlc_adj_dualReflect u v).mp huv.1).symm
        ((rlc_adj_dualReflect v b).mp hvb.1)
    · intro heq
      exact hub (rlc_dualReflect.injective heq)
    · intro hopp
      simp [huDir, hbDir, rlc_dualReflect, rlc_dualReflectFun] at hopp
      omega
    · exact hvBox
    · simp [rlc_connectorBox, mem_rect, hbDir,
        rlc_dualReflect, rlc_dualReflectFun]
      constructor <;> omega
    · exact hnotIn
    · exact hhRegion
    · exact hh
    · intro k hkIn hkOut
      simp [huDir, hbDir, flankFaces,
        rlc_dualReflect, rlc_dualReflectFun] at hkIn hkOut
      rcases hkIn with hkIn | hkIn <;>
        rcases hkOut with hkOut | hkOut <;>
        simp [hkIn, rlc_connectorFaceBox, mem_rect] at hkOut ⊢ <;> omega
  · have hv1Lower := bottomLower huv.symm huDir
    apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma' hvb.1).2
    apply rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident_boxed
      gamma gamma'
        ((rlc_adj_dualReflect u v).mp huv.1).symm
        ((rlc_adj_dualReflect v b).mp hvb.1)
    · intro heq
      exact hub (rlc_dualReflect.injective heq)
    · intro hopp
      simp [huDir, hbDir, rlc_dualReflect, rlc_dualReflectFun] at hopp
      omega
    · exact hvBox
    · simp [rlc_connectorBox, mem_rect, hbDir,
        rlc_dualReflect, rlc_dualReflectFun]
      constructor <;> omega
    · exact hnotIn
    · exact hhRegion
    · exact hh
    · intro k hkIn hkOut
      simp [huDir, hbDir, flankFaces,
        rlc_dualReflect, rlc_dualReflectFun] at hkIn hkOut
      rcases hkIn with hkIn | hkIn <;>
        rcases hkOut with hkOut | hkOut <;>
        simp [hkIn, rlc_connectorFaceBox, mem_rect] at hkOut ⊢ <;> omega
  · exact False.elim (hub (huDir.trans hbDir.symm))


theorem rlc_reflectedLeft_bottomBoundary_continuation_carrier
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v b w h : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hvb : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj v b)
    (hub : u ≠ b)
    (hvflip : rlc_dualReflect v = rlc_flipX w)
    (hw : w ∈ rlc_pathVertices gamma'.1)
    (hvBottom : (rlc_dualReflect v) 1 = -n)
    (hvBox : rlc_dualReflect v ∈ rlc_connectorBox n)
    (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉
      rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  have hHRect : H ⊆ rect (-2 * n) (2 * n) (-n) n :=
    rlc_connectorCentralFaceFilledReachSet_subset_connectorRect
      hn gamma gamma' rho
  have hv1 : v 1 = -n - 1 := by
    simp [rlc_dualReflect, rlc_dualReflectFun] at hvBottom
    omega
  have hne : (![v 0 + 1, v 1 + 1] : Site 2) ∉ H :=
    rlc_reflectedLeft_hit_sourceNE_not_filled
      gamma gamma' hfaith rho hno hw hvflip
  have neighborDir {t : Site 2}
      (hvt : (faceBoundaryGraph H).Adj v t) :
      t = ![v 0 - 1, v 1] ∨ t = ![v 0, v 1 + 1] := by
    rcases rlc_faceBoundary_step_of_NE_not_mem H hvt hne with
      ⟨ht, htH⟩ | ht | ⟨ht, _⟩ | ht
    · exfalso
      subst t
      have htRect := hHRect htH
      rw [mem_rect] at htRect
      simp at htRect
      omega
    · exact Or.inl ht
    · exact Or.inr ht
    · exfalso
      subst t
      have hp : (![v 0, v 1] : Site 2) ∉ H := by
        intro hp
        have hpRect := hHRect hp
        rw [mem_rect] at hpRect
        simp at hpRect
        omega
      have hq : (![v 0 + 1, v 1] : Site 2) ∉ H := by
        intro hq
        have hqRect := hHRect hq
        rw [mem_rect] at hqRect
        simp at hqRect
        omega
      have hshared : sharedPrimalEdge v ![v 0, v 1 - 1] =
          s((![v 0, v 1] : Site 2), ![v 0 + 1, v 1]) := by
        simp [sharedPrimalEdge]
      have hbd := hvt.2
      rw [hshared, bdEdge_mk] at hbd
      simp [hp, hq] at hbd
  have leftLower {t : Site 2}
      (hvt : (faceBoundaryGraph H).Adj v t)
      (ht : t = ![v 0 - 1, v 1]) : -2 * n ≤ v 0 := by
    subst t
    by_contra hv0
    have hp : (![v 0, v 1] : Site 2) ∉ H := by
      intro hp
      have hpRect := hHRect hp
      rw [mem_rect] at hpRect
      simp at hpRect
      omega
    have hq : (![v 0, v 1 + 1] : Site 2) ∉ H := by
      intro hq
      have hqRect := hHRect hq
      rw [mem_rect] at hqRect
      simp at hqRect
      omega
    have hshared : sharedPrimalEdge v ![v 0 - 1, v 1] =
        s((![v 0, v 1] : Site 2), ![v 0, v 1 + 1]) := by
      simp [sharedPrimalEdge]
      omega
    have hbd := hvt.2
    rw [hshared, bdEdge_mk] at hbd
    simp [hp, hq] at hbd
  have huDir := neighborDir huv.symm
  have hbDir := neighborDir hvb
  have hvRect : rlc_dualReflect v ∈
      rect (-2 * n) (2 * n) (-n) n := by
    simpa [rlc_connectorBox] using hvBox
  rw [mem_rect] at hvRect
  simp [rlc_dualReflect, rlc_dualReflectFun] at hvRect
  rcases huDir with huDir | huDir <;>
    rcases hbDir with hbDir | hbDir
  · exact False.elim (hub (huDir.trans hbDir.symm))
  · have hv0Lower := leftLower huv.symm huDir
    apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma' hvb.1).2
    apply rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident_boxed
      gamma gamma'
        ((rlc_adj_dualReflect u v).mp huv.1).symm
        ((rlc_adj_dualReflect v b).mp hvb.1)
    · intro heq
      exact hub (rlc_dualReflect.injective heq)
    · intro hopp
      simp [huDir, hbDir, rlc_dualReflect, rlc_dualReflectFun] at hopp
      omega
    · exact hvBox
    · simp [rlc_connectorBox, mem_rect, hbDir,
        rlc_dualReflect, rlc_dualReflectFun]
      constructor <;> omega
    · exact hnotIn
    · exact hhRegion
    · exact hh
    · intro k hkIn hkOut
      simp [huDir, hbDir, flankFaces,
        rlc_dualReflect, rlc_dualReflectFun] at hkIn hkOut
      rcases hkIn with hkIn | hkIn <;>
        rcases hkOut with hkOut | hkOut <;>
        simp [hkIn, rlc_connectorFaceBox, mem_rect] at hkOut ⊢ <;> omega
  · have hv0Lower := leftLower hvb hbDir
    apply (rlc_reflectedEdgeCarrierGeometry_iff_planarEdges
      gamma gamma' hvb.1).2
    apply rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident_boxed
      gamma gamma'
        ((rlc_adj_dualReflect u v).mp huv.1).symm
        ((rlc_adj_dualReflect v b).mp hvb.1)
    · intro heq
      exact hub (rlc_dualReflect.injective heq)
    · intro hopp
      simp [huDir, hbDir, rlc_dualReflect, rlc_dualReflectFun] at hopp
      omega
    · exact hvBox
    · simp [rlc_connectorBox, mem_rect, hbDir,
        rlc_dualReflect, rlc_dualReflectFun]
      constructor <;> omega
    · exact hnotIn
    · exact hhRegion
    · exact hh
    · intro k hkIn hkOut
      simp [huDir, hbDir, flankFaces,
        rlc_dualReflect, rlc_dualReflectFun] at hkIn hkOut
      rcases hkIn with hkIn | hkIn <;>
        rcases hkOut with hkOut | hkOut <;>
        simp [hkIn, rlc_connectorFaceBox, mem_rect] at hkOut ⊢ <;> omega
  · exact False.elim (hub (huDir.trans hbDir.symm))


theorem rlc_reflectedEdgeCarrierGeometry_comm {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f g : Site 2) :
    RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ↔
      RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' g f := by
  unfold RlcCentralFaceReflectedEdgeCarrierGeometry
  constructor
  · rintro (hwall | ⟨hf, hg, hregion⟩)
    · exact Or.inl (by simpa [Sym2.eq_swap] using hwall)
    · refine Or.inr ⟨hg, hf, ?_⟩
      simpa [flankFaces_comm] using hregion
  · rintro (hwall | ⟨hg, hf, hregion⟩)
    · exact Or.inl (by simpa [Sym2.eq_swap] using hwall)
    · refine Or.inr ⟨hf, hg, ?_⟩
      simpa [flankFaces_comm] using hregion


end
end StatMech.Universality
