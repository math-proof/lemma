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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part58
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_wallTerminalFamilyTable_iff_rows
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur ul : Site 2}
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul) :
    RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyTable
        gamma gamma' omega qr ql ↔
      RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
          gamma gamma' omega qr ql ∨
        RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
          gamma gamma' omega qr ql ∨
        RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowThree
          gamma gamma' omega qr ql ∨
        RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowFour
          gamma gamma' omega qr ql := by
  rfl


theorem rlc_twoChannelFullPhysical_twoArcWallTerminalFamilyTable
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur ul : Site 2}
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hallR : ∀ e ∈ qr.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma')
    (hallL : ∀ e ∈ ql.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma')
    (hurLoc :
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
          gamma gamma' (rlc_dualReflect ur) ∨
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' (rlc_dualReflect ur))
    (hulLoc :
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
          gamma gamma' (rlc_dualReflect ul) ∨
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' (rlc_dualReflect ul)) :
    RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyTable
      gamma gamma' omega qr ql := by
  have qrNotNil : ¬qr.Nil := by
    intro hnil
    rcases hurLoc with hurLeft | hurRight
    · exact hurLeft.2.2.1 (by simpa [hnil.eq] using hxPath)
    · exact hurRight.2.2.1 (by simpa [hnil.eq] using hxPath)
  have qlNotNil : ¬ql.Nil := by
    intro hnil
    rcases hulLoc with hulLeft | hulRight
    · exact hulLeft.2.2.2 (by simpa [hnil.eq] using hyPath)
    · exact hulRight.2.2.2 (by simpa [hnil.eq] using hyPath)
  rcases hurLoc with hurLeft | hurRight
  · have hqrLeft :=
      rlc_twoChannelFullPhysical_goodWallWalk_reflectedLeft_of_terminal
        hfaith qr qrNotNil hallR hurLeft.2.1
    rcases hulLoc with hulLeft | hulRight
    · exact Or.inl ⟨hqrLeft, hurLeft,
        rlc_twoChannelFullPhysical_goodWallWalk_reflectedLeft_of_terminal
          hfaith ql qlNotNil hallL hulLeft.2.1,
        hulLeft⟩
    · exact Or.inr (Or.inl ⟨hqrLeft, hurLeft,
        rlc_twoChannelFullPhysical_goodWallWalk_reflectedRight_of_terminal
          hfaith ql qlNotNil hallL hulRight.2.1,
        hulRight⟩)
  · have hqrRight :=
      rlc_twoChannelFullPhysical_goodWallWalk_reflectedRight_of_terminal
        hfaith qr qrNotNil hallR hurRight.2.1
    rcases hulLoc with hulLeft | hulRight
    · exact Or.inr (Or.inr (Or.inl ⟨hqrRight, hurRight,
        rlc_twoChannelFullPhysical_goodWallWalk_reflectedLeft_of_terminal
          hfaith ql qlNotNil hallL hulLeft.2.1,
        hulLeft⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hqrRight, hurRight,
        rlc_twoChannelFullPhysical_goodWallWalk_reflectedRight_of_terminal
          hfaith ql qlNotNil hallL hulRight.2.1,
        hulRight⟩))


theorem rlc_twoChannelFullPhysical_sameReflectedLeft_end_order
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    (z : Site 2)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    {x y ur ul : Site 2}
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hxz : rlc_dualReflect x = z)
    (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
    (hqrLeft : ∀ e ∈ qr.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
    (hqlLeft : ∀ e ∈ ql.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
    (hurLeft : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
      gamma gamma' (rlc_dualReflect ur))
    (hulLeft : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
      gamma gamma' (rlc_dualReflect ul)) :
    let W := (rlc_ambientCrossingWalk gamma'.1).map
      rlc_flipXLatticeHom
    W.support.idxOf (rlc_dualReflect ur) <
      W.support.idxOf (rlc_dualReflect ul) := by
  classical
  let W := (rlc_ambientCrossingWalk gamma'.1).map
    rlc_flipXLatticeHom
  let hDual :
      rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega →g
        hypercubicLattice 2 := {
    toFun := rlc_dualReflect
    map_rel' := fun {f g} hfg =>
      (rlc_adj_dualReflect f g).mp hfg.1.1
  }
  let qrDual := qr.map hDual
  have hWPath : W.IsPath :=
    rlc_reflectedAmbientCrossingWalk_isPath gamma'.1
  have hurW : rlc_dualReflect ur ∈ W.support := by
    obtain ⟨r, hr, hur⟩ := hurLeft.2.1
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨r,
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 r).2 hr,
      hur.symm⟩
  have hulW : rlc_dualReflect ul ∈ W.support := by
    obtain ⟨r, hr, hul⟩ := hulLeft.2.1
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨r,
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 r).2 hr,
      hul.symm⟩
  obtain ⟨hzW, hulSuffix⟩ :=
    rlc_twoChannelFullPhysical_reflectedLeftAxisWalk_end_mem_suffix_at
      hnoGood z hzRight hzLeft ql hyAxis hqlLeft
  change z ∈ W.support at hzW
  change rlc_dualReflect ul ∈
    (W.dropUntil z hzW).support at hulSuffix
  have hzul : W.support.idxOf z ≤
      W.support.idxOf (rlc_dualReflect ul) :=
    rlc_isPath_idxOf_le_of_mem_dropUntil W hWPath hzW hulSuffix
  have hzne : z ≠ rlc_dualReflect ul := by
    intro h
    apply hulLeft.2.2.1
    simpa [← h] using hzRight
  have hzNotSuffix : z ∉
      (W.dropUntil (rlc_dualReflect ul) hulW).support := by
    intro hzSuffix
    have hulz := rlc_isPath_idxOf_le_of_mem_dropUntil
      W hWPath hulW hzSuffix
    have hidx : W.support.idxOf z =
        W.support.idxOf (rlc_dualReflect ul) := by omega
    exact hzne ((List.idxOf_inj hzW).1 hidx)
  have hqrEdges : ∀ e ∈ qrDual.edges, e ∈ W.edges := by
    intro e he
    change e ∈ (qr.map hDual).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    exact rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
      gamma'.1 (hqrLeft e0 he0)
  have hprefixDisjoint :=
    rlc_twoChannelFullPhysical_noGood_rightLeftPrefixes_disjoint
      hnoGood hxPath hyPath qr ql
  have hulAvoid : rlc_dualReflect ul ∉ qrDual.support := by
    intro hul
    change rlc_dualReflect ul ∈ (qr.map hDual).support at hul
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hul
    obtain ⟨w, hw, hwu⟩ := hul
    have hweq : w = ul := rlc_dualReflect.injective hwu
    exact hprefixDisjoint ul (by simpa [hweq] using hw) ql.end_mem_support
  have hsame := rlc_walk_end_mem_pathSuffix_iff_of_avoid
    W hWPath hulW qrDual hqrEdges hulAvoid
  have hurNotSuffix : rlc_dualReflect ur ∉
      (W.dropUntil (rlc_dualReflect ul) hulW).support := by
    intro hurSuffix
    apply hzNotSuffix
    have hxSuffix := hsame.mpr hurSuffix
    change rlc_dualReflect x ∈
      (W.dropUntil (rlc_dualReflect ul) hulW).support at hxSuffix
    rwa [hxz] at hxSuffix
  have hnotLe : ¬W.support.idxOf (rlc_dualReflect ul) ≤
      W.support.idxOf (rlc_dualReflect ur) := by
    intro hle
    exact hurNotSuffix
      ((rlc_isPath_mem_dropUntil_iff_idxOf_le
        W hWPath hulW hurW).2 hle)
  exact Nat.lt_of_not_ge hnotLe


theorem rlc_twoChannelFullPhysical_sameReflectedRight_end_order
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {r x y ur ul : Site 2}
    (hrRight : r ∈ rlc_pathVertices gamma.1)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hxAxis : rlc_dualReflect x = (gamma.1.1 : Site 2))
    (hyr : rlc_dualReflect y = rlc_flipX r)
    (hqrRight : ∀ e ∈ qr.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
    (hqlRight : ∀ e ∈ ql.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
    (hurRight : RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
      gamma gamma' (rlc_dualReflect ur))
    (hulRight : RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
      gamma gamma' (rlc_dualReflect ul)) :
    let W := ((rlc_ambientCrossingWalk gamma.1).map
      rlc_flipXLatticeHom).reverse
    W.support.idxOf (rlc_dualReflect ul) <
      W.support.idxOf (rlc_dualReflect ur) := by
  classical
  let W := ((rlc_ambientCrossingWalk gamma.1).map
    rlc_flipXLatticeHom).reverse
  let hDual :
      rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega →g
        hypercubicLattice 2 := {
    toFun := rlc_dualReflect
    map_rel' := fun {f g} hfg =>
      (rlc_adj_dualReflect f g).mp hfg.1.1
  }
  let qlDual := ql.map hDual
  have hWPath : W.IsPath :=
    (rlc_reflectedAmbientCrossingWalk_isPath gamma.1).reverse
  have hurW : rlc_dualReflect ur ∈ W.support := by
    obtain ⟨s, hs, hur⟩ := hurRight.2.1
    have hsMap : rlc_flipX s ∈
        ((rlc_ambientCrossingWalk gamma.1).map
          rlc_flipXLatticeHom).support := by
      rw [SimpleGraph.Walk.support_map, List.mem_map]
      exact ⟨s,
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 s).2 hs,
        rfl⟩
    simpa [W, SimpleGraph.Walk.support_reverse, hur] using hsMap
  have hulW : rlc_dualReflect ul ∈ W.support := by
    obtain ⟨s, hs, hul⟩ := hulRight.2.1
    have hsMap : rlc_flipX s ∈
        ((rlc_ambientCrossingWalk gamma.1).map
          rlc_flipXLatticeHom).support := by
      rw [SimpleGraph.Walk.support_map, List.mem_map]
      exact ⟨s,
        (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 s).2 hs,
        rfl⟩
    simpa [W, SimpleGraph.Walk.support_reverse, hul] using hsMap
  have hrLeft : rlc_flipX r ∈ rlc_pathVertices gamma'.1 := by
    simpa [hyr] using hyPath
  obtain ⟨hrW, hurSuffix⟩ :=
    rlc_twoChannelFullPhysical_reflectedRightAxisWalk_end_mem_suffix_at
      hnoGood r hrRight hrLeft qr hxAxis hqrRight
  change rlc_flipX r ∈ W.support at hrW
  change rlc_dualReflect ur ∈
    (W.dropUntil (rlc_flipX r) hrW).support at hurSuffix
  have hru : W.support.idxOf (rlc_flipX r) ≤
      W.support.idxOf (rlc_dualReflect ur) :=
    rlc_isPath_idxOf_le_of_mem_dropUntil W hWPath hrW hurSuffix
  have hrne : rlc_flipX r ≠ rlc_dualReflect ur := by
    intro h
    apply hurRight.2.2.2
    simpa [← h] using hrLeft
  have hrNotSuffix : rlc_flipX r ∉
      (W.dropUntil (rlc_dualReflect ur) hurW).support := by
    intro hrSuffix
    have hur := rlc_isPath_idxOf_le_of_mem_dropUntil
      W hWPath hurW hrSuffix
    have hidx : W.support.idxOf (rlc_flipX r) =
        W.support.idxOf (rlc_dualReflect ur) := by omega
    exact hrne ((List.idxOf_inj hrW).1 hidx)
  have hqlEdges : ∀ e ∈ qlDual.edges, e ∈ W.edges := by
    intro e he
    change e ∈ (ql.map hDual).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    have hforward :=
      rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
        gamma.1 (hqlRight e0 he0)
    simpa [W, SimpleGraph.Walk.edges_reverse] using hforward
  have hprefixDisjoint :=
    rlc_twoChannelFullPhysical_noGood_rightLeftPrefixes_disjoint
      hnoGood hxPath hyPath qr ql
  have hurAvoid : rlc_dualReflect ur ∉ qlDual.support := by
    intro hur
    change rlc_dualReflect ur ∈ (ql.map hDual).support at hur
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hur
    obtain ⟨w, hw, hwu⟩ := hur
    have hweq : w = ur := rlc_dualReflect.injective hwu
    exact hprefixDisjoint ur qr.end_mem_support (by simpa [hweq] using hw)
  have hsame := rlc_walk_end_mem_pathSuffix_iff_of_avoid
    W hWPath hurW qlDual hqlEdges hurAvoid
  have hulNotSuffix : rlc_dualReflect ul ∉
      (W.dropUntil (rlc_dualReflect ur) hurW).support := by
    intro hulSuffix
    apply hrNotSuffix
    have hySuffix := hsame.mpr hulSuffix
    change rlc_dualReflect y ∈
      (W.dropUntil (rlc_dualReflect ur) hurW).support at hySuffix
    rwa [hyr] at hySuffix
  have hnotLe : ¬W.support.idxOf (rlc_dualReflect ur) ≤
      W.support.idxOf (rlc_dualReflect ul) := by
    intro hle
    exact hulNotSuffix
      ((rlc_isPath_mem_dropUntil_iff_idxOf_le
        W hWPath hurW hulW).2 hle)
  exact Nat.lt_of_not_ge hnotLe


theorem rlc_twoChannelFullPhysical_wallFamilyRowOne_orderedSourceSplice
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {z x y ur vr ul vl : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hxz : rlc_dualReflect x = z)
    (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma' omega qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
    ∃ T : (hypercubicLattice 2).Walk vr vl,
      (∀ v ∈ T.support,
        v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
          ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
            phb_doubleDualShift a = v) ∧
      ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) <
        ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul) := by
  have horder :=
    rlc_twoChannelFullPhysical_sameReflectedLeft_end_order
      hnoGood z hzRight hzLeft hxPath hyPath qr ql hxz hyAxis
        hrow.1 hrow.2.2.1 hrow.2.1 hrow.2.2.2
  obtain ⟨_p, _q, _p', _q', T, _hpq, _hpq', _hpqAdj, _hpqAdj',
      _hpReach, _hpReach', _hqOut, _hqOut', hTprov⟩ :=
    rlc_twoChannelFullPhysical_boundary_directedReachableShiftWalk
      hurv hulv
  exact ⟨T, hTprov, horder⟩


theorem rlc_twoChannelFullPhysical_wallFamilyRowFour_orderedSourceSplice
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma' omega)
    {r x y ur vr ul vl : Site 2}
    (hrRight : r ∈ rlc_pathVertices gamma.1)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hxAxis : rlc_dualReflect x = (gamma.1.1 : Site 2))
    (hyr : rlc_dualReflect y = rlc_flipX r)
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowFour
      gamma gamma' omega qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
    ∃ T : (hypercubicLattice 2).Walk vr vl,
      (∀ v ∈ T.support,
        v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
          ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
            phb_doubleDualShift a = v) ∧
      (((rlc_ambientCrossingWalk gamma.1).map
          rlc_flipXLatticeHom).reverse).support.idxOf
            (rlc_dualReflect ul) <
        (((rlc_ambientCrossingWalk gamma.1).map
          rlc_flipXLatticeHom).reverse).support.idxOf
            (rlc_dualReflect ur) := by
  have horder :=
    rlc_twoChannelFullPhysical_sameReflectedRight_end_order
      hnoGood hrRight hxPath hyPath qr ql hxAxis hyr
        hrow.1 hrow.2.2.1 hrow.2.1 hrow.2.2.2
  obtain ⟨_p, _q, _p', _q', T, _hpq, _hpq', _hpqAdj, _hpqAdj',
      _hpReach, _hpReach', _hqOut, _hqOut', hTprov⟩ :=
    rlc_twoChannelFullPhysical_boundary_directedReachableShiftWalk
      hurv hulv
  exact ⟨T, hTprov, horder⟩


end
end StatMech.Universality
