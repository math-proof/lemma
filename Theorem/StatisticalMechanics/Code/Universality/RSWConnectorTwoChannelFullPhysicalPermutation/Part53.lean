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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part53
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_twoArcFirstBad_of_noGoodFirstBad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {hx : x ∈ c.support} {hy : y ∈ c.support}
    (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
      gamma gamma' omega c hx hy) :
    RlcTwoChannelFullPhysicalTwoArcFirstBadAt
      gamma gamma' omega c hx hy := by
  obtain ⟨ur, vr, ul, vl, qr, rr, ql, rl, hurv, hulv,
      hdecR, hdecL, hne, hbadR, hbadL, _hclassR, _hclassL⟩ := hbad
  exact ⟨ur, vr, ul, vl, qr, rr, ql, rl, hurv, hulv,
    hbadR, hdecR, hbadL, hdecL, hne⟩


theorem rlc_twoChannelFullPhysical_twoArcBadTerminalPlacement_of_noGoodFirstBad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {hx : x ∈ c.support} {hy : y ∈ c.support}
    (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
      gamma gamma' omega c hx hy) :
    RlcTwoChannelFullPhysicalTwoArcBadTerminalPlacementAt
      gamma gamma' omega c hx hy :=
  rlc_twoChannelFullPhysical_twoArcBadTerminalPlacement_of_firstBad
    (rlc_twoChannelFullPhysical_twoArcFirstBad_of_noGoodFirstBad hbad)


theorem rlc_twoChannelFullPhysical_not_badEdgesOnOneArc_of_twoArcNoGoodFirstBad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    (hc : c.IsTrail) {hx : x ∈ c.support} {hy : y ∈ c.support}
    (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
      gamma gamma' omega c hx hy) :
    ¬RlcTwoChannelFullPhysicalBadEdgesOnOneArcAt
      gamma gamma' omega c hx hy := by
  obtain ⟨ur, vr, ul, vl, hbadR, hmemR, hbadL, hmemL, _hne⟩ :=
    rlc_twoChannelFullPhysical_twoArcBadTerminalPlacement_of_noGoodFirstBad
      hbad
  have hdisjoint :=
    rlc_orderedContourArc_edges_disjoint_complementary c hc hx hy
  rintro (hallComp | hallOrd)
  · exact hdisjoint hmemR
      (hallComp (rlc_orderedContourArc_edges_subset c hx hy hmemR) hbadR)
  · exact hdisjoint
      (hallOrd (rlc_complementaryContourArc_edges_subset c hx hy hmemL)
        hbadL) hmemL


theorem rlc_twoChannelFullPhysical_not_contourArcSide_of_twoArcNoGoodFirstBad
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    (hc : c.IsTrail) {hx : x ∈ c.support} {hy : y ∈ c.support}
    (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
      gamma gamma' omega c hx hy) :
    ¬RlcTwoChannelFullPhysicalContourArcSide
      gamma gamma' omega c hx hy := by
  rw [rlc_twoChannelFullPhysical_contourArcSide_iff_badEdgesOnOneArc
    gamma gamma' omega c hc hx hy]
  exact
    rlc_twoChannelFullPhysical_not_badEdgesOnOneArc_of_twoArcNoGoodFirstBad
      hc hbad


theorem rlc_twoChannelFullPhysical_twoArcNoGood_insideSourceWalk
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {hx : x ∈ c.support} {hy : y ∈ c.support}
    (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
      gamma gamma' omega c hx hy) :
    ∃ (ur vr ul vl p q p' q' : Site 2)
      (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk x ur)
      (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk y ul)
      (w : (hypercubicLattice 2).Walk p p'),
      (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr ∧
        (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl ∧
        s(ur, vr) ≠ s(ul, vl) ∧
        RlcTwoChannelFullPhysicalRightArcClassifiedBad
          gamma gamma' omega ur vr ∧
        RlcTwoChannelFullPhysicalLeftArcClassifiedBad
          gamma gamma' omega ul vl ∧
        sharedPrimalEdge ur vr = s(p, q) ∧
        sharedPrimalEdge ul vl = s(p', q') ∧
        (hypercubicLattice 2).Adj p q ∧
        (hypercubicLattice 2).Adj p' q' ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        (phb_doubleDualShift p ∈ s(ur, vr) ∨
          phb_doubleDualShift q ∈ s(ur, vr)) ∧
        (phb_doubleDualShift p' ∈ s(ul, vl) ∨
          phb_doubleDualShift q' ∈ s(ul, vl)) ∧
        ∀ z ∈ w.support,
          z ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
            z ∈ rect (-2 * n) (2 * n) (-n) n := by
  obtain ⟨ur, vr, ul, vl, qr, rr, ql, rl, hurv, hulv,
      _hdecR, _hdecL, hne, _hbadR, _hbadL, hclassR, hclassL⟩ := hbad
  obtain ⟨p, q, p', q', w, hpq, hpq', hpqAdj, hpqAdj', hpReach,
      hpReach', hqOut, hqOut', hwReach⟩ :=
    rlc_twoChannelFullPhysical_boundary_insideSourceWalk
      gamma gamma' omega hurv hulv
  have hincR := rlc_doubleDualShift_endpoint_mem_boundaryEdge
    hurv.1 hpqAdj hpq
  have hincL := rlc_doubleDualShift_endpoint_mem_boundaryEdge
    hulv.1 hpqAdj' hpq'
  exact ⟨ur, vr, ul, vl, p, q, p', q', qr, ql, w, hurv, hulv, hne,
    hclassR, hclassL, hpq, hpq', hpqAdj, hpqAdj', hpReach, hpReach',
    hqOut, hqOut', hincR, hincL, hwReach⟩


theorem rlc_twoChannelFullPhysical_twoArcNoGood_shiftedInsideSourceWalk
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {hx : x ∈ c.support} {hy : y ∈ c.support}
    (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
      gamma gamma' omega c hx hy) :
    ∃ (ur vr ul vl a b : Site 2)
      (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk x ur)
      (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk y ul)
      (W : (hypercubicLattice 2).Walk a b),
      (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr ∧
        (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl ∧
        s(ur, vr) ≠ s(ul, vl) ∧
        RlcTwoChannelFullPhysicalRightArcShiftedClassifiedBad
          gamma gamma' omega ur vr a ∧
        RlcTwoChannelFullPhysicalLeftArcShiftedClassifiedBad
          gamma gamma' omega ul vl b ∧
        a ∈ s(ur, vr) ∧ b ∈ s(ul, vl) ∧
        (∀ z ∈ W.support,
          z ∈ rect (-2 * n - 2) (2 * n) (-n - 2) n) ∧
        ∀ z ∈ W.support,
          (∃ v ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
            phb_doubleDualShift v = z) ∨
          ∃ v ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega,
            phb_doubleDualShift v = z := by
  obtain ⟨ur, vr, ul, vl, p, q, p', q', qr, ql, w, hurv, hulv, hne,
      hclassR, hclassL, hpq, hpq', hpqAdj, hpqAdj', hpReach, hpReach',
      hqOut, hqOut', hincR, hincL, hwReach⟩ :=
    rlc_twoChannelFullPhysical_twoArcNoGood_insideSourceWalk hbad
  obtain ⟨a, b, W, ha, hb, haOrigin, hbOrigin, hW⟩ :=
    rlc_doubleDualShiftWalk_between_boundaryEdges
      w hpqAdj hpqAdj' hincR hincL
  have hpFilled : p ∈
      rlc_twoChannelFullFilledReachSet gamma gamma' omega :=
    rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega hpReach
  have hpFilled' : p' ∈
      rlc_twoChannelFullFilledReachSet gamma gamma' omega :=
    rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega hpReach'
  have hshiftClassR :
      RlcTwoChannelFullPhysicalRightArcShiftedClassifiedBad
        gamma gamma' omega ur vr a := by
    rcases hclassR with ⟨htarget, hloc⟩ |
        ⟨r, t, hrt, _hrtAdj, _hrReach, htOut, hloc⟩
    · exact Or.inl ⟨htarget, hloc, ha⟩
    · obtain ⟨hpr, hqt⟩ := rlc_orientedBoundaryWitness_unique
        hpFilled htOut (hpq.symm.trans hrt)
      subst r
      subst t
      exact Or.inr ⟨p, q, hpq, hpqAdj, hpReach, hqOut,
        hloc, haOrigin⟩
  have hshiftClassL :
      RlcTwoChannelFullPhysicalLeftArcShiftedClassifiedBad
        gamma gamma' omega ul vl b := by
    rcases hclassL with ⟨htarget, hloc⟩ |
        ⟨r, t, hrt, _hrtAdj, _hrReach, htOut, hloc⟩
    · exact Or.inl ⟨htarget, hloc, hb⟩
    · obtain ⟨hpr, hqt⟩ := rlc_orientedBoundaryWitness_unique
        hpFilled' htOut (hpq'.symm.trans hrt)
      subst r
      subst t
      exact Or.inr ⟨p', q', hpq', hpqAdj', hpReach', hqOut',
        hloc, hbOrigin⟩
  refine ⟨ur, vr, ul, vl, a, b, qr, ql, W, hurv, hulv, hne,
    hshiftClassR, hshiftClassL, ha, hb, ?_, ?_⟩
  · intro z hz
    rcases hW z hz with hq | hq' | ⟨v, hv, hvz⟩
    · rw [hq]
      exact rlc_doubleDualShift_neighbor_mem_expandedRect
        (rlc_twoChannelFullReachSet_subset_box
          gamma gamma' omega hpReach) hpqAdj
    · rw [hq']
      exact rlc_doubleDualShift_neighbor_mem_expandedRect
        (rlc_twoChannelFullReachSet_subset_box
          gamma gamma' omega hpReach') hpqAdj'
    · rw [← hvz]
      have hvBox := (hwReach v hv).2
      have hvShift := rlc_doubleDualShift_mem_translatedRect hvBox
      rw [mem_rect] at hvShift ⊢
      omega
  · intro z hz
    rcases hW z hz with hq | hq' | ⟨v, hv, hvz⟩
    · exact Or.inr ⟨q, hqOut, hq.symm⟩
    · exact Or.inr ⟨q', hqOut', hq'.symm⟩
    · exact Or.inl ⟨v, (hwReach v hv).1, hvz⟩


theorem rlc_twoChannelFullPhysical_twoArcNoGood_badTerminalWalk
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {hx : x ∈ c.support} {hy : y ∈ c.support}
    (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
      gamma gamma' omega c hx hy) :
    ∃ (ur vr ul vl : Site 2)
      (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk x ur)
      (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk y ul)
      (W : (hypercubicLattice 2).Walk ur ul),
      (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr ∧
        (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl ∧
        s(ur, vr) ≠ s(ul, vl) ∧
        ∀ z ∈ W.support,
          z ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
  obtain ⟨ur, vr, ul, vl, a, b, qr, ql, W, hurv, hulv, hne,
      _hclassR, _hclassL, ha, hb, hWBox, _hWSource⟩ :=
    rlc_twoChannelFullPhysical_twoArcNoGood_shiftedInsideSourceWalk hbad
  have haTether : a = ur ∨ (hypercubicLattice 2).Adj a ur := by
    rw [Sym2.mem_iff] at ha
    rcases ha with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hurv.1.symm
  have hbTether : b = ul ∨ (hypercubicLattice 2).Adj b ul := by
    rw [Sym2.mem_iff] at hb
    rcases hb with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hulv.1.symm
  obtain ⟨W', hW'⟩ :=
    rlc_walk_between_tethers W haTether hbTether
  have hinner {z : Site 2}
      (hz : z ∈ rect (-2 * n - 2) (2 * n) (-n - 2) n) :
      z ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
    rw [mem_rect] at hz ⊢
    omega
  have hurBox : ur ∈
      rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
    rcases haTether with rfl | haTether
    · exact hinner (hWBox a W.start_mem_support)
    · have h := rlc_neighbor_mem_expandedRect
        (hWBox a W.start_mem_support) haTether
      rw [mem_rect] at h ⊢
      omega
  have hulBox : ul ∈
      rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
    rcases hbTether with rfl | hbTether
    · exact hinner (hWBox b W.end_mem_support)
    · have h := rlc_neighbor_mem_expandedRect
        (hWBox b W.end_mem_support) hbTether
      rw [mem_rect] at h ⊢
      omega
  refine ⟨ur, vr, ul, vl, qr, ql, W', hurv, hulv, hne, ?_⟩
  intro z hz
  rcases hW' z hz with rfl | rfl | hz
  · exact hurBox
  · exact hulBox
  · exact hinner (hWBox z hz)


theorem rlc_twoChannelFullPhysical_twoArcNoGood_badTerminalWalk_withDirections
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {hx : x ∈ c.support} {hy : y ∈ c.support}
    (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
      gamma gamma' omega c hx hy) :
    ∃ (ur vr ul vl : Site 2)
      (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk x ur)
      (rr : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y)
      (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk y ul)
      (rl : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x)
      (W : (hypercubicLattice 2).Walk ur ul)
      (hurv : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
      (hulv : (faceBoundaryGraph
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl),
      rlc_orderedContourArc c hx hy =
          (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
            gamma gamma' omega)).append (.cons hurv rr) ∧
        (rlc_complementaryContourArc c hx hy).reverse =
          (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
            gamma gamma' omega)).append (.cons hulv rl) ∧
        s(ur, vr) ≠ s(ul, vl) ∧
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' ur vr ∧
        ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
          gamma gamma' ul vl ∧
        RlcTwoChannelFullPhysicalRightArcClassifiedBad
          gamma gamma' omega ur vr ∧
        RlcTwoChannelFullPhysicalLeftArcClassifiedBad
          gamma gamma' omega ul vl ∧
        ∀ z ∈ W.support,
          z ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
  obtain ⟨ur, vr, ul, vl, qr, rr, ql, rl, hurv, hulv,
      hdecR, hdecL, hne, hbadR, hbadL, hclassR, hclassL⟩ := hbad
  obtain ⟨p, q, p', q', w, hpq, hpq', hpqAdj, hpqAdj', hpReach,
      hpReach', _hqOut, _hqOut', hwReach⟩ :=
    rlc_twoChannelFullPhysical_boundary_insideSourceWalk
      gamma gamma' omega hurv hulv
  have hincR := rlc_doubleDualShift_endpoint_mem_boundaryEdge
    hurv.1 hpqAdj hpq
  have hincL := rlc_doubleDualShift_endpoint_mem_boundaryEdge
    hulv.1 hpqAdj' hpq'
  obtain ⟨a, b, W, ha, hb, _haOrigin, _hbOrigin, hW⟩ :=
    rlc_doubleDualShiftWalk_between_boundaryEdges
      w hpqAdj hpqAdj' hincR hincL
  have hWBox : ∀ z ∈ W.support,
      z ∈ rect (-2 * n - 2) (2 * n) (-n - 2) n := by
    intro z hz
    rcases hW z hz with hq | hq' | ⟨v, hv, hvz⟩
    · rw [hq]
      exact rlc_doubleDualShift_neighbor_mem_expandedRect
        (rlc_twoChannelFullReachSet_subset_box
          gamma gamma' omega hpReach) hpqAdj
    · rw [hq']
      exact rlc_doubleDualShift_neighbor_mem_expandedRect
        (rlc_twoChannelFullReachSet_subset_box
          gamma gamma' omega hpReach') hpqAdj'
    · rw [← hvz]
      have hvBox := (hwReach v hv).2
      have hvShift := rlc_doubleDualShift_mem_translatedRect hvBox
      rw [mem_rect] at hvShift ⊢
      omega
  have haTether : a = ur ∨ (hypercubicLattice 2).Adj a ur := by
    rw [Sym2.mem_iff] at ha
    rcases ha with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hurv.1.symm
  have hbTether : b = ul ∨ (hypercubicLattice 2).Adj b ul := by
    rw [Sym2.mem_iff] at hb
    rcases hb with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr hulv.1.symm
  obtain ⟨W', hW'⟩ := rlc_walk_between_tethers W haTether hbTether
  have hinner {z : Site 2}
      (hz : z ∈ rect (-2 * n - 2) (2 * n) (-n - 2) n) :
      z ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
    rw [mem_rect] at hz ⊢
    omega
  have hurBox : ur ∈
      rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
    rcases haTether with rfl | haTether
    · exact hinner (hWBox a W.start_mem_support)
    · have h := rlc_neighbor_mem_expandedRect
        (hWBox a W.start_mem_support) haTether
      rw [mem_rect] at h ⊢
      omega
  have hulBox : ul ∈
      rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
    rcases hbTether with rfl | hbTether
    · exact hinner (hWBox b W.end_mem_support)
    · have h := rlc_neighbor_mem_expandedRect
        (hWBox b W.end_mem_support) hbTether
      rw [mem_rect] at h ⊢
      omega
  refine ⟨ur, vr, ul, vl, qr, rr, ql, rl, W', hurv, hulv,
    hdecR, hdecL, hne, hbadR, hbadL, hclassR, hclassL, ?_⟩
  intro z hz
  rcases hW' z hz with rfl | rfl | hz
  · exact hurBox
  · exact hulBox
  · exact hinner (hWBox z hz)


theorem rlc_twoChannelFullPhysical_directedBadTerminalCrossingWalk
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {ur vr ul vl : Site 2}
    (W : (hypercubicLattice 2).Walk ur ul)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    (hWBox : ∀ v ∈ W.support,
      v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) :
    ∃ T : (hypercubicLattice 2).Walk vr vl,
      ∀ v ∈ T.support,
        v ∈ rect (-2 * n - 4) (2 * n + 2) (-n - 4) (n + 2) := by
  let pre : (hypercubicLattice 2).Walk vr ur := hurv.1.symm.toWalk
  let post : (hypercubicLattice 2).Walk ul vl := hulv.1.toWalk
  let T : (hypercubicLattice 2).Walk vr vl := (pre.append W).append post
  have hinner {v : Site 2}
      (hv : v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) :
      v ∈ rect (-2 * n - 4) (2 * n + 2) (-n - 4) (n + 2) := by
    rw [mem_rect] at hv ⊢
    omega
  have hurBox := hWBox ur W.start_mem_support
  have hulBox := hWBox ul W.end_mem_support
  have hvrBox : vr ∈
      rect (-2 * n - 4) (2 * n + 2) (-n - 4) (n + 2) := by
    have h := rlc_neighbor_mem_expandedRect hurBox hurv.1
    rw [mem_rect] at h ⊢
    omega
  have hvlBox : vl ∈
      rect (-2 * n - 4) (2 * n + 2) (-n - 4) (n + 2) := by
    have h := rlc_neighbor_mem_expandedRect hulBox hulv.1
    rw [mem_rect] at h ⊢
    omega
  refine ⟨T, ?_⟩
  intro v hv
  change v ∈ ((pre.append W).append post).support at hv
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with (hvPre | hvW) | hvPost
  · have : v = vr ∨ v = ur := by simpa [pre] using hvPre
    rcases this with rfl | rfl
    · exact hvrBox
    · exact hinner hurBox
  · exact hinner (hWBox v hvW)
  · have : v = ul ∨ v = vl := by simpa [post] using hvPost
    rcases this with rfl | rfl
    · exact hinner hulBox
    · exact hvlBox


theorem rlc_twoChannelFullPhysical_boundary_directedSourceWalk_withProvenance
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {ur vr ul vl : Site 2}
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
    ∃ (p q p' q' : Site 2)
      (T : (hypercubicLattice 2).Walk vr vl),
      sharedPrimalEdge ur vr = s(p, q) ∧
        sharedPrimalEdge ul vl = s(p', q') ∧
        (hypercubicLattice 2).Adj p q ∧
        (hypercubicLattice 2).Adj p' q' ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        (phb_doubleDualShift p ∈ s(ur, vr) ∨
          phb_doubleDualShift q ∈ s(ur, vr)) ∧
        (phb_doubleDualShift p' ∈ s(ul, vl) ∨
          phb_doubleDualShift q' ∈ s(ul, vl)) ∧
        (∀ z ∈ T.support,
          z ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) ∧
        ∀ z ∈ T.support,
          z = vr ∨ z = vl ∨
            z = phb_doubleDualShift q ∨
            z = phb_doubleDualShift q' ∨
            ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
              phb_doubleDualShift a = z := by
  obtain ⟨p, q, p', q', w, hpq, hpq', hpqAdj, hpqAdj', hpReach,
      hpReach', hqOut, hqOut', hwReach⟩ :=
    rlc_twoChannelFullPhysical_boundary_insideSourceWalk
      gamma gamma' omega hurv hulv
  have hincR := rlc_doubleDualShift_endpoint_mem_boundaryEdge
    hurv.1 hpqAdj hpq
  have hincL := rlc_doubleDualShift_endpoint_mem_boundaryEdge
    hulv.1 hpqAdj' hpq'
  obtain ⟨a, b, W, ha, hb, _haOrigin, _hbOrigin, hW⟩ :=
    rlc_doubleDualShiftWalk_between_boundaryEdges
      w hpqAdj hpqAdj' hincR hincL
  have haTether : a = vr ∨ (hypercubicLattice 2).Adj a vr := by
    rw [Sym2.mem_iff] at ha
    rcases ha with rfl | rfl
    · exact Or.inr hurv.1
    · exact Or.inl rfl
  have hbTether : b = vl ∨ (hypercubicLattice 2).Adj b vl := by
    rw [Sym2.mem_iff] at hb
    rcases hb with rfl | rfl
    · exact Or.inr hulv.1
    · exact Or.inl rfl
  obtain ⟨T, hT⟩ := rlc_walk_between_tethers W haTether hbTether
  have hWBox : ∀ z ∈ W.support,
      z ∈ rect (-2 * n - 2) (2 * n) (-n - 2) n := by
    intro z hz
    rcases hW z hz with hq | hq' | ⟨v, hv, hvz⟩
    · rw [hq]
      exact rlc_doubleDualShift_neighbor_mem_expandedRect
        (rlc_twoChannelFullReachSet_subset_box
          gamma gamma' omega hpReach) hpqAdj
    · rw [hq']
      exact rlc_doubleDualShift_neighbor_mem_expandedRect
        (rlc_twoChannelFullReachSet_subset_box
          gamma gamma' omega hpReach') hpqAdj'
    · rw [← hvz]
      have hvBox := (hwReach v hv).2
      have hvShift := rlc_doubleDualShift_mem_translatedRect hvBox
      rw [mem_rect] at hvShift ⊢
      omega
  have hinner {z : Site 2}
      (hz : z ∈ rect (-2 * n - 2) (2 * n) (-n - 2) n) :
      z ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
    rw [mem_rect] at hz ⊢
    omega
  have hvrBox : vr ∈
      rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
    rcases haTether with rfl | haTether
    · exact hinner (hWBox a W.start_mem_support)
    · have h := rlc_neighbor_mem_expandedRect
        (hWBox a W.start_mem_support) haTether
      rw [mem_rect] at h ⊢
      omega
  have hvlBox : vl ∈
      rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
    rcases hbTether with rfl | hbTether
    · exact hinner (hWBox b W.end_mem_support)
    · have h := rlc_neighbor_mem_expandedRect
        (hWBox b W.end_mem_support) hbTether
      rw [mem_rect] at h ⊢
      omega
  refine ⟨p, q, p', q', T, hpq, hpq', hpqAdj, hpqAdj', hpReach,
    hpReach', hqOut, hqOut', hincR, hincL, ?_, ?_⟩
  · intro z hz
    rcases hT z hz with rfl | rfl | hzW
    · exact hvrBox
    · exact hvlBox
    · exact hinner (hWBox z hzW)
  · intro z hz
    rcases hT z hz with rfl | rfl | hzW
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · rcases hW z hzW with hq | hq' | ⟨v, hv, hvz⟩
      · exact Or.inr (Or.inr (Or.inl hq))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hq')))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨v, (hwReach v hv).1, hvz⟩)))


theorem rlc_twoChannelFullPhysical_boundary_directedReachableShiftWalk
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {ur vr ul vl : Site 2}
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
    ∃ (p q p' q' : Site 2)
      (T : (hypercubicLattice 2).Walk vr vl),
      sharedPrimalEdge ur vr = s(p, q) ∧
        sharedPrimalEdge ul vl = s(p', q') ∧
        (hypercubicLattice 2).Adj p q ∧
        (hypercubicLattice 2).Adj p' q' ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        ∀ z ∈ T.support,
          z = vr ∨ z = ur ∨ z = ul ∨ z = vl ∨
            ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
              phb_doubleDualShift a = z := by
  obtain ⟨p, q, p', q', w, hpq, hpq', hpqAdj, hpqAdj', hpReach,
      hpReach', hqOut, hqOut', hwReach⟩ :=
    rlc_twoChannelFullPhysical_boundary_insideSourceWalk
      gamma gamma' omega hurv hulv
  obtain ⟨pre, hpre⟩ :=
    rlc_walk_secondFace_to_doubleDualShift_firstEndpoint hurv.1 hpq
  obtain ⟨post, hpost⟩ :=
    rlc_walk_secondFace_to_doubleDualShift_firstEndpoint hulv.1 hpq'
  let hom : hypercubicLattice 2 →g hypercubicLattice 2 := {
    toFun := phb_doubleDualShift
    map_rel' := fun {_ _} h ↦ phb_doubleDualShift_latAdj.mpr h }
  let W := w.map hom
  let T := (pre.append W).append post.reverse
  refine ⟨p, q, p', q', T, hpq, hpq', hpqAdj, hpqAdj', hpReach,
    hpReach', hqOut, hqOut', ?_⟩
  intro z hz
  dsimp only [T] at hz
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_reverse] at hz
  rcases hz with (hzPre | hzW) | hzPost
  · rcases hpre z hzPre with rfl | rfl | hz
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hpReach, hz.symm⟩)))
  · change z ∈ (w.map hom).support at hzW
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hzW
    obtain ⟨a, ha, rfl⟩ := hzW
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨a, (hwReach a ha).1, rfl⟩)))
  · rcases hpost z (by simpa using hzPost) with rfl | rfl | hz
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p', hpReach', hz.symm⟩)))


theorem
    rlc_twoChannelFullPhysical_boundary_directedReachableShiftWalk_withSource
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {ur vr ul vl : Site 2}
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
    ∃ (p q p' q' : Site 2)
      (w : (hypercubicLattice 2).Walk p p')
      (T : (hypercubicLattice 2).Walk vr vl),
      sharedPrimalEdge ur vr = s(p, q) ∧
        sharedPrimalEdge ul vl = s(p', q') ∧
        (hypercubicLattice 2).Adj p q ∧
        (hypercubicLattice 2).Adj p' q' ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        (∀ a ∈ w.support,
          a ∈ rlc_twoChannelFullReachSet gamma gamma' omega) ∧
        ∀ z ∈ T.support,
          z = vr ∨ z = ur ∨ z = ul ∨ z = vl ∨
            ∃ a ∈ w.support, phb_doubleDualShift a = z := by
  obtain ⟨p, q, p', q', w, hpq, hpq', hpqAdj, hpqAdj', hpReach,
      hpReach', hqOut, hqOut', hwReach⟩ :=
    rlc_twoChannelFullPhysical_boundary_insideSourceWalk
      gamma gamma' omega hurv hulv
  obtain ⟨pre, hpre⟩ :=
    rlc_walk_secondFace_to_doubleDualShift_firstEndpoint hurv.1 hpq
  obtain ⟨post, hpost⟩ :=
    rlc_walk_secondFace_to_doubleDualShift_firstEndpoint hulv.1 hpq'
  let hom : hypercubicLattice 2 →g hypercubicLattice 2 := {
    toFun := phb_doubleDualShift
    map_rel' := fun {_ _} h ↦ phb_doubleDualShift_latAdj.mpr h }
  let W := w.map hom
  let T := (pre.append W).append post.reverse
  refine ⟨p, q, p', q', w, T, hpq, hpq', hpqAdj, hpqAdj', hpReach,
    hpReach', hqOut, hqOut', fun a ha ↦ (hwReach a ha).1, ?_⟩
  intro z hz
  dsimp only [T] at hz
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_reverse] at hz
  rcases hz with (hzPre | hzW) | hzPost
  · rcases hpre z hzPre with rfl | rfl | hz
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨p, w.start_mem_support, hz.symm⟩)))
  · change z ∈ (w.map hom).support at hzW
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hzW
    obtain ⟨a, ha, rfl⟩ := hzW
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, rfl⟩)))
  · rcases hpost z (by simpa using hzPost) with rfl | rfl | hz
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨p', w.end_mem_support, hz.symm⟩)))


theorem
    rlc_twoChannelFullPhysical_boundary_directedReachableShiftWalk_withEdges
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {ur vr ul vl : Site 2}
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
    ∃ (p q p' q' : Site 2)
      (w : (hypercubicLattice 2).Walk p p')
      (T : (hypercubicLattice 2).Walk vr vl),
      sharedPrimalEdge ur vr = s(p, q) ∧
        sharedPrimalEdge ul vl = s(p', q') ∧
        (hypercubicLattice 2).Adj p q ∧
        (hypercubicLattice 2).Adj p' q' ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        (∀ a ∈ w.support,
          a ∈ rlc_twoChannelFullReachSet gamma gamma' omega) ∧
        (∀ e ∈ w.edges,
          rlc_twoChannelFullAmbientConfig gamma gamma' omega e = true) ∧
        (∀ a ∈ w.support,
          phb_doubleDualShift a ∈ T.support) ∧
        (∀ e ∈ w.edges,
          Sym2.map phb_doubleDualShift e ∈ T.edges) ∧
        (phb_doubleDualShift q ∈ s(ur, vr) →
          phb_doubleDualShift q ∈ T.support) ∧
        (phb_doubleDualShift q' ∈ s(ul, vl) →
          phb_doubleDualShift q' ∈ T.support) ∧
        (∀ z ∈ T.support,
          z = vr ∨ z = ur ∨ z = ul ∨ z = vl ∨
            ∃ a ∈ w.support, phb_doubleDualShift a = z) ∧
        ∀ e ∈ T.edges,
          (∀ z ∈ e,
              z = vr ∨ z = ur ∨ z = phb_doubleDualShift p) ∨
            (∃ e₀ ∈ w.edges,
              Sym2.map phb_doubleDualShift e₀ = e) ∨
            ∀ z ∈ e,
              z = vl ∨ z = ul ∨ z = phb_doubleDualShift p' := by
  obtain ⟨p, q, p', q', w, hpq, hpq', hpqAdj, hpqAdj', hpReach,
      hpReach', hqOut, hqOut', hwReach, hwOpen⟩ :=
    rlc_twoChannelFullPhysical_boundary_insideOpenSourceWalk
      gamma gamma' omega hurv hulv
  obtain ⟨pre, hpre, hqPre⟩ :=
    rlc_walk_secondFace_to_doubleDualShift_firstEndpoint_with_incidence
      hurv.1 hpq
  obtain ⟨post, hpost, hqPost⟩ :=
    rlc_walk_secondFace_to_doubleDualShift_firstEndpoint_with_incidence
      hulv.1 hpq'
  let hom : hypercubicLattice 2 →g hypercubicLattice 2 := {
    toFun := phb_doubleDualShift
    map_rel' := fun {_ _} h ↦ phb_doubleDualShift_latAdj.mpr h }
  let W := w.map hom
  let T := (pre.append W).append post.reverse
  refine ⟨p, q, p', q', w, T, hpq, hpq', hpqAdj, hpqAdj', hpReach,
    hpReach', hqOut, hqOut', hwReach, hwOpen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    dsimp only [T]
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff]
    left; right
    change phb_doubleDualShift a ∈ (w.map hom).support
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨a, ha, rfl⟩
  · intro e he
    dsimp only [T]
    simp only [SimpleGraph.Walk.edges_append, List.mem_append]
    left; right
    change Sym2.map phb_doubleDualShift e ∈ (w.map hom).edges
    rw [SimpleGraph.Walk.edges_map, List.mem_map]
    exact ⟨e, he, rfl⟩
  · intro hinc
    dsimp only [T]
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (Or.inl (hqPre hinc))
  · intro hinc
    dsimp only [T]
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse]
    exact Or.inr (by simpa using hqPost hinc)
  · intro z hz
    dsimp only [T] at hz
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.support_reverse] at hz
    rcases hz with (hzPre | hzW) | hzPost
    · rcases hpre z hzPre with rfl | rfl | hz
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨p, w.start_mem_support, hz.symm⟩)))
    · change z ∈ (w.map hom).support at hzW
      rw [SimpleGraph.Walk.support_map, List.mem_map] at hzW
      obtain ⟨a, ha, rfl⟩ := hzW
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, ha, rfl⟩)))
    · rcases hpost z (by simpa using hzPost) with rfl | rfl | hz
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨p', w.end_mem_support, hz.symm⟩)))
  · intro e he
    dsimp only [T] at he
    simp only [SimpleGraph.Walk.edges_append, List.mem_append] at he
    rcases he with (hePre | heW) | hePost
    · left
      intro z hz
      induction e using Sym2.inductionOn with
      | _ a b =>
          rw [Sym2.mem_iff] at hz
          rcases hz with rfl | rfl
          · exact hpre _ (pre.fst_mem_support_of_mem_edges hePre)
          · exact hpre _ (pre.snd_mem_support_of_mem_edges hePre)
    · right; left
      change e ∈ (w.map hom).edges at heW
      rw [SimpleGraph.Walk.edges_map, List.mem_map] at heW
      obtain ⟨e₀, he₀, heeq⟩ := heW
      exact ⟨e₀, he₀, heeq⟩
    · right; right
      have hePost' : e ∈ post.edges := by
        simpa [SimpleGraph.Walk.edges_reverse] using hePost
      intro z hz
      induction e using Sym2.inductionOn with
      | _ a b =>
          rw [Sym2.mem_iff] at hz
          rcases hz with rfl | rfl
          · exact hpost _ (post.fst_mem_support_of_mem_edges hePost')
          · exact hpost _ (post.snd_mem_support_of_mem_edges hePost')


@[simp] theorem rlc_dualReflect_doubleDualShift_eq_flipX (z : Site 2) :
    rlc_dualReflect (phb_doubleDualShift z) = rlc_flipX z := by
  ext i
  fin_cases i <;>
    simp [rlc_dualReflect, rlc_dualReflectFun, phb_doubleDualShift,
      rlc_flipX, rlc_flipXFun]


end
end StatMech.Universality
