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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part83
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelFullPhysical_wallFamilyRowOne_originalParity_HContact_or_residue
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u z x y ur vr ul vl p q p' q' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hc : c.IsCycle) (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hxz : rlc_dualReflect x = z)
    (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpqAdj' : (hypercubicLattice 2).Adj p' q')
    (hpShift : phb_doubleDualShift p = vr)
    (hpShift' : phb_doubleDualShift p' = vl)
    (horder : ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) <
      ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
    (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c hx hy).edges)
    (hLArc : s(ul, vl) ∈
      (rlc_complementaryContourArc c hx hy).edges)
    (i j : Nat)
    (hiLength : i ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).length)
    (hij : i ≤ j)
    (hjLength : j ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).length) :
    let B := rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight
    let H := rlc_walkIndexInterval B i j hiLength hij hjLength
    let P := RlcTwoChannelFullPhysicalRowOneOriginalParityContact
      gamma' p q p' q'
    (∃ a ∈ H.support, P a) ∨
      RlcTwoChannelFullPhysicalRowOneOriginalParityIndexedContactResidue
        gamma gamma' c hx hy hzRight i j p q p' q' := by
  dsimp only
  let B := rlc_bookRowOnePhysicalTraceNetworkBracket
    gamma gamma' hzRight
  let P := RlcTwoChannelFullPhysicalRowOneOriginalParityContact
    gamma' p q p' q'
  have hcontact :=
    rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_originalParity_indexedContact
      hn c hc hx hy hzRight hxz hyAxis hrow hurv hulv hpq hpq'
        hpqAdj hpqAdj' hpShift hpShift' horder hRArc hLArc i j
          hiLength hij hjLength
  change (∃ a ∈ (rlc_walkIndexInterval B i j hiLength hij hjLength).support,
      P a) ∨
    (∃ k : Nat, k < i ∧ P (B.getVert k)) ∨
    (∃ k : Nat, j < k ∧ k ≤ B.length ∧ P (B.getVert k)) ∨
    ∃ a ∈ (rlc_orderedContourArc c hx hy).support, P a at hcontact
  rcases hcontact with hH | hbefore | hafter | harc
  · exact Or.inl hH
  · right
    change
      (∃ k : Nat, k < i ∧ P (B.getVert k) ∧
        RlcTwoChannelFullPhysicalRowOneBracketSourceProvenance
          gamma gamma' (B.getVert k)) ∨ _
    obtain ⟨k, hki, hkP⟩ := hbefore
    exact Or.inl ⟨k, hki, hkP,
      rlc_bookRowOnePhysicalTraceNetworkBracket_support_cases
        gamma gamma' hzRight (B.getVert_mem_support k)⟩
  · right
    change _ ∨
      (∃ k : Nat, j < k ∧ k ≤ B.length ∧ P (B.getVert k) ∧
        RlcTwoChannelFullPhysicalRowOneBracketSourceProvenance
          gamma gamma' (B.getVert k)) ∨ _
    obtain ⟨k, hjk, hkLength, hkP⟩ := hafter
    exact Or.inr (Or.inl ⟨k, hjk, hkLength, hkP,
      rlc_bookRowOnePhysicalTraceNetworkBracket_support_cases
        gamma gamma' hzRight (B.getVert_mem_support k)⟩)
  · right
    exact Or.inr (Or.inr harc)


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowOne_originalParity_HContact_of_noResidue
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u z x y ur vr ul vl p q p' q' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hc : c.IsCycle) (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hxz : rlc_dualReflect x = z)
    (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpqAdj' : (hypercubicLattice 2).Adj p' q')
    (hpShift : phb_doubleDualShift p = vr)
    (hpShift' : phb_doubleDualShift p' = vl)
    (horder : ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) <
      ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
    (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c hx hy).edges)
    (hLArc : s(ul, vl) ∈
      (rlc_complementaryContourArc c hx hy).edges)
    (i j : Nat)
    (hiLength : i ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).length)
    (hij : i ≤ j)
    (hjLength : j ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).length)
    (hresidue : ¬
      RlcTwoChannelFullPhysicalRowOneOriginalParityIndexedContactResidue
        gamma gamma' c hx hy hzRight i j p q p' q') :
    let B := rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight
    let H := rlc_walkIndexInterval B i j hiLength hij hjLength
    let P := RlcTwoChannelFullPhysicalRowOneOriginalParityContact
      gamma' p q p' q'
    ∃ a ∈ H.support, P a := by
  rcases
      rlc_twoChannelFullPhysical_wallFamilyRowOne_originalParity_HContact_or_residue
        hn c hc hx hy hzRight hxz hyAxis hrow hurv hulv hpq hpq'
          hpqAdj hpqAdj' hpShift hpShift' horder hRArc hLArc i j
            hiLength hij hjLength with hH | hresidue'
  · exact hH
  · exact False.elim (hresidue hresidue')


theorem rlc_twoChannelFullPhysical_rowOneBracket_shiftedReach_cases
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {z a : Site 2} (hzRight : z ∈ rlc_pathVertices gamma.1)
    (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (haBracket : phb_doubleDualShift a ∈
      (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).support) :
    (∃ w ∈ rlc_pathVertices gamma.1, a = rlc_flipX w) ∨
      ∃ w ∈ rlc_pathVertices gamma'.1, a = rlc_flipX w := by
  have haBox := rlc_twoChannelFullReachSet_subset_box
    gamma gamma' omega haReach
  rcases rlc_bookRowOnePhysicalTraceNetworkBracket_support_cases
      gamma gamma' hzRight haBracket with
    ⟨w, hwRight, hshift⟩ | ⟨w, hwDetour, hshift⟩ |
      ⟨w, hwLeft, hshift⟩
  · exact Or.inl ⟨w, hwRight,
      (rlc_doubleDualShift_eq_dualReflect_symm_iff a w).1 hshift⟩
  · have haw : a = rlc_flipX w :=
      (rlc_doubleDualShift_eq_dualReflect_symm_iff a w).1 hshift
    have hwBox : w ∈ rect (-2 * n) (2 * n) (-n) n := by
      rw [haw] at haBox
      exact (rlc_mem_connectorBox_flipX w).mpr haBox
    by_cases hw0 : 0 ≤ w 0
    · have hwRightBox : w ∈ rect 0 (2 * n) (-n) n := by
        rw [mem_rect] at hwBox ⊢
        omega
      have hwEnd :=
        rlc_bookExteriorEndpointDetour_meets_rightBox_only_endpoint
          hn gamma gamma' hwDetour hwRightBox
      exact Or.inl ⟨w, by
        rw [hwEnd]
        exact rlc_connector_path_end_mem_vertices gamma.1, haw⟩
    · have hwLeftBox : w ∈ rect (-2 * n) 0 (-n) n := by
        rw [mem_rect] at hwBox ⊢
        omega
      have hwStart :=
        rlc_bookExteriorEndpointDetour_meets_leftBox_only_endpoint
          hn gamma gamma' hwDetour hwLeftBox
      exact Or.inr ⟨w, by
        rw [hwStart]
        exact rlc_path_start_mem_vertices gamma'.1, haw⟩
  · exact Or.inr ⟨w, hwLeft,
      (rlc_doubleDualShift_eq_dualReflect_symm_iff a w).1 hshift⟩


theorem
    rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection_classified
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u z a b ur vr ul vl p p' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (H : (hypercubicLattice 2).Walk a b)
    (hHB : H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).support)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
    (w : (hypercubicLattice 2).Walk p p')
    (T : (hypercubicLattice 2).Walk vr vl)
    (hwReach : ∀ r ∈ w.support,
      r ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hTprov : ∀ v ∈ T.support,
      v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
        ∃ r ∈ w.support, phb_doubleDualShift r = v)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    {v : Site 2} (hvH : v ∈ H.support) (hvT : v ∈ T.support) :
    v = a ∨ v = b ∨
      ∃ r ∈ w.support,
        phb_doubleDualShift r = v ∧
          (r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) ∧
          ((∃ q ∈ rlc_pathVertices gamma.1, r = rlc_flipX q) ∨
            ∃ q ∈ rlc_pathVertices gamma'.1, r = rlc_flipX q) := by
  rcases rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection
      c hcycle H hclean w T hwReach hTprov hurv hulv hvH hvT with
    hva | hvb | ⟨r, hrw, hrv, hrContact⟩
  · exact Or.inl hva
  · exact Or.inr (Or.inl hvb)
  · refine Or.inr (Or.inr ⟨r, hrw, hrv, hrContact, ?_⟩)
    exact rlc_twoChannelFullPhysical_rowOneBracket_shiftedReach_cases
      hn hzRight (hwReach r hrw) (by rw [hrv]; exact hHB hvH)


theorem
    rlc_twoChannelFullPhysical_reachable_reflectedLeft_intersection_or_exclusive
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {a w : Site 2}
    (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hwLeft : w ∈ rlc_pathVertices gamma'.1)
    (haw : a = rlc_flipX w) :
    a ∈ rlc_pathVertices gamma.1 ∨
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
        gamma gamma' a := by
  by_cases haRight : a ∈ rlc_pathVertices gamma.1
  · exact Or.inl haRight
  · right
    have haLeft : a ∉ rlc_pathVertices gamma'.1 := by
      intro haLeft
      exact (rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
        gamma gamma' omega hno haLeft) haReach
    have haPos : 0 < a 0 := by
      have hwBox := rlc_pathVertex_mem_rect gamma'.1 hwLeft
      rw [mem_rect] at hwBox
      have hcoord : a 0 = -w 0 := by rw [haw]; rfl
      by_contra hnot
      have hw0 : w 0 = 0 := by omega
      have hwAxis := hfaith.left_axis_unique hwLeft hw0
      apply haLeft
      rw [haw, hwAxis,
        rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2]
      exact rlc_connector_path_end_mem_vertices gamma'.1
    exact ⟨haPos, ⟨w, hwLeft, haw⟩, haRight, haLeft⟩


theorem rlc_bookRowOnePhysicalTraceNetworkBracket_axisSource_not_mem
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {z : Site 2} (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1) :
    phb_doubleDualShift (gamma.1.1 : Site 2) ∉
      (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).support := by
  intro hmem
  simp only [rlc_bookRowOnePhysicalTraceNetworkBracket,
    SimpleGraph.Walk.support_copy] at hmem
  let S := rlc_bookSimpleTraceNetworkBracket gamma gamma' hzRight
    (s := rlc_flipX (gamma'.1.2.1 : Site 2))
      (rlc_bookRowOne_flippedLeftEndpoint_mem gamma')
  change phb_doubleDualShift (gamma.1.1 : Site 2) ∈
    (S.map rlc_dualReflectSymmLatticeHom).support at hmem
  rw [SimpleGraph.Walk.support_map rlc_dualReflectSymmLatticeHom S,
    List.mem_map] at hmem
  obtain ⟨w, hw, hshift⟩ := hmem
  have haxisShift : phb_doubleDualShift (gamma.1.1 : Site 2) =
      rlc_dualReflect.symm (gamma.1.1 : Site 2) := by
    calc
      phb_doubleDualShift (gamma.1.1 : Site 2) =
          phb_doubleDualShift (rlc_flipX (gamma.1.1 : Site 2)) :=
        congrArg phb_doubleDualShift
          (rlc_flipX_eq_self_of_zero gamma.1.1.2.2).symm
      _ = rlc_dualReflect.symm (gamma.1.1 : Site 2) :=
        rlc_doubleDualShift_flipX_eq_dualReflect_symm _
  have hwStart : w = (gamma.1.1 : Site 2) := by
    apply rlc_dualReflect.symm.injective
    exact hshift.trans haxisShift
  subst w
  dsimp only [S, rlc_bookSimpleTraceNetworkBracket] at hw
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hw
  rcases hw with (hwRight | hwDetour) | hwLeft
  · let W := rlc_ambientCrossingWalk gamma.1
    have hzW : z ∈ W.support :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).2
        hzRight
    have hstartW : (gamma.1.1 : Site 2) ∈ W.support :=
      W.start_mem_support
    have hidx :=
      (rlc_isPath_mem_dropUntil_iff_idxOf_le W
        (rlc_ambientCrossingWalk_isPath gamma.1) hzW hstartW).1 hwRight
    have hzIdx : W.support.idxOf z = 0 := by
      rw [rlc_walk_idxOf_start W] at hidx
      omega
    have hzGet := W.getVert_support_idxOf hzW
    have hzStart : z = (gamma.1.1 : Site 2) := by
      rw [hzIdx] at hzGet
      simpa using hzGet.symm
    have hzLeft' : z ∈ rlc_pathVertices gamma'.1 := by
      rw [rlc_flipX_eq_self_of_zero (hzStart ▸ gamma.1.1.2.2)] at hzLeft
      exact hzLeft
    exact hfaith.traceVertices_disjoint hzRight hzLeft'
  · have hstartBox : (gamma.1.1 : Site 2) ∈
        rect 0 (2 * n) (-n) n := by
      have hbox := rlc_pathVertex_mem_rect gamma.1
        (rlc_path_start_mem_vertices gamma.1)
      rw [mem_rect] at hbox ⊢
      omega
    have hends :=
      rlc_bookExteriorEndpointDetour_meets_rightBox_only_endpoint
        hn gamma gamma' hwDetour hstartBox
    have hcoord := congrArg (fun q : Site 2 => q 0) hends
    have hleft := gamma.1.1.2.2
    have hright := gamma.1.2.1.2.2
    change (gamma.1.1 : Site 2) 0 =
      (gamma.1.2.1 : Site 2) 0 at hcoord
    rw [hleft, hright] at hcoord
    omega
  · exact hfaith.traceVertices_disjoint
      (rlc_path_start_mem_vertices gamma.1)
      ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma'.1 (gamma.1.1 : Site 2)).1
          ((rlc_ambientCrossingWalk gamma'.1).support_takeUntil_subset_support
            ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1
              (rlc_flipX (rlc_flipX (gamma'.1.2.1 : Site 2)))).2
                (rlc_bookRowOne_flippedLeftEndpoint_mem gamma')) hwLeft))


theorem
    rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection_exactLocations
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {u z a b ur vr ul vl p p' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (H : (hypercubicLattice 2).Walk a b)
    (hHB : H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).support)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
    (w : (hypercubicLattice 2).Walk p p')
    (T : (hypercubicLattice 2).Walk vr vl)
    (hwReach : ∀ r ∈ w.support,
      r ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hTprov : ∀ v ∈ T.support,
      v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
        ∃ r ∈ w.support, phb_doubleDualShift r = v)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    {v : Site 2} (hvH : v ∈ H.support) (hvT : v ∈ T.support) :
    v = a ∨ v = b ∨
      ∃ r ∈ w.support,
        phb_doubleDualShift r = v ∧
          (r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) ∧
          (RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
              gamma gamma' r ∨
            (r ∈ rlc_pathVertices gamma.1 ∧
              ∃ q ∈ rlc_pathVertices gamma'.1, r = rlc_flipX q) ∨
            RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
              gamma gamma' r) := by
  rcases
      rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection_classified
        hn c hcycle hzRight H hHB hclean w T hwReach hTprov hurv hulv
          hvH hvT with
    hva | hvb | ⟨r, hrw, hrv, hrContact, hrRight | hrLeft⟩
  · exact Or.inl hva
  · exact Or.inr (Or.inl hvb)
  · obtain ⟨q, hqRight, hrq⟩ := hrRight
    rcases
        rlc_twoChannelFullPhysical_reachable_reflectedRight_axis_or_exclusive
          hfaith hno (hwReach r hrw) hqRight hrq with
      hrAxis | hrExclusive
    · exact False.elim
        ((rlc_bookRowOnePhysicalTraceNetworkBracket_axisSource_not_mem
          hn hfaith hzRight hzLeft) (by
            rw [← hrAxis, hrv]
            exact hHB hvH))
    · exact Or.inr (Or.inr
        ⟨r, hrw, hrv, hrContact, Or.inl hrExclusive⟩)
  · obtain ⟨q, hqLeft, hrq⟩ := hrLeft
    rcases
        rlc_twoChannelFullPhysical_reachable_reflectedLeft_intersection_or_exclusive
          hfaith hno (hwReach r hrw) hqLeft hrq with
      hrRight | hrExclusive
    · exact Or.inr (Or.inr ⟨r, hrw, hrv, hrContact,
        Or.inr (Or.inl ⟨hrRight, q, hqLeft, hrq⟩)⟩)
    · exact Or.inr (Or.inr ⟨r, hrw, hrv, hrContact,
        Or.inr (Or.inr hrExclusive)⟩)


theorem
    rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection_rightArcBadLocation
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {u z a b ur vr ul vl p p' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (H : (hypercubicLattice 2).Walk a b)
    (hHB : H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).support)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
    (w : (hypercubicLattice 2).Walk p p')
    (T : (hypercubicLattice 2).Walk vr vl)
    (hwReach : ∀ r ∈ w.support,
      r ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hTprov : ∀ v ∈ T.support,
      v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
        ∃ r ∈ w.support, phb_doubleDualShift r = v)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    {v : Site 2} (hvH : v ∈ H.support) (hvT : v ∈ T.support) :
    v = a ∨ v = b ∨
      ∃ r ∈ w.support,
        phb_doubleDualShift r = v ∧
          (r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) ∧
          RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' r := by
  rcases
      rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection_exactLocations
        hn hfaith hno c hcycle hzRight hzLeft H hHB hclean w T hwReach
          hTprov hurv hulv hvH hvT with
    hva | hvb | ⟨r, hrw, hrv, hrContact, hrRight | hrBoth | hrLeft⟩
  · exact Or.inl hva
  · exact Or.inr (Or.inl hvb)
  · exact Or.inr (Or.inr ⟨r, hrw, hrv, hrContact,
      Or.inr (Or.inr (Or.inl hrRight))⟩)
  · exact Or.inr (Or.inr ⟨r, hrw, hrv, hrContact, Or.inl hrBoth.1⟩)
  · exact Or.inr (Or.inr ⟨r, hrw, hrv, hrContact,
      Or.inr (Or.inl hrLeft)⟩)


theorem
    rlc_twoChannelFullPhysical_rowOne_cleanSeparator_shiftedSourceVertex_rightArcBadLocation
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {u z a b ur vr ul vl p p' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (H : (hypercubicLattice 2).Walk a b)
    (hHB : H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).support)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
    (w : (hypercubicLattice 2).Walk p p')
    (T : (hypercubicLattice 2).Walk vr vl)
    (hwReach : ∀ r ∈ w.support,
      r ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hwT : ∀ r ∈ w.support,
      phb_doubleDualShift r ∈ T.support)
    (hTprov : ∀ v ∈ T.support,
      v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
        ∃ r ∈ w.support, phb_doubleDualShift r = v)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    {r : Site 2} (hrw : r ∈ w.support)
    (hrH : phb_doubleDualShift r ∈ H.support) :
    phb_doubleDualShift r = a ∨ phb_doubleDualShift r = b ∨
      ((r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) ∧
        RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' r) := by
  rcases
      rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection_rightArcBadLocation
        hn hfaith hno c hcycle hzRight hzLeft H hHB hclean w T hwReach
          hTprov hurv hulv hrH (hwT r hrw) with
    hra | hrb | ⟨s, _hsw, hsr, hsContact, hsBad⟩
  · exact Or.inl hra
  · exact Or.inr (Or.inl hrb)
  · have hsr' : s = r := phb_doubleDualEquiv.injective hsr
    subst s
    exact Or.inr (Or.inr ⟨hsContact, hsBad⟩)


theorem
    rlc_twoChannelFullPhysical_rowOne_shiftedSourceSubwalk_insideOutside_rightArcBad_or_cycleContact
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {u z a b ur vr ul vl p p' s t : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (H : (hypercubicLattice 2).Walk a b)
    (hHB : H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).support)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
    (w : (hypercubicLattice 2).Walk p p')
    (T : (hypercubicLattice 2).Walk vr vl)
    (hwReach : ∀ r ∈ w.support,
      r ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hwT : ∀ r ∈ w.support,
      phb_doubleDualShift r ∈ T.support)
    (hTprov : ∀ v ∈ T.support,
      v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
        ∃ r ∈ w.support, phb_doubleDualShift r = v)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    (P : (hypercubicLattice 2).Walk s t)
    (hPprov : ∀ v ∈ P.support,
      ∃ r ∈ w.support, phb_doubleDualShift r = v)
    (hsInside : s ∈ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))
    (htOutside : t ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) :
    (∃ r ∈ w.support, phb_doubleDualShift r ∈ c.support) ∨
      ∃ r ∈ w.support,
        (r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) ∧
          RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' r := by
  have hcontact :=
    rlc_exteriorChord_inside_to_outside_path_meets_chord_or_cycleArc
      (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
      c ha hb H P hsInside htOutside
  rcases hcontact with ⟨v, hvP, hvH | hvArc⟩ |
      ⟨v, hvP, hvH | hvArc⟩
  · obtain ⟨r, hrw, hrv⟩ := hPprov v hvP
    have hrClass :=
      rlc_twoChannelFullPhysical_rowOne_cleanSeparator_shiftedSourceVertex_rightArcBadLocation
        hn hfaith hno c hcycle hzRight hzLeft H hHB hclean w T hwReach
          hwT hTprov hurv hulv hrw (by simpa [hrv] using hvH)
    rcases hrClass with hra | hrb | hrBad
    · exact Or.inl ⟨r, hrw, by simpa [hra] using ha⟩
    · exact Or.inl ⟨r, hrw, by simpa [hrb] using hb⟩
    · exact Or.inr ⟨r, hrw, hrBad⟩
  · obtain ⟨r, hrw, hrv⟩ := hPprov v hvP
    exact Or.inl ⟨r, hrw, by
      rw [hrv]
      exact rlc_orderedContourArc_support_subset c ha hb hvArc⟩
  · obtain ⟨r, hrw, hrv⟩ := hPprov v hvP
    have hrClass :=
      rlc_twoChannelFullPhysical_rowOne_cleanSeparator_shiftedSourceVertex_rightArcBadLocation
        hn hfaith hno c hcycle hzRight hzLeft H hHB hclean w T hwReach
          hwT hTprov hurv hulv hrw (by simpa [hrv] using hvH)
    rcases hrClass with hra | hrb | hrBad
    · exact Or.inl ⟨r, hrw, by simpa [hra] using ha⟩
    · exact Or.inl ⟨r, hrw, by simpa [hrb] using hb⟩
    · exact Or.inr ⟨r, hrw, hrBad⟩
  · obtain ⟨r, hrw, hrv⟩ := hPprov v hvP
    exact Or.inl ⟨r, hrw, by
      rw [hrv]
      exact rlc_complementaryContourArc_support_subset c ha hb hvArc⟩


theorem rlc_pathEdge_endpoint_mem_vertices
    {a b c d : Int} (tau : RlcCrossingPath a b c d)
    {e : Sym2 (Site 2)} (he : e ∈ rlc_pathEdges tau)
    {z : Site 2} (hz : z ∈ e) : z ∈ rlc_pathVertices tau := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hends := rlc_pathEdge_endpoints_mem_vertices tau he
      rw [Sym2.mem_iff] at hz
      rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hends.1
      · exact hends.2


theorem rlc_twoChannelFullPhysical_reachableWalk_open_source_or_rightTrace
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {p p' : Site 2} (w : (hypercubicLattice 2).Walk p p')
    (hwReach : ∀ a ∈ w.support,
      a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    {e : Sym2 (Site 2)} (he : e ∈ w.edges)
    (hsourceOrTrace :
      (∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
        source.1.map Subtype.val = e) ∨
        e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    (∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
      source.1.map Subtype.val = e) ∨ e ∈ rlc_pathEdges gamma.1 := by
  rcases hsourceOrTrace with hsource | htrace
  · exact Or.inl hsource
  · rw [Finset.mem_union] at htrace
    rcases htrace with hright | hleft
    · exact Or.inr hright
    · induction e using Sym2.inductionOn with
      | _ a b =>
          have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1
            (by simpa using hleft)
          exact False.elim
            ((rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
              gamma gamma' omega hno hends.1)
                (hwReach a (w.fst_mem_support_of_mem_edges he)))


theorem rlc_twoChannelFullPhysical_planarEdge_source_or_originalTrace
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) {e : Sym2 (Site 2)}
    (hlat : e ∈ (hypercubicLattice 2).edgeSet)
    (hplanar : e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma') :
    (∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
      source.1.map Subtype.val = e) ∨
        e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab : (hypercubicLattice 2).Adj a b := by
        simpa [SimpleGraph.mem_edgeSet] using hlat
      have haBox := rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
        gamma gamma' hplanar (Sym2.mem_mk_left _ _)
      have hbBox := rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
        gamma gamma' hplanar (Sym2.mem_mk_right _ _)
      let af : RlcConnectorVertex n := ⟨a, by
        simpa [rlc_connectorBox] using haBox⟩
      let bf : RlcConnectorVertex n := ⟨b, by
        simpa [rlc_connectorBox] using hbBox⟩
      have hclosure : (rlc_connectorCentralFaceClosureGraph
          gamma gamma').Adj af bf := by
        exact ⟨by simpa [af, bf] using hab,
          by simpa [af, bf] using hplanar⟩
      rw [rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace]
        at hclosure
      rcases hclosure with hsource | htrace
      · left
        let source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
          ⟨s(af, bf), (SimpleGraph.mem_edgeSet _).2 hsource⟩
        exact ⟨source, by simp [source, af, bf, Sym2.map_mk]⟩
      · exact Or.inr (by simpa [af, bf] using htrace.2)


theorem rlc_twoChannelFullPhysical_sourceMissing_trace_or_notPlanar
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (hmissing : ¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
      (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) :
    rlc_pimsEdgeEquiv (target.1.map Subtype.val) ∈
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨
      rlc_pimsEdgeEquiv (target.1.map Subtype.val) ∉
        rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  by_cases hplanar : rlc_pimsEdgeEquiv (target.1.map Subtype.val) ∈
      rlc_connectorCentralFacePlanarEdges gamma gamma'
  · left
    have htargetLat : target.1.map Subtype.val ∈
        (hypercubicLattice 2).edgeSet := by
      induction hedge : target.1 using Sym2.inductionOn with
      | _ a b =>
          have hab : (rlc_connectorTwoChannelGraph gamma gamma').Adj a b :=
            (SimpleGraph.mem_edgeSet _).1 (hedge ▸ target.2)
          rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
          exact hab.1.elim (fun h => h.1) (fun h => h.1)
    have hpimsLat : rlc_pimsEdgeEquiv (target.1.map Subtype.val) ∈
        (hypercubicLattice 2).edgeSet :=
      rlc_pimsEdgeEquiv_mem_latticeEdge htargetLat
    rcases
        rlc_twoChannelFullPhysical_planarEdge_source_or_originalTrace
          gamma gamma' hpimsLat hplanar with hsource | htrace
    · exact False.elim (hmissing ⟨⟨hsource.choose,
        hsource.choose_spec⟩⟩)
    · exact htrace
  · exact Or.inr hplanar


theorem
    rlc_twoChannelFullPhysical_shiftedSourceMissing_rightTraceContact_or_preimageNotPlanar
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {p p' : Site 2} (w : (hypercubicLattice 2).Walk p p')
    (hwReach : ∀ a ∈ w.support,
      a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    {e : Sym2 (Site 2)} (he : e ∈ w.edges)
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val = Sym2.map rlc_flipX e)
    (hmissing : ¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
      (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) :
    (∃ z ∈ e, z ∈ rlc_pathVertices gamma.1) ∨
      rlc_pimsEdgeEquiv (target.1.map Subtype.val) ∉
        rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  rcases rlc_twoChannelFullPhysical_sourceMissing_trace_or_notPlanar
      target hmissing with htrace | hnotPlanar
  · left
    induction e using Sym2.inductionOn with
    | _ a b =>
        have hab := w.adj_of_mem_edges he
        obtain ⟨z, hzab, hzSource⟩ :=
          rlc_pimsEdgeEquiv_flipXEdge_sharedEndpoint hab
        have hzTarget : z ∈
            rlc_pimsEdgeEquiv (target.1.map Subtype.val) := by
          rw [htarget, Sym2.map_mk]
          exact hzSource
        have hzReach : z ∈
            rlc_twoChannelFullReachSet gamma gamma' omega := by
          rw [Sym2.mem_iff] at hzab
          rcases hzab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hwReach a (w.fst_mem_support_of_mem_edges he)
          · exact hwReach b (w.snd_mem_support_of_mem_edges he)
        rw [Finset.mem_union] at htrace
        rcases htrace with hright | hleft
        · exact ⟨z, hzab,
            rlc_pathEdge_endpoint_mem_vertices gamma.1 hright hzTarget⟩
        · have hzLeft : z ∈ rlc_pathVertices gamma'.1 :=
            rlc_pathEdge_endpoint_mem_vertices gamma'.1 hleft hzTarget
          exact False.elim
            ((rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
              gamma gamma' omega hno hzLeft) hzReach)
  · exact Or.inr hnotPlanar


theorem rlc_pimsEdgeEquiv_flipXEdge_incidentNonopposite
    {a b : Site 2} (hab : (hypercubicLattice 2).Adj a b) :
    ∃ z x y : Site 2,
      s(a, b) = s(z, x) ∧
      rlc_pimsEdgeEquiv s(rlc_flipX a, rlc_flipX b) = s(z, y) ∧
      (hypercubicLattice 2).Adj z x ∧
      (hypercubicLattice 2).Adj z y ∧ x ≠ y ∧
      ¬(x 0 + y 0 = 2 * z 0 ∧ x 1 + y 1 = 2 * z 1) := by
  rcases face_adj_dir hab with hb | hb | hb | hb
  · subst b
    refine ⟨a, ![a 0 + 1, a 1], ![a 0, a 1 - 1], rfl,
      ?_, ?_, ?_, ?_, ?_⟩
    · convert rlc_pimsEdgeEquiv_horizontal (-a 0 - 1) (a 1) using 1 <;>
        simp [rlc_flipX, rlc_flipXFun, Sym2.eq_swap] <;> ring
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · intro h
      have h0 := congrArg (fun z : Site 2 => z 0) h
      simp at h0
    · simp <;> omega
  · subst b
    refine ⟨![a 0 - 1, a 1], a, ![a 0 - 1, a 1 - 1],
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Sym2.eq_swap]
    · convert rlc_pimsEdgeEquiv_horizontal (-a 0) (a 1) using 1 <;>
        simp [rlc_flipX, rlc_flipXFun, Sym2.eq_swap] <;> ring
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · intro h
      have h0 := congrArg (fun z : Site 2 => z 0) h
      simp at h0
    · simp <;> omega
  · subst b
    refine ⟨a, ![a 0, a 1 + 1], ![a 0 - 1, a 1], rfl,
      ?_, ?_, ?_, ?_, ?_⟩
    · convert rlc_pimsEdgeEquiv_vertical (-a 0) (a 1) using 1 <;>
        simp [rlc_flipX, rlc_flipXFun, Sym2.eq_swap] <;> ring
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · intro h
      have h1 := congrArg (fun z : Site 2 => z 1) h
      simp at h1
    · simp <;> omega
  · subst b
    refine ⟨![a 0, a 1 - 1], a, ![a 0 - 1, a 1 - 1],
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Sym2.eq_swap]
    · convert rlc_pimsEdgeEquiv_vertical (-a 0) (a 1 - 1) using 1 <;>
        simp [rlc_flipX, rlc_flipXFun, Sym2.eq_swap] <;> ring
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · simp [hypercubicLattice_adj, Fin.sum_univ_two]
    · intro h
      have h1 := congrArg (fun z : Site 2 => z 1) h
      simp at h1
    · simp <;> omega


theorem rlc_pimsEdgeEquiv_flipXEdge_notPlanar_wall_or_boundary
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) {e : Sym2 (Site 2)}
    (hlat : e ∈ (hypercubicLattice 2).edgeSet)
    (hplanar : e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma')
    (hnotPlanar : rlc_pimsEdgeEquiv (Sym2.map rlc_flipX e) ∉
      rlc_connectorCentralFacePlanarEdges gamma gamma') :
    e ∈ rlc_connectorFourTraceEdges gamma gamma' ∨
      ∃ z ∈ e, z 0 = -2 * n ∨ z 0 = 2 * n ∨
        z 1 = -n ∨ z 1 = n := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      have hab : (hypercubicLattice 2).Adj a b := by
        simpa [SimpleGraph.mem_edgeSet] using hlat
      obtain ⟨z, x, y, hezx, hpims, hzx, hzy, hxy, hnopp⟩ :=
        rlc_pimsEdgeEquiv_flipXEdge_incidentNonopposite hab
      by_cases hwall : s(a, b) ∈
          rlc_connectorFourTraceEdges gamma gamma'
      · exact Or.inl hwall
      · right
        have hplanarZX : s(z, x) ∈
            rlc_connectorCentralFacePlanarEdges gamma gamma' := by
          rw [← hezx]
          exact hplanar
        have hnotPlanarZY : s(z, y) ∉
            rlc_connectorCentralFacePlanarEdges gamma gamma' := by
          rw [← hpims]
          simpa [Sym2.map_mk] using hnotPlanar
        have hnotWallZX : s(z, x) ∉
            rlc_connectorFourTraceEdges gamma gamma' := by
          rwa [← hezx]
        have hcarrier :=
          (rlc_mem_connectorCentralFacePlanarEdges_iff gamma gamma' hzx).1
            hplanarZX
        rcases hcarrier with hwallZX |
            ⟨hzBox, _hxBox, f, hfRegion, hfFlank⟩
        · exact False.elim (hnotWallZX hwallZX)
        · by_cases hzInterior : -2 * n < z 0 ∧ z 0 < 2 * n ∧
              -n < z 1 ∧ z 1 < n
          · exact False.elim (hnotPlanarZY
              (rlc_mem_connectorCentralFacePlanarEdges_of_nonopposite_incident
                gamma gamma' hzx hzy hxy hnopp hzInterior hnotWallZX
                  hfRegion hfFlank))
          · refine ⟨z, ?_, ?_⟩
            · rw [hezx]
              exact Sym2.mem_mk_left _ _
            · simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at hzBox
              rw [mem_rect] at hzBox
              push Not at hzInterior
              omega


theorem rlc_twoChannelFullPhysical_shiftedSourceMissing_location
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {p p' : Site 2} (w : (hypercubicLattice 2).Walk p p')
    (hwReach : ∀ a ∈ w.support,
      a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    {e : Sym2 (Site 2)} (he : e ∈ w.edges)
    (hplanar : e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma')
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val = Sym2.map rlc_flipX e)
    (hmissing : ¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
      (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) :
    (∃ z ∈ e, z ∈ rlc_pathVertices gamma.1) ∨
      e ∈ rlc_connectorFourTraceEdges gamma gamma' ∨
      ∃ z ∈ e, z 0 = -2 * n ∨ z 0 = 2 * n ∨
        z 1 = -n ∨ z 1 = n := by
  rcases
      rlc_twoChannelFullPhysical_shiftedSourceMissing_rightTraceContact_or_preimageNotPlanar
        hno w hwReach he target htarget hmissing with
    hright | hnotPlanar
  · exact Or.inl hright
  · right
    have hlat : e ∈ (hypercubicLattice 2).edgeSet := by
      induction e using Sym2.inductionOn with
      | _ a b =>
          simpa [SimpleGraph.mem_edgeSet] using w.adj_of_mem_edges he
    have hnotPlanar' : rlc_pimsEdgeEquiv (Sym2.map rlc_flipX e) ∉
        rlc_connectorCentralFacePlanarEdges gamma gamma' := by
      rwa [← htarget]
    exact rlc_pimsEdgeEquiv_flipXEdge_notPlanar_wall_or_boundary
      gamma gamma' hlat hplanar hnotPlanar'


theorem rlc_twoChannelFullPhysical_shiftedSourceMissing_exactLocation
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {p p' : Site 2} (w : (hypercubicLattice 2).Walk p p')
    (hwReach : ∀ z ∈ w.support,
      z ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    {e : Sym2 (Site 2)} (he : e ∈ w.edges)
    (hplanar : e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma')
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val = Sym2.map rlc_flipX e)
    (hmissing : ¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
      (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) :
    ∃ z ∈ e,
      RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' z := by
  have hloc := rlc_twoChannelFullPhysical_shiftedSourceMissing_location
    hno w hwReach he hplanar target htarget hmissing
  induction e using Sym2.inductionOn with
  | _ a b =>
      have haReach := hwReach a (w.fst_mem_support_of_mem_edges he)
      rcases hloc with hright | hwall | hboundary
      · obtain ⟨z, hzEdge, hzRight⟩ := hright
        exact ⟨z, hzEdge, Or.inl hzRight⟩
      · rw [rlc_connectorFourTraceEdges, Finset.mem_union] at hwall
        rcases hwall with horiginal | hreflected
        · rw [Finset.mem_union] at horiginal
          rcases horiginal with hright | hleft
          · exact ⟨a, Sym2.mem_mk_left _ _, Or.inl
              (rlc_pathEdge_endpoints_mem_vertices gamma.1 hright).1⟩
          · exact False.elim
              ((rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
                gamma gamma' omega hno
                  (rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft).1)
                    haReach)
        · rw [rlc_connectorReflectedTraceEdges, Finset.mem_union]
            at hreflected
          rcases hreflected with hflipRight | hflipLeft
          · obtain ⟨q, hqRight, haq⟩ :=
              rlc_reflectedPathEdge_endpoint_mem_vertices gamma.1 hflipRight
                (Sym2.mem_mk_left _ _)
            rcases
                rlc_twoChannelFullPhysical_reachable_reflectedRight_axis_or_exclusive
                  hfaith hno haReach hqRight haq with haxis | hexclusive
            · exact ⟨a, Sym2.mem_mk_left _ _, Or.inl (by
                rw [haxis]
                exact rlc_path_start_mem_vertices gamma.1)⟩
            · exact ⟨a, Sym2.mem_mk_left _ _,
                Or.inr (Or.inr (Or.inl hexclusive))⟩
          · obtain ⟨q, hqLeft, haq⟩ :=
              rlc_reflectedPathEdge_endpoint_mem_vertices gamma'.1 hflipLeft
                (Sym2.mem_mk_left _ _)
            rcases
                rlc_twoChannelFullPhysical_reachable_reflectedLeft_intersection_or_exclusive
                  hfaith hno haReach hqLeft haq with hright | hexclusive
            · exact ⟨a, Sym2.mem_mk_left _ _, Or.inl hright⟩
            · exact ⟨a, Sym2.mem_mk_left _ _,
                Or.inr (Or.inl hexclusive)⟩
      · obtain ⟨z, hzEdge, hzBoundary⟩ := hboundary
        exact ⟨z, hzEdge, Or.inr (Or.inr (Or.inr hzBoundary))⟩


theorem rlc_twoChannelFullPhysical_source_notAcross_staticCut_reachSet_extend
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    {u v : RlcConnectorVertex n} (hsource : source.1 = s(u, v))
    (huReach : u.1 ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A source.1) :
    v.1 ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
  have huCut := rlc_twoChannelFullReachSet_subset_staticCut
    gamma gamma' A hAright hAleft huReach
  have huA : u ∈ A :=
    (rlc_twoChannelFullPhysicalLiftVertexCut_mem A u).mp
      (by simpa [hsource] using huCut)
  have huvSame :=
    (rlc_twoChannelFullPhysical_not_crossesCut_iff_monochromatic
      A source.1).1 hnotCross u v hsource
  have hvA : v ∈ A := huvSame.mp huA
  have hopenConfig :
      rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A source =
        true :=
    (rlc_twoChannelFullPhysicalCutInteriorConfig_true_iff
      gamma gamma' A source).2 (by
        intro a b hab
        rw [hsource, Sym2.eq_iff] at hab
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨huA, hvA⟩
        · exact ⟨hvA, huA⟩)
  have hopenAmbient : rlc_twoChannelFullAmbientConfig gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
        s(u.1, v.1) = true := by
    have hsourceMap := congrArg (Sym2.map Subtype.val) hsource
    simp only [Sym2.map_mk] at hsourceMap
    rw [← hsourceMap, rlc_twoChannelFullAmbientConfig_source]
    exact hopenConfig
  have huvAdj : (hypercubicLattice 2).Adj u.1 v.1 := by
    have huvGraph : (rlc_connectorTwoChannelGraph gamma gamma').Adj u v := by
      exact (SimpleGraph.mem_edgeSet _).1 (hsource ▸ source.2)
    exact huvGraph.1.elim (fun h ↦ h.1) (fun h ↦ h.1)
  exact rlc_twoChannelFullReachSet_extend gamma gamma'
    (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
      huReach v.2 huvAdj hopenAmbient


theorem
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_endpoints_reachable
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {a b : Site 2} (hab : (hypercubicLattice 2).Adj a b)
    (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hbReach : b ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val =
      s(rlc_flipX a, rlc_flipX b))
    (physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma')
    (hphysical : physical.1 = target)
    (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
      (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
    ∀ z ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
        Subtype.val,
      z ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
  let source := rlc_twoChannelFullPhysicalSourceEdge physical
  have hsourceMap : source.1.map Subtype.val =
      rlc_pimsEdgeEquiv s(rlc_flipX a, rlc_flipX b) := by
    calc
      source.1.map Subtype.val =
          rlc_pimsEdgeEquiv (physical.1.1.map Subtype.val) :=
        rlc_twoChannelFullPhysicalSourceEdge_map physical
      _ = rlc_pimsEdgeEquiv (target.1.map Subtype.val) := by
        rw [hphysical]
      _ = _ := by rw [htarget]
  obtain ⟨z, hzab, hzSource⟩ :=
    rlc_pimsEdgeEquiv_flipXEdge_sharedEndpoint hab
  have hzReach : z ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
    rw [Sym2.mem_iff] at hzab
    rcases hzab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact haReach
    · exact hbReach
  rw [← hsourceMap] at hzSource
  induction hedge : source.1 using Sym2.inductionOn with
  | _ u v =>
      have huv : source.1 = s(u, v) := hedge
      rw [hedge, Sym2.map_mk, Sym2.mem_iff] at hzSource
      intro q hq
      rw [Sym2.map_mk, Sym2.mem_iff] at hq
      rcases hzSource with hzu | hzv <;>
        rcases hq with hqu | hqv
      · simpa [hqu, hzu] using hzReach
      · simpa [hqv] using
          rlc_twoChannelFullPhysical_source_notAcross_staticCut_reachSet_extend
            A hAright hAleft source huv (by simpa [hzu] using hzReach)
              hnotCross
      · simpa [hqu] using
          rlc_twoChannelFullPhysical_source_notAcross_staticCut_reachSet_extend
            A hAright hAleft source (huv.trans Sym2.eq_swap)
              (by simpa [hzv] using hzReach) hnotCross
      · simpa [hqv, hzv] using hzReach


theorem
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_noOutsideEndpoint
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {a b : Site 2} (hab : (hypercubicLattice 2).Adj a b)
    (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hbReach : b ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val =
      s(rlc_flipX a, rlc_flipX b))
    (physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma')
    (hphysical : physical.1 = target)
    (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
      (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
    ¬∃ z ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
          Subtype.val,
        z ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
  intro hout
  obtain ⟨z, hzSource, hzOut⟩ := hout
  have hzReach :=
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_endpoints_reachable
      A hAright hAleft hab haReach hbReach target htarget physical
        hphysical hnotCross z hzSource
  exact hzOut
    (rlc_twoChannelFullReachSet_subset_filled gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
        hzReach)


theorem rlc_twoChannelFullPhysical_shiftedSourceEdge_status_reachable
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {p p' : Site 2} (w : (hypercubicLattice 2).Walk p p')
    (hwReach : ∀ a ∈ w.support,
      a ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    {e₀ : Sym2 (Site 2)} (he₀ : e₀ ∈ w.edges)
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val = Sym2.map rlc_flipX e₀)
    (hstatus :
      (¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
          (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) ∨
        ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
          physical.1 = target ∧
            ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
              (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
    (¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
        (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) ∨
      ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
        physical.1 = target ∧
          ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
            (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧
          ∀ z ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
              Subtype.val,
            z ∈ rlc_twoChannelFullReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A) := by
  rcases hstatus with hmissing | ⟨physical, hphysical, hnotCross⟩
  · exact Or.inl hmissing
  · right
    refine ⟨physical, hphysical, hnotCross, ?_⟩
    induction e₀ using Sym2.inductionOn with
    | _ a b =>
        have hab := w.adj_of_mem_edges he₀
        have haReach := hwReach a (w.fst_mem_support_of_mem_edges he₀)
        have hbReach := hwReach b (w.snd_mem_support_of_mem_edges he₀)
        apply
          rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_endpoints_reachable
            A hAright hAleft hab haReach hbReach target
              (by simpa [Sym2.map_mk] using htarget) physical hphysical
                hnotCross


theorem rlc_twoChannelFullPhysical_shiftedSourceEdge_status_localized
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {p p' : Site 2} (w : (hypercubicLattice 2).Walk p p')
    (hwReach : ∀ a ∈ w.support,
      a ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    {e : Sym2 (Site 2)} (he : e ∈ w.edges)
    (hplanar : e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma')
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val = Sym2.map rlc_flipX e)
    (hstatus :
      (¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
          (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) ∨
        ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
          physical.1 = target ∧
            ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
              (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
    ((∃ z ∈ e, z ∈ rlc_pathVertices gamma.1) ∨
        e ∈ rlc_connectorFourTraceEdges gamma gamma' ∨
        ∃ z ∈ e, z 0 = -2 * n ∨ z 0 = 2 * n ∨
          z 1 = -n ∨ z 1 = n) ∨
      ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
        physical.1 = target ∧
          ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
            (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧
          ∀ z ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
              Subtype.val,
            z ∈ rlc_twoChannelFullReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A) := by
  rcases rlc_twoChannelFullPhysical_shiftedSourceEdge_status_reachable
      A hAright hAleft w hwReach he target htarget hstatus with
    hmissing | hphysical
  · exact Or.inl
      (rlc_twoChannelFullPhysical_shiftedSourceMissing_location
        (rlc_twoChannelFullPhysicalCutInteriorConfig_failure
          gamma gamma' A hAright hAleft)
        w hwReach he hplanar target htarget hmissing)
  · exact Or.inr hphysical


theorem rlc_twoChannelFullPhysical_shiftedSourceEdge_status_exactLocations
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {p p' : Site 2} (w : (hypercubicLattice 2).Walk p p')
    (hwReach : ∀ a ∈ w.support,
      a ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    {e : Sym2 (Site 2)} (he : e ∈ w.edges)
    (hplanar : e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma')
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val = Sym2.map rlc_flipX e)
    (hstatus :
      (¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
          (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) ∨
        ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
          physical.1 = target ∧
            ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
              (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
    (∃ z ∈ e,
        RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' z) ∨
      ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
        physical.1 = target ∧
          ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
            (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧
          ∀ z ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
              Subtype.val,
            z ∈ rlc_twoChannelFullReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A) := by
  rcases rlc_twoChannelFullPhysical_shiftedSourceEdge_status_reachable
      A hAright hAleft w hwReach he target htarget hstatus with
    hmissing | hphysical
  · exact Or.inl
      (rlc_twoChannelFullPhysical_shiftedSourceMissing_exactLocation
        hfaith
        (rlc_twoChannelFullPhysicalCutInteriorConfig_failure
          gamma gamma' A hAright hAleft)
        w hwReach he hplanar target htarget hmissing)
  · exact Or.inr hphysical


end
end StatMech.Universality
