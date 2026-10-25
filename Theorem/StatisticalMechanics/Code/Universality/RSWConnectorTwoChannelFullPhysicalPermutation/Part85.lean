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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part84
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelFullPhysical_rowOneCleanExactSourceSpliceEdgeResidue_localized
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {u a b ur vr ul vl p p' f g : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (H : (hypercubicLattice 2).Walk a b)
    (w : (hypercubicLattice 2).Walk p p')
    (hwReach : ∀ z ∈ w.support,
      z ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hres : RlcTwoChannelFullPhysicalRowOneCleanExactSourceSpliceEdgeResidue
      gamma gamma' A B c H ur vr ul vl w f g) :
    RlcTwoChannelFullPhysicalRowOneLocalizedExactSourceSpliceEdgeResidue
      gamma gamma' A B c H ur vr ul vl w f g := by
  change (s(f, g) = s(ur, vr) ∧ _) ∨
    (s(f, g) = s(ul, vl) ∧ _) ∨ _ ∨ _ ∨ _ at hres
  change (s(f, g) = s(ur, vr) ∧ _) ∨
    (s(f, g) = s(ul, vl) ∧ _) ∨ _ ∨ _ ∨ _
  rcases hres with hright | hleft | htetherR | hsource | htetherL
  · exact Or.inl hright
  · exact Or.inr (Or.inl hleft)
  · exact Or.inr (Or.inr (Or.inl htetherR))
  · rcases hsource with ⟨e₀, he₀, hshift, hopen, hsourceOrTrace,
      hplanar, hcross, target, htarget, hstatus⟩
    have hno := rlc_twoChannelFullPhysicalCutInteriorConfig_failure
      gamma gamma' A hAright hAleft
    have hsourceRight :=
      rlc_twoChannelFullPhysical_reachableWalk_open_source_or_rightTrace
        hno w hwReach he₀ hsourceOrTrace
    have hstatus' :=
      rlc_twoChannelFullPhysical_shiftedSourceEdge_status_exactLocations
        hfaith A hAright hAleft w hwReach he₀ hplanar target htarget hstatus
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨e₀, he₀, hshift, hopen, hsourceRight, hplanar, hcross,
        target, htarget, hstatus'⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr htetherL)))


theorem
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedLocalizedSourceSplice_cleanSeparator
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
    (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {u z x y ur vr ul vl : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hcycle : c.IsCycle) (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk y ul)
    (hxz : rlc_dualReflect x = z)
    (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ul vl) :
    ∃ (p q p' q' : Site 2)
      (w : (hypercubicLattice 2).Walk p p')
      (T : (hypercubicLattice 2).Walk vr vl)
      (V : (hypercubicLattice 2).Walk
        (rlc_dualReflect.symm (gamma.1.1 : Site 2))
        (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2)))
      (f g : Site 2) (i j : Nat)
      (H : (hypercubicLattice 2).Walk
        ((rlc_bookRowOnePhysicalTraceNetworkBracket
          gamma gamma' hzRight).getVert i)
        ((rlc_bookRowOnePhysicalTraceNetworkBracket
          gamma gamma' hzRight).getVert j))
      (hi : (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).getVert i ∈ c.support)
      (hj : (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).getVert j ∈ c.support),
      sharedPrimalEdge ur vr = s(p, q) ∧
        sharedPrimalEdge ul vl = s(p', q') ∧
        (hypercubicLattice 2).Adj p q ∧
        (hypercubicLattice 2).Adj p' q' ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
        p' ∈ rlc_twoChannelFullReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
        q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
        (∀ a ∈ w.support,
          a ∈ rlc_twoChannelFullReachSet gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)) ∧
        (∀ a ∈ w.support,
          phb_doubleDualShift a ∈ T.support) ∧
        (∀ e ∈ w.edges,
          Sym2.map phb_doubleDualShift e ∈ T.edges) ∧
        (∀ a ∈ T.support,
          a = vr ∨ a = ur ∨ a = ul ∨ a = vl ∨
            ∃ b ∈ w.support, phb_doubleDualShift b = a) ∧
        (∀ e ∈ T.edges,
          (∀ a ∈ e, a = vr ∨ a = ur ∨
            a = phb_doubleDualShift p) ∨
          (∃ e₀ ∈ w.edges, Sym2.map phb_doubleDualShift e₀ = e) ∨
          ∀ a ∈ e, a = vl ∨ a = ul ∨
            a = phb_doubleDualShift p') ∧
        s(f, g) ∈ V.edges ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut
          (rlc_twoChannelFullPhysicalLiftVertexCut B)
            s(rlc_dualReflect f, rlc_dualReflect g) ∧
        ((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) <
          ((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul) ∧
        H.IsPath ∧
        rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∈
          H.support ∧
        rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∉
          c.support ∧
        H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket
          gamma gamma' hzRight).support ∧
        (∀ v ∈ H.support,
          v = (rlc_bookRowOnePhysicalTraceNetworkBracket
              gamma gamma' hzRight).getVert i ∨
            v = (rlc_bookRowOnePhysicalTraceNetworkBracket
              gamma gamma' hzRight).getVert j ∨
            (v ∉ c.support ∧
              v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
                (rlc_twoChannelFullFilledReachSet gamma gamma'
                  (rlc_twoChannelFullPhysicalCutInteriorConfig
                    gamma gamma' A)))))) ∧
        (H.append ((rlc_orderedContourArc c hi hj).mapLe
          (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A)))).reverse).IsCycle ∧
        (H.append ((rlc_complementaryContourArc c hi hj).mapLe
          (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A)))).reverse).IsCycle ∧
        RlcTwoChannelFullPhysicalRowOneLocalizedExactSourceSpliceEdgeResidue
          gamma gamma' A B c H ur vr ul vl w f g := by
  obtain ⟨p, q, p', q', w, T, V, f, g, i, j, H, hi, hj,
      hpq, hpq', hpqAdj, hpqAdj', hpReach, hpReach', hqOut, hqOut',
      hwReach, hwT, heT, hTprov, hTedge, hfgV, hcross, horder, hHPath, hdH, hdC,
      hHB, hclean, hordered, hcomplementary, hres⟩ :=
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedExactSourceSplice_cleanSeparator
      hn hfaith A B hAright hAleft hBright hBleft hnoPair c hcycle hx hy
        hzRight hzLeft hxPath hyPath qr ql hxz hyAxis hrow hurv hulv
  have hres' :=
    rlc_twoChannelFullPhysical_rowOneCleanExactSourceSpliceEdgeResidue_localized
      hfaith A B hAright hAleft c H w hwReach hres
  exact ⟨p, q, p', q', w, T, V, f, g, i, j, H, hi, hj,
    hpq, hpq', hpqAdj, hpqAdj', hpReach, hpReach', hqOut, hqOut',
    hwReach, hwT, heT, hTprov, hTedge, hfgV, hcross, horder, hHPath, hdH, hdC,
    hHB, hclean, hordered, hcomplementary, hres'⟩


theorem rlc_twoChannelFullPhysical_rowOne_reachableShift_tether_terminal
    {f g ur vr ul vl p p' : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g)
    (hpShift : phb_doubleDualShift p = vr)
    (hpShift' : phb_doubleDualShift p' = vl)
    (htether :
      ((s(f, g) = s(vr, phb_doubleDualShift p) ∨
          s(f, g) = s(ur, phb_doubleDualShift p)) ∨
        (s(f, g) = s(vl, phb_doubleDualShift p') ∨
          s(f, g) = s(ul, phb_doubleDualShift p')))) :
    s(f, g) = s(ur, vr) ∨ s(f, g) = s(ul, vl) := by
  rcases htether with (hloop | hright) | hloop | hleft
  · rw [hpShift, Sym2.eq_iff] at hloop
    rcases hloop with ⟨hf, hg⟩ | ⟨hf, hg⟩
    · exact False.elim (hfg.ne (hf.trans hg.symm))
    · exact False.elim (hfg.ne (hf.trans hg.symm))
  · exact Or.inl (by simpa [hpShift] using hright)
  · rw [hpShift', Sym2.eq_iff] at hloop
    rcases hloop with ⟨hf, hg⟩ | ⟨hf, hg⟩
    · exact False.elim (hfg.ne (hf.trans hg.symm))
    · exact False.elim (hfg.ne (hf.trans hg.symm))
  · exact Or.inr (by simpa [hpShift'] using hleft)


theorem
    rlc_twoChannelFullPhysical_noPair_rowOne_cleanSeparator_terminalBranch
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {u a b x y ur vr ul vl f g : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))))
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk y ul)
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ul vl)
    (hcross : rlc_twoChannelFullPhysicalEdgeCrossesCut
      (rlc_twoChannelFullPhysicalLiftVertexCut B)
        s(rlc_dualReflect f, rlc_dualReflect g))
    (hterminal : s(f, g) = s(ur, vr) ∨ s(f, g) = s(ul, vl)) :
    (s(f, g) = s(ur, vr) ∧
        RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
          gamma gamma' A B c H ur vr) ∨
      (s(f, g) = s(ul, vl) ∧
        RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
          gamma gamma' A B c H ul vl) := by
  rcases hterminal with hright | hleft
  · have hmap := congrArg (Sym2.map rlc_dualReflect) hright
    simp only [Sym2.map_mk] at hmap
    have hfailure :=
      rlc_twoChannelFullPhysical_noPair_exclusiveReflectedLeft_terminalFailure
        gamma gamma' A B hAright hAleft hnoPair hurv hrow.2.1 (by
          rw [← hmap]
          exact hcross)
    have hexact :=
      rlc_twoChannelFullPhysical_reflectedLeftTerminalFailure_exactResidue
        hn gamma gamma' A B hAright hAleft hurv hrow.2.1 hfailure
    exact Or.inl ⟨hright, by
      simpa [RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact]
        using
          rlc_twoChannelFullPhysical_reflectedLeftTerminalExactResidue_cleanSeparatorContact
            A B c hcycle ha hb H hclean hexact⟩
  · have hmap := congrArg (Sym2.map rlc_dualReflect) hleft
    simp only [Sym2.map_mk] at hmap
    have hfailure :=
      rlc_twoChannelFullPhysical_noPair_exclusiveReflectedLeft_terminalFailure
        gamma gamma' A B hAright hAleft hnoPair hulv hrow.2.2.2 (by
          rw [← hmap]
          exact hcross)
    have hexact :=
      rlc_twoChannelFullPhysical_reflectedLeftTerminalFailure_exactResidue
        hn gamma gamma' A B hAright hAleft hulv hrow.2.2.2 hfailure
    exact Or.inr ⟨hleft, by
      simpa [RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact]
        using
          rlc_twoChannelFullPhysical_reflectedLeftTerminalExactResidue_cleanSeparatorContact
            A B c hcycle ha hb H hclean hexact⟩


theorem
    rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_identifySource
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A B : Set (RlcConnectorVertex n))
    {u a b f g p q : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (H : (hypercubicLattice 2).Walk a b)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (hpq : sharedPrimalEdge f g = s(p, q))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hterminal :
      RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
        gamma gamma' A B c H f g) :
    ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) ∧
        s(rlc_dualReflect f, rlc_dualReflect g) ∉
          rlc_reflectedPathEdges gamma'.1) ∨
      ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
        target.1.map Subtype.val =
            s(rlc_dualReflect f, rlc_dualReflect g) ∧
          rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧
          (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry
            gamma gamma' f g) ∧
          sharedPrimalEdge f g = s(p, q) ∧
          (hypercubicLattice 2).Adj p q ∧
          p ∈ rlc_twoChannelFullReachSet gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
          q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
          ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
                gamma gamma' p ∧
              RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue
                gamma gamma'
                  (rlc_twoChannelFullPhysicalCutInteriorConfig
                    gamma gamma' A) p q) ∨
            p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧
          (q ∈ H.support ∨ p ∈ c.support ∨ q ∈ c.support) := by
  change ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) ∧
      s(rlc_dualReflect f, rlc_dualReflect g) ∉
        rlc_reflectedPathEdges gamma'.1) ∨
    ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
      target.1.map Subtype.val =
          s(rlc_dualReflect f, rlc_dualReflect g) ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧
        (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry
          gamma gamma' f g) ∧
        ∃ p₀ q₀ : Site 2,
          sharedPrimalEdge f g = s(p₀, q₀) ∧
            (hypercubicLattice 2).Adj p₀ q₀ ∧
            p₀ ∈ rlc_twoChannelFullReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
            q₀ ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
            ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
                  gamma gamma' p₀ ∧
                RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue
                  gamma gamma'
                    (rlc_twoChannelFullPhysicalCutInteriorConfig
                      gamma gamma' A) p₀ q₀) ∨
              p₀ 0 = -2 * n ∨ p₀ 1 = -n ∨ p₀ 1 = n) ∧
            (p₀ = a ∨ p₀ = b ∨ q₀ ∈ H.support ∨
              p₀ ∈ c.support ∨ q₀ ∈ c.support) at hterminal
  rcases hterminal with htarget |
      ⟨target, htarget, hcross, hsourceBad, p₀, q₀, hp₀q₀,
        hp₀q₀Adj, hp₀Reach, hq₀Out, hp₀Place, hcontact⟩
  · exact Or.inl htarget
  have hpqEq : s(p₀, q₀) = s(p, q) := hp₀q₀.symm.trans hpq
  rw [Sym2.eq_iff] at hpqEq
  have horient : p₀ = p ∧ q₀ = q := by
    rcases hpqEq with hsame | hswap
    · exact hsame
    · have hqReach : q ∈ rlc_twoChannelFullReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
        simpa [hswap.1] using hp₀Reach
      exact False.elim (hqOut
        (rlc_twoChannelFullReachSet_subset_filled gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
            hqReach))
  have hcontact₀ : q₀ ∈ H.support ∨ p₀ ∈ c.support ∨ q₀ ∈ c.support := by
    rcases hcontact with hpa | hpb | hqH | hpC | hqC
    · exact Or.inr (Or.inl (hpa.symm ▸ ha))
    · exact Or.inr (Or.inl (hpb.symm ▸ hb))
    · exact Or.inl hqH
    · exact Or.inr (Or.inl hpC)
    · exact Or.inr (Or.inr hqC)
  have hcontact' : q ∈ H.support ∨ p ∈ c.support ∨ q ∈ c.support := by
    simpa [horient.1, horient.2] using hcontact₀
  exact Or.inr ⟨target, htarget, hcross, hsourceBad, hpq,
    by simpa [horient.1, horient.2] using hp₀q₀Adj,
    hpReach, hqOut, by simpa [horient.1, horient.2] using hp₀Place,
    hcontact'⟩


theorem
    rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_chord
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A B : Set (RlcConnectorVertex n))
    {u a b f g p q : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (H : (hypercubicLattice 2).Walk a b)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (hpq : sharedPrimalEdge f g = s(p, q))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (havoid : p ∉ c.support ∧ q ∉ c.support)
    (hterminal :
      RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
        gamma gamma' A B c H f g) :
    ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) ∧
        s(rlc_dualReflect f, rlc_dualReflect g) ∉
          rlc_reflectedPathEdges gamma'.1) ∨
      ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
        target.1.map Subtype.val =
            s(rlc_dualReflect f, rlc_dualReflect g) ∧
          rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧
          (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry
            gamma gamma' f g) ∧
          sharedPrimalEdge f g = s(p, q) ∧
          (hypercubicLattice 2).Adj p q ∧
          p ∈ rlc_twoChannelFullReachSet gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
          q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
          (((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
                gamma gamma' p) ∧
              ∃ z : Site 2,
                (hypercubicLattice 2).Adj p z ∧
                  rlc_twoChannelFullAmbientConfig gamma gamma'
                    (rlc_twoChannelFullPhysicalCutInteriorConfig
                      gamma gamma' A) s(p, z) = true ∧
                  ((∃ source :
                      (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
                      source.1.map Subtype.val = s(p, z)) ∨
                    (s(p, z) ∉
                        rlc_connectorFourTraceEdges gamma gamma' ∧
                      z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1 ∧
                      ∀ y : Site 2,
                        (hypercubicLattice 2).Adj p y →
                          y ≠ z → y ≠ q →
                          ∃ source :
                            (rlc_connectorTwoChannelGraph
                              gamma gamma').edgeSet,
                            source.1.map Subtype.val = s(p, y)))) ∨
            p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧
          q ∈ H.support := by
  rcases
      rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_identifySource
        A B c H ha hb hpq hpReach hqOut hterminal with
    htarget | ⟨target, htarget, hcross, hsourceBad, hpq, hpqAdj,
      hpReach, hqOut, hpPlace, hcontact⟩
  · exact Or.inl htarget
  · have hqH : q ∈ H.support := by
      rcases hcontact with hqH | hpC | hqC
      · exact hqH
      · exact False.elim (havoid.1 hpC)
      · exact False.elim (havoid.2 hqC)
    refine Or.inr ⟨target, htarget, hcross, hsourceBad, hpq,
      hpqAdj, hpReach, hqOut, ?_, hqH⟩
    simpa only [
      RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue]
      using hpPlace


theorem
    rlc_twoChannelFullPhysical_reflectedLeftTerminal_nonChord_forces_cycleEndpoint
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A B : Set (RlcConnectorVertex n))
    {u a b f g p q : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (H : (hypercubicLattice 2).Walk a b)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (hpq : sharedPrimalEdge f g = s(p, q))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hterminal :
      RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
        gamma gamma' A B c H f g)
    (hnoTargetBad : ¬((
        ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) ∧
      s(rlc_dualReflect f, rlc_dualReflect g) ∉
        rlc_reflectedPathEdges gamma'.1))
    (hqH : q ∉ H.support) :
    p ∈ c.support ∨ q ∈ c.support := by
  rcases
      rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_identifySource
        A B c H ha hb hpq hpReach hqOut hterminal with
    htarget | ⟨_target, _htarget, _hcross, _hsourceBad, _hpq,
      _hpqAdj, _hpReach, _hqOut, _hpPlace, hcontact⟩
  · exact False.elim (hnoTargetBad htarget)
  · rcases hcontact with hqH' | hpC | hqC
    · exact False.elim (hqH hqH')
    · exact Or.inl hpC
    · exact Or.inr hqC


theorem
    rlc_twoChannelFullPhysical_reflectedLeftTerminal_reachableSource_incidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {f g p q : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g)
    (hfExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
      gamma gamma' (rlc_dualReflect f))
    (hpq : sharedPrimalEdge f g = s(p, q))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega) :
    phb_doubleDualShift p = g ∨ p = f ∨ p = g := by
  have hpNe : phb_doubleDualShift p ≠ f :=
    rlc_shiftedReach_ne_exclusiveReflectedLeftFace
      hno hpReach hfExclusive
  have hgeom :=
    rlc_sharedPrimalEdge_doubleDualShift_endpoint_geometry hfg hpq
  rcases hgeom with ⟨hdir, hord⟩ | ⟨hdir, hord⟩ |
      ⟨hdir, hord⟩ | ⟨hdir, hord⟩
  · rcases hord with ⟨hpShift, _hqShift⟩ | ⟨hpShift, _hqShift⟩
    · exact False.elim (hpNe hpShift)
    · right; right
      have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp [phb_doubleDualShift] at hp0 hp1 hd0 hd1
      funext i
      fin_cases i
      · change p 0 = g 0
        omega
      · change p 1 = g 1
        omega
  · rcases hord with ⟨hpShift, _hqShift⟩ | ⟨hpShift, _hqShift⟩
    · exact Or.inl hpShift
    · right; left
      have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      simp [phb_doubleDualShift] at hp0 hp1
      funext i
      fin_cases i
      · change p 0 = f 0
        omega
      · change p 1 = f 1
        omega
  · rcases hord with ⟨hpShift, _hqShift⟩ | ⟨hpShift, _hqShift⟩
    · exact False.elim (hpNe hpShift)
    · right; right
      have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp [phb_doubleDualShift] at hp0 hp1 hd0 hd1
      funext i
      fin_cases i
      · change p 0 = g 0
        omega
      · change p 1 = g 1
        omega
  · rcases hord with ⟨hpShift, _hqShift⟩ | ⟨hpShift, _hqShift⟩
    · exact Or.inl hpShift
    · right; left
      have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      simp [phb_doubleDualShift] at hp0 hp1
      funext i
      fin_cases i
      · change p 0 = f 0
        omega
      · change p 1 = f 1
        omega


theorem
    rlc_twoChannelFullPhysical_reflectedLeftTerminal_literalSourceEdge_geometry
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {f g p q : Site 2}
    (hfg : (hypercubicLattice 2).Adj f g)
    (hfExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
      gamma gamma' (rlc_dualReflect f))
    (hpq : sharedPrimalEdge f g = s(p, q))
    (hpFace : p = f ∨ p = g) :
    ∃ w ∈ rlc_pathVertices gamma'.1,
      (p = f ∧ phb_doubleDualShift q = g ∧
          (q = ![w 0 - 1, w 1] ∨ q = ![w 0, w 1 - 1])) ∨
        (p = g ∧ phb_doubleDualShift q = f ∧ q = w ∧
          (p = ![w 0 - 1, w 1] ∨ p = ![w 0, w 1 - 1])) := by
  obtain ⟨w, hwLeft, hfw⟩ := hfExclusive.2.1
  refine ⟨w, hwLeft, ?_⟩
  have hf0 := congrArg (fun z : Site 2 => z 0) hfw
  have hf1 := congrArg (fun z : Site 2 => z 1) hfw
  simp [rlc_dualReflect, rlc_dualReflectFun,
    rlc_flipX, rlc_flipXFun] at hf0 hf1
  have hgeom :=
    rlc_sharedPrimalEdge_doubleDualShift_endpoint_geometry hfg hpq
  rcases hgeom with ⟨hdir, hord⟩ | ⟨hdir, hord⟩ |
      ⟨hdir, hord⟩ | ⟨hdir, hord⟩
  · rcases hord with ⟨hpShift, _hqShift⟩ | ⟨hpShift, hqShift⟩
    · exfalso
      rcases hpFace with hpFace | hpFace
      · have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
        simp [hpFace, phb_doubleDualShift] at hp0
      · have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
        have hd1 := congrArg (fun z : Site 2 => z 1) hdir
        simp [hpFace, phb_doubleDualShift] at hp1 hd1
        omega
    · right
      have hpg : p = g := by
        have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
        have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
        have hd0 := congrArg (fun z : Site 2 => z 0) hdir
        have hd1 := congrArg (fun z : Site 2 => z 1) hdir
        simp [phb_doubleDualShift] at hp0 hp1 hd0 hd1
        funext i
        fin_cases i <;> simp <;> omega
      have hqw : q = w := by
        have hq0 := congrArg (fun z : Site 2 => z 0) hqShift
        have hq1 := congrArg (fun z : Site 2 => z 1) hqShift
        simp [phb_doubleDualShift] at hq0 hq1
        funext i
        fin_cases i <;> simp <;> omega
      refine ⟨hpg, hqShift, hqw, Or.inr ?_⟩
      rw [hpg]
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp at hd0 hd1
      funext i
      fin_cases i <;> simp <;> omega
  · rcases hord with ⟨hpShift, _hqShift⟩ | ⟨hpShift, hqShift⟩
    · exfalso
      rcases hpFace with hpFace | hpFace
      · have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
        have hd1 := congrArg (fun z : Site 2 => z 1) hdir
        simp [hpFace, phb_doubleDualShift] at hp1 hd1
        omega
      · have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
        simp [hpFace, phb_doubleDualShift] at hp0
    · left
      have hpf : p = f := by
        have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
        have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
        simp [phb_doubleDualShift] at hp0 hp1
        funext i
        fin_cases i <;> simp <;> omega
      refine ⟨hpf, hqShift, Or.inl ?_⟩
      have hq0 := congrArg (fun z : Site 2 => z 0) hqShift
      have hq1 := congrArg (fun z : Site 2 => z 1) hqShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp [phb_doubleDualShift] at hq0 hq1 hd0 hd1
      funext i
      fin_cases i <;> simp <;> omega
  · rcases hord with ⟨hpShift, _hqShift⟩ | ⟨hpShift, hqShift⟩
    · exfalso
      rcases hpFace with hpFace | hpFace
      · have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
        simp [hpFace, phb_doubleDualShift] at hp0
      · have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
        have hd0 := congrArg (fun z : Site 2 => z 0) hdir
        simp [hpFace, phb_doubleDualShift] at hp0 hd0
        omega
    · right
      have hpg : p = g := by
        have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
        have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
        have hd0 := congrArg (fun z : Site 2 => z 0) hdir
        have hd1 := congrArg (fun z : Site 2 => z 1) hdir
        simp [phb_doubleDualShift] at hp0 hp1 hd0 hd1
        funext i
        fin_cases i <;> simp <;> omega
      have hqw : q = w := by
        have hq0 := congrArg (fun z : Site 2 => z 0) hqShift
        have hq1 := congrArg (fun z : Site 2 => z 1) hqShift
        simp [phb_doubleDualShift] at hq0 hq1
        funext i
        fin_cases i <;> simp <;> omega
      refine ⟨hpg, hqShift, hqw, Or.inl ?_⟩
      rw [hpg]
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp at hd0 hd1
      funext i
      fin_cases i <;> simp <;> omega
  · rcases hord with ⟨hpShift, _hqShift⟩ | ⟨hpShift, hqShift⟩
    · exfalso
      rcases hpFace with hpFace | hpFace
      · have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
        have hd0 := congrArg (fun z : Site 2 => z 0) hdir
        simp [hpFace, phb_doubleDualShift] at hp0 hd0
        omega
      · have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
        simp [hpFace, phb_doubleDualShift] at hp0
    · left
      have hpf : p = f := by
        have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
        have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
        simp [phb_doubleDualShift] at hp0 hp1
        funext i
        fin_cases i <;> simp <;> omega
      refine ⟨hpf, hqShift, Or.inr ?_⟩
      have hq0 := congrArg (fun z : Site 2 => z 0) hqShift
      have hq1 := congrArg (fun z : Site 2 => z 1) hqShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp [phb_doubleDualShift] at hq0 hq1 hd0 hd1
      funext i
      fin_cases i <;> simp <;> omega


theorem
    rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_identifySource_incidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A B : Set (RlcConnectorVertex n))
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {u a b f g p q : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (H : (hypercubicLattice 2).Walk a b)
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (hfg : (hypercubicLattice 2).Adj f g)
    (hfExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
      gamma gamma' (rlc_dualReflect f))
    (hpq : sharedPrimalEdge f g = s(p, q))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hterminal :
      RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
        gamma gamma' A B c H f g) :
    ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) ∧
        s(rlc_dualReflect f, rlc_dualReflect g) ∉
          rlc_reflectedPathEdges gamma'.1) ∨
      ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
        target.1.map Subtype.val =
            s(rlc_dualReflect f, rlc_dualReflect g) ∧
          rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧
          (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry
            gamma gamma' f g) ∧
          sharedPrimalEdge f g = s(p, q) ∧
          (hypercubicLattice 2).Adj p q ∧
          p ∈ rlc_twoChannelFullReachSet gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
          q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
          ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
                gamma gamma' p ∧
              RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue
                gamma gamma'
                  (rlc_twoChannelFullPhysicalCutInteriorConfig
                    gamma gamma' A) p q) ∨
            p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧
          (phb_doubleDualShift p = g ∨ p = f ∨ p = g) := by
  rcases
      rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_identifySource
        A B c H ha hb hpq hpReach hqOut hterminal with
    htarget | ⟨target, htarget, hcross, hsourceBad, hpq, hpqAdj,
      hpReach, hqOut, hpPlace, _hcontact⟩
  · exact Or.inl htarget
  · exact Or.inr ⟨target, htarget, hcross, hsourceBad, hpq,
      hpqAdj, hpReach, hqOut, hpPlace,
      rlc_twoChannelFullPhysical_reflectedLeftTerminal_reachableSource_incidence
        hno hfg hfExclusive hpq hpReach⟩


theorem
    rlc_twoChannelFullPhysical_rowOneLocalizedExactSourceSpliceEdgeResidue_terminalBranches
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A B : Set (RlcConnectorVertex n))
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {u a b ur vr ul vl p q p' q' f g : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (H : (hypercubicLattice 2).Walk a b)
    (w : (hypercubicLattice 2).Walk p p')
    (ha : a ∈ c.support) (hb : b ∈ c.support)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ul vl)
    (hurExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
      gamma gamma' (rlc_dualReflect ur))
    (hulExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
      gamma gamma' (rlc_dualReflect ul))
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hres : RlcTwoChannelFullPhysicalRowOneLocalizedExactSourceSpliceEdgeResidue
      gamma gamma' A B c H ur vr ul vl w f g) :
    let terminalBranch := fun t v r s =>
      ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' t v) ∧
          s(rlc_dualReflect t, rlc_dualReflect v) ∉
            rlc_reflectedPathEdges gamma'.1) ∨
        ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
          target.1.map Subtype.val =
              s(rlc_dualReflect t, rlc_dualReflect v) ∧
            rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧
            (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry
              gamma gamma' t v) ∧
            sharedPrimalEdge t v = s(r, s) ∧
            (hypercubicLattice 2).Adj r s ∧
            r ∈ rlc_twoChannelFullReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
            s ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
            ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
                  gamma gamma' r ∧
                RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue
                  gamma gamma'
                    (rlc_twoChannelFullPhysicalCutInteriorConfig
                    gamma gamma' A) r s) ∨
              r 0 = -2 * n ∨ r 1 = -n ∨ r 1 = n) ∧
            ∃ z ∈ rlc_pathVertices gamma'.1,
              (r = t ∧ phb_doubleDualShift s = v ∧
                  (s = ![z 0 - 1, z 1] ∨ s = ![z 0, z 1 - 1])) ∨
                (r = v ∧ phb_doubleDualShift s = t ∧ s = z ∧
                  (r = ![z 0 - 1, z 1] ∨ r = ![z 0, z 1 - 1]))
    (((s(f, g) = s(ur, vr) ∧ terminalBranch ur vr p q) ∨
        (s(f, g) = s(ul, vl) ∧ terminalBranch ul vl p' q')) ∨
      (s(f, g) = s(vr, phb_doubleDualShift p) ∨
        s(f, g) = s(ur, phb_doubleDualShift p)) ∨
      (∃ e₀ ∈ w.edges,
        Sym2.map phb_doubleDualShift e₀ = s(f, g) ∧
          rlc_twoChannelFullAmbientConfig gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A) e₀ = true ∧
          ((∃ source :
              (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
              source.1.map Subtype.val = e₀) ∨
            e₀ ∈ rlc_pathEdges gamma.1) ∧
          e₀ ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ∧
          rlc_twoChannelFullPhysicalEdgeCrossesCut
            (rlc_twoChannelFullPhysicalLiftVertexCut B)
              (Sym2.map rlc_flipX e₀) ∧
          ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
            target.1.map Subtype.val = Sym2.map rlc_flipX e₀ ∧
              ((∃ z ∈ e₀,
                  RlcTwoChannelFullPhysicalRightArcBadLocation
                    gamma gamma' z) ∨
                ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
                  physical.1 = target ∧
                    ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
                      (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧
                    ∀ z ∈
                        (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
                          Subtype.val,
                      z ∈ rlc_twoChannelFullReachSet gamma gamma'
                        (rlc_twoChannelFullPhysicalCutInteriorConfig
                          gamma gamma' A))) ∨
      (s(f, g) = s(vl, phb_doubleDualShift p') ∨
        s(f, g) = s(ul, phb_doubleDualShift p'))) := by
  dsimp only
  change (s(f, g) = s(ur, vr) ∧ _) ∨
    (s(f, g) = s(ul, vl) ∧ _) ∨ _ ∨ _ ∨ _ at hres
  rcases hres with hright | hleft | htetherR | hsource | htetherL
  · rcases
        rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_identifySource_incidence
          A B hno c H ha hb hurv.1 hurExclusive hpq hpReach hqOut
            hright.2 with
      htarget | ⟨target, htarget, hcross, hsourceBad, hpq, hpqAdj,
        hpReach, hqOut, hpPlace, hshift | hpFace⟩
    · exact Or.inl (Or.inl ⟨hright.1, Or.inl htarget⟩)
    · apply Or.inr
      apply Or.inl
      right
      rw [hshift]
      exact hright.1
    · exact Or.inl (Or.inl ⟨hright.1, Or.inr
        ⟨target, htarget, hcross, hsourceBad, hpq, hpqAdj,
          hpReach, hqOut, hpPlace,
          rlc_twoChannelFullPhysical_reflectedLeftTerminal_literalSourceEdge_geometry
            hurv.1 hurExclusive hpq hpFace⟩⟩)
  · rcases
        rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_identifySource_incidence
          A B hno c H ha hb hulv.1 hulExclusive hpq' hpReach' hqOut'
            hleft.2 with
      htarget | ⟨target, htarget, hcross, hsourceBad, hpq', hpqAdj',
        hpReach', hqOut', hpPlace, hshift | hpFace⟩
    · exact Or.inl (Or.inr ⟨hleft.1, Or.inl htarget⟩)
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      right
      rw [hshift]
      exact hleft.1
    · exact Or.inl (Or.inr ⟨hleft.1, Or.inr
        ⟨target, htarget, hcross, hsourceBad, hpq', hpqAdj',
          hpReach', hqOut', hpPlace,
          rlc_twoChannelFullPhysical_reflectedLeftTerminal_literalSourceEdge_geometry
            hulv.1 hulExclusive hpq' hpFace⟩⟩)
  · exact Or.inr (Or.inl htetherR)
  · exact Or.inr (Or.inr (Or.inl hsource))
  · exact Or.inr (Or.inr (Or.inr htetherL))


theorem
    rlc_twoChannelFullPhysical_rowOneLocalizedExactSourceSpliceEdgeResidue_tetherFree
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {u a b x y ur vr ul vl p q p' q' f g : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))))
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk y ul)
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hpShift : phb_doubleDualShift p = vr)
    (hpShift' : phb_doubleDualShift p' = vl)
    (w : (hypercubicLattice 2).Walk p p')
    (hfg : (hypercubicLattice 2).Adj f g)
    (hcross : rlc_twoChannelFullPhysicalEdgeCrossesCut
      (rlc_twoChannelFullPhysicalLiftVertexCut B)
        s(rlc_dualReflect f, rlc_dualReflect g))
    (hres : RlcTwoChannelFullPhysicalRowOneLocalizedExactSourceSpliceEdgeResidue
      gamma gamma' A B c H ur vr ul vl w f g) :
    let terminalBranch := fun t v r s =>
      ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' t v) ∧
          s(rlc_dualReflect t, rlc_dualReflect v) ∉
            rlc_reflectedPathEdges gamma'.1) ∨
        ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
          target.1.map Subtype.val =
              s(rlc_dualReflect t, rlc_dualReflect v) ∧
            rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧
            (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry
              gamma gamma' t v) ∧
            sharedPrimalEdge t v = s(r, s) ∧
            (hypercubicLattice 2).Adj r s ∧
            r ∈ rlc_twoChannelFullReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
            s ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
            ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
                  gamma gamma' r ∧
                RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue
                  gamma gamma'
                    (rlc_twoChannelFullPhysicalCutInteriorConfig
                      gamma gamma' A) r s) ∨
              r 0 = -2 * n ∨ r 1 = -n ∨ r 1 = n) ∧
            (phb_doubleDualShift r = v ∨ r = t ∨ r = v)
    let shiftedSourceBranch :=
      ∃ e₀ ∈ w.edges,
        Sym2.map phb_doubleDualShift e₀ = s(f, g) ∧
          rlc_twoChannelFullAmbientConfig gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A) e₀ = true ∧
          ((∃ source :
              (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
              source.1.map Subtype.val = e₀) ∨
            e₀ ∈ rlc_pathEdges gamma.1) ∧
          e₀ ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ∧
          rlc_twoChannelFullPhysicalEdgeCrossesCut
            (rlc_twoChannelFullPhysicalLiftVertexCut B)
              (Sym2.map rlc_flipX e₀) ∧
          ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
            target.1.map Subtype.val = Sym2.map rlc_flipX e₀ ∧
              (((∃ z ∈ e₀,
                  RlcTwoChannelFullPhysicalRightArcBadLocation
                    gamma gamma' z)) ∨
                ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
                  physical.1 = target ∧
                    ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
                      (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧
                    ∀ z ∈
                        (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
                          Subtype.val,
                      z ∈ rlc_twoChannelFullReachSet gamma gamma'
                        (rlc_twoChannelFullPhysicalCutInteriorConfig
                          gamma gamma' A))
    (s(f, g) = s(ur, vr) ∧ terminalBranch ur vr p q) ∨
      (s(f, g) = s(ul, vl) ∧ terminalBranch ul vl p' q') ∨
      shiftedSourceBranch := by
  dsimp only
  have hno : rlc_twoChannelEdgeConfigExtend gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma' :=
    rlc_twoChannelFullPhysicalCutInteriorConfig_failure
      gamma gamma' A hAright hAleft
  have hright :
      RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
          gamma gamma' A B c H ur vr →
        ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry
              gamma gamma' ur vr) ∧
            s(rlc_dualReflect ur, rlc_dualReflect vr) ∉
              rlc_reflectedPathEdges gamma'.1) ∨
          ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
            target.1.map Subtype.val =
                s(rlc_dualReflect ur, rlc_dualReflect vr) ∧
              rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧
              (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry
                gamma gamma' ur vr) ∧
              sharedPrimalEdge ur vr = s(p, q) ∧
              (hypercubicLattice 2).Adj p q ∧
              p ∈ rlc_twoChannelFullReachSet gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A) ∧
              q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A) ∧
              ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
                    gamma gamma' p ∧
                  RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue
                    gamma gamma'
                      (rlc_twoChannelFullPhysicalCutInteriorConfig
                        gamma gamma' A) p q) ∨
                p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧
              (phb_doubleDualShift p = vr ∨ p = ur ∨ p = vr) := by
    intro hterminal
    exact
      rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_identifySource_incidence
        A B hno c H ha hb hurv.1 hrow.2.1 hpq hpReach hqOut hterminal
  have hleft :
      RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
          gamma gamma' A B c H ul vl →
        ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry
              gamma gamma' ul vl) ∧
            s(rlc_dualReflect ul, rlc_dualReflect vl) ∉
              rlc_reflectedPathEdges gamma'.1) ∨
          ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
            target.1.map Subtype.val =
                s(rlc_dualReflect ul, rlc_dualReflect vl) ∧
              rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧
              (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry
                gamma gamma' ul vl) ∧
              sharedPrimalEdge ul vl = s(p', q') ∧
              (hypercubicLattice 2).Adj p' q' ∧
              p' ∈ rlc_twoChannelFullReachSet gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A) ∧
              q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A) ∧
              ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
                    gamma gamma' p' ∧
                  RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue
                    gamma gamma'
                      (rlc_twoChannelFullPhysicalCutInteriorConfig
                        gamma gamma' A) p' q') ∨
                p' 0 = -2 * n ∨ p' 1 = -n ∨ p' 1 = n) ∧
              (phb_doubleDualShift p' = vl ∨ p' = ul ∨ p' = vl) := by
    intro hterminal
    exact
      rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_identifySource_incidence
        A B hno c H ha hb hulv.1 hrow.2.2.2 hpq' hpReach' hqOut'
          hterminal
  change (s(f, g) = s(ur, vr) ∧ _) ∨
    (s(f, g) = s(ul, vl) ∧ _) ∨ _ ∨ _ ∨ _ at hres
  rcases hres with hterminalR | hterminalL | htetherR | hsource | htetherL
  · exact Or.inl ⟨hterminalR.1, hright hterminalR.2⟩
  · exact Or.inr (Or.inl ⟨hterminalL.1, hleft hterminalL.2⟩)
  · have hterminal :=
      rlc_twoChannelFullPhysical_rowOne_reachableShift_tether_terminal
        (f := f) (g := g) (ur := ur) (vr := vr) (ul := ul) (vl := vl)
          (p := p) (p' := p') hfg hpShift hpShift' (Or.inl htetherR)
    rcases
        rlc_twoChannelFullPhysical_noPair_rowOne_cleanSeparator_terminalBranch
          hn A B hAright hAleft hnoPair c hcycle ha hb H hclean qr ql hrow
            hurv hulv hcross hterminal with hterminalR | hterminalL
    · exact Or.inl ⟨hterminalR.1, hright hterminalR.2⟩
    · exact Or.inr (Or.inl ⟨hterminalL.1, hleft hterminalL.2⟩)
  · exact Or.inr (Or.inr hsource)
  · have hterminal :=
      rlc_twoChannelFullPhysical_rowOne_reachableShift_tether_terminal
        (f := f) (g := g) (ur := ur) (vr := vr) (ul := ul) (vl := vl)
          (p := p) (p' := p') hfg hpShift hpShift' (Or.inr htetherL)
    rcases
        rlc_twoChannelFullPhysical_noPair_rowOne_cleanSeparator_terminalBranch
          hn A B hAright hAleft hnoPair c hcycle ha hb H hclean qr ql hrow
            hurv hulv hcross hterminal with hterminalR | hterminalL
    · exact Or.inl ⟨hterminalR.1, hright hterminalR.2⟩
    · exact Or.inr (Or.inl ⟨hterminalL.1, hleft hterminalL.2⟩)


theorem
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_noSeparatorAvoidingExteriorReroute
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {u a b x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hxy : (hypercubicLattice 2).Adj x y)
    (hxReach : x ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hyReach : y ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val =
      s(rlc_flipX x, rlc_flipX y))
    (physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma')
    (hphysical : physical.1 = target)
    (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
      (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
    ∀ r ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
        Subtype.val,
      ¬∃ (t : Site 2) (P : (hypercubicLattice 2).Walk r t),
        t ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
          (∀ z ∈ P.support, z ∉ c.support) ∧
          ∀ z ∈ P.support, z ∉ H.support := by
  have hallReach :=
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_endpoints_reachable
      A hAright hAleft hxy hxReach hyReach target htarget physical
        hphysical hnotCross
  intro r hrSource
  rintro ⟨t, P, htOut, havoidCycle, havoidChord⟩
  have hrInside : r ∈ jec_leftRegion
      (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig
            gamma gamma' A)))) := by
    rw [← rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
          c hcycle]
    exact rlc_twoChannelFullReachSet_subset_filled gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
        (hallReach r hrSource)
  have htOutside : t ∉ jec_leftRegion
      (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig
            gamma gamma' A)))) := by
    rw [← rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
          c hcycle]
    exact htOut
  obtain ⟨z, hzP, hzH⟩ :=
    rlc_exteriorChord_inside_to_outside_path_meets_chord_of_avoids_cycle
      (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))
      c ha hb H P hrInside htOutside havoidCycle
  exact havoidChord z hzP hzH


theorem
    rlc_twoChannelFullPhysical_shiftedTarget_pairedSource_to_terminalPrefixReroute
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {p p' x y q : Site 2}
    (w : (hypercubicLattice 2).Walk p p')
    (hxy : s(x, y) ∈ w.edges)
    (hpq : (hypercubicLattice 2).Adj p q)
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val =
      s(rlc_flipX x, rlc_flipX y))
    (physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma')
    (hphysical : physical.1 = target) :
    ∃ (z : Site 2) (hzW : z ∈ w.support),
      z ∈ s(x, y) ∧
        ∃ r ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
            Subtype.val,
          (hypercubicLattice 2).Adj z r ∧
            ∃ P : (hypercubicLattice 2).Walk r q,
              ∀ v ∈ P.support,
                v = q ∨ v ∈ (w.takeUntil z hzW).support ∨
                  v ∈
                    (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
                      Subtype.val := by
  have hxyAdj : (hypercubicLattice 2).Adj x y :=
    w.adj_of_mem_edges hxy
  obtain ⟨z, x', r, hzx, hsourceGeom, _hzxAdj, hzrAdj,
      _hxr, _hnonopposite⟩ :=
    rlc_pimsEdgeEquiv_flipXEdge_incidentNonopposite hxyAdj
  have hsourceMap :
      (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val =
        rlc_pimsEdgeEquiv s(rlc_flipX x, rlc_flipX y) := by
    calc
      (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val =
          rlc_pimsEdgeEquiv (physical.1.1.map Subtype.val) :=
        rlc_twoChannelFullPhysicalSourceEdge_map physical
      _ = rlc_pimsEdgeEquiv (target.1.map Subtype.val) := by
        rw [hphysical]
      _ = _ := by rw [htarget]
  have hsourceZX :
      (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val =
        s(z, r) := hsourceMap.trans hsourceGeom
  have hzxEdge : s(z, x') ∈ w.edges := by
    rw [← hzx]
    exact hxy
  have hzW : z ∈ w.support :=
    w.fst_mem_support_of_mem_edges hzxEdge
  let W : (hypercubicLattice 2).Walk z p :=
    (w.takeUntil z hzW).reverse
  obtain ⟨P, hP⟩ := rlc_walk_between_tethers W
    (Or.inr hzrAdj) (Or.inr hpq)
  refine ⟨z, hzW, ?_, r, ?_, hzrAdj, P, ?_⟩
  · rw [hzx]
    exact Sym2.mem_mk_left _ _
  · rw [hsourceZX]
    exact Sym2.mem_mk_right _ _
  · intro v hvP
    rcases hP v hvP with rfl | rfl | hvW
    · exact Or.inr (Or.inr (by
        rw [hsourceZX]
        exact Sym2.mem_mk_right _ _))
    · exact Or.inl rfl
    · right
      left
      dsimp only [W] at hvW
      rw [SimpleGraph.Walk.support_reverse] at hvW
      simpa using hvW


theorem
    rlc_twoChannelFullPhysical_shiftedTarget_pairedSource_to_terminalReroute
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {p p' x y q : Site 2}
    (w : (hypercubicLattice 2).Walk p p')
    (hxy : s(x, y) ∈ w.edges)
    (hpq : (hypercubicLattice 2).Adj p q)
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val =
      s(rlc_flipX x, rlc_flipX y))
    (physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma')
    (hphysical : physical.1 = target) :
    ∃ r ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
        Subtype.val,
      ∃ P : (hypercubicLattice 2).Walk r q,
        ∀ v ∈ P.support,
          v = q ∨ v ∈ w.support ∨
            v ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
              Subtype.val := by
  obtain ⟨z, hzW, _hzEdge, r, hrSource, _hzr, P, hP⟩ :=
    rlc_twoChannelFullPhysical_shiftedTarget_pairedSource_to_terminalPrefixReroute
      w hxy hpq target htarget physical hphysical
  refine ⟨r, hrSource, P, ?_⟩
  · intro v hvP
    rcases hP v hvP with rfl | hvPrefix | hvSource
    · exact Or.inl rfl
    · exact Or.inr (Or.inl
        (w.support_takeUntil_subset_support hzW hvPrefix))
    · exact Or.inr (Or.inr hvSource)


theorem
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_terminalReroute_cleanContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {u a b p p' x y q : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))))
    (w : (hypercubicLattice 2).Walk p p')
    (hwReach : ∀ v ∈ w.support,
      v ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hxy : s(x, y) ∈ w.edges)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val =
      s(rlc_flipX x, rlc_flipX y))
    (physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma')
    (hphysical : physical.1 = target)
    (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
      (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
    (q ∈ c.support ∨ q ∈ H.support) ∨
      ∃ v : Site 2,
        (v ∈ w.support ∨
          v ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
            Subtype.val) ∧
        v ∈ c.support := by
  have hxyAdj : (hypercubicLattice 2).Adj x y :=
    w.adj_of_mem_edges hxy
  have hxReach := hwReach x (w.fst_mem_support_of_mem_edges hxy)
  have hyReach := hwReach y (w.snd_mem_support_of_mem_edges hxy)
  have hsourceReach :=
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_endpoints_reachable
      A hAright hAleft hxyAdj hxReach hyReach target htarget physical
        hphysical hnotCross
  obtain ⟨r, hrSource, P, hP⟩ :=
    rlc_twoChannelFullPhysical_shiftedTarget_pairedSource_to_terminalReroute
      w hxy hpq target htarget physical hphysical
  have hcontact : ∃ v ∈ P.support,
      v ∈ c.support ∨ v ∈ H.support := by
    by_contra hnone
    push_neg at hnone
    exact
      (rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_noSeparatorAvoidingExteriorReroute
        A hAright hAleft c hcycle ha hb H hxyAdj hxReach hyReach
          target htarget physical hphysical hnotCross r hrSource)
        ⟨q, P, hqOut,
          (fun v hvP hvC ↦ (hnone v hvP).1 hvC),
          fun v hvP hvH ↦ (hnone v hvP).2 hvH⟩
  obtain ⟨v, hvP, hvC | hvH⟩ := hcontact
  · rcases hP v hvP with rfl | hvW | hvSource
    · exact Or.inl (Or.inl hvC)
    · exact Or.inr ⟨v, Or.inl hvW, hvC⟩
    · exact Or.inr ⟨v, Or.inr hvSource, hvC⟩
  · rcases hP v hvP with rfl | hvW | hvSource
    · exact Or.inl (Or.inr hvH)
    · rcases hclean v hvH with hva | hvb | hvOff
      · exact Or.inr ⟨v, Or.inl hvW, by simpa [hva] using ha⟩
      · exact Or.inr ⟨v, Or.inl hvW, by simpa [hvb] using hb⟩
      · have hvInside : v ∈ jec_leftRegion
            (c.mapLe (faceBoundaryGraph_le
              (rlc_twoChannelFullFilledReachSet gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A)))) := by
          rw [← rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
            gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
                c hcycle]
          exact rlc_twoChannelFullReachSet_subset_filled gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
              (hwReach v hvW)
        exact False.elim (hvOff.2 hvInside)
    · rcases hclean v hvH with hva | hvb | hvOff
      · exact Or.inr ⟨v, Or.inr hvSource, by simpa [hva] using ha⟩
      · exact Or.inr ⟨v, Or.inr hvSource, by simpa [hvb] using hb⟩
      · have hvInside : v ∈ jec_leftRegion
            (c.mapLe (faceBoundaryGraph_le
              (rlc_twoChannelFullFilledReachSet gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A)))) := by
          rw [← rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
            gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
                c hcycle]
          exact rlc_twoChannelFullReachSet_subset_filled gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
              (hsourceReach v hvSource)
        exact False.elim (hvOff.2 hvInside)


theorem
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_terminalPrefixReroute_cleanContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {u a b p p' x y q : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))))
    (w : (hypercubicLattice 2).Walk p p')
    (hwReach : ∀ v ∈ w.support,
      v ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hxy : s(x, y) ∈ w.edges)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val =
      s(rlc_flipX x, rlc_flipX y))
    (physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma')
    (hphysical : physical.1 = target)
    (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
      (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
    (q ∈ c.support ∨ q ∈ H.support) ∨
      ∃ (z : Site 2) (hzW : z ∈ w.support),
        z ∈ s(x, y) ∧
          ((∃ v ∈ (w.takeUntil z hzW).support, v ∈ c.support) ∨
            ∃ v ∈
                (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
                  Subtype.val,
              v ∈ c.support) := by
  have hxyAdj : (hypercubicLattice 2).Adj x y :=
    w.adj_of_mem_edges hxy
  have hxReach := hwReach x (w.fst_mem_support_of_mem_edges hxy)
  have hyReach := hwReach y (w.snd_mem_support_of_mem_edges hxy)
  have hsourceReach :=
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_endpoints_reachable
      A hAright hAleft hxyAdj hxReach hyReach target htarget physical
        hphysical hnotCross
  obtain ⟨z, hzW, hzEdge, r, hrSource, _hzr, P, hP⟩ :=
    rlc_twoChannelFullPhysical_shiftedTarget_pairedSource_to_terminalPrefixReroute
      w hxy hpq target htarget physical hphysical
  have hcontact : ∃ v ∈ P.support,
      v ∈ c.support ∨ v ∈ H.support := by
    by_contra hnone
    push_neg at hnone
    exact
      (rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_noSeparatorAvoidingExteriorReroute
        A hAright hAleft c hcycle ha hb H hxyAdj hxReach hyReach
          target htarget physical hphysical hnotCross r hrSource)
        ⟨q, P, hqOut,
          (fun v hvP hvC ↦ (hnone v hvP).1 hvC),
          fun v hvP hvH ↦ (hnone v hvP).2 hvH⟩
  obtain ⟨v, hvP, hvC | hvH⟩ := hcontact
  · rcases hP v hvP with rfl | hvPrefix | hvSource
    · exact Or.inl (Or.inl hvC)
    · exact Or.inr ⟨z, hzW, hzEdge,
        Or.inl ⟨v, hvPrefix, hvC⟩⟩
    · exact Or.inr ⟨z, hzW, hzEdge,
        Or.inr ⟨v, hvSource, hvC⟩⟩
  · rcases hP v hvP with rfl | hvPrefix | hvSource
    · exact Or.inl (Or.inr hvH)
    · rcases hclean v hvH with hva | hvb | hvOff
      · exact Or.inr ⟨z, hzW, hzEdge, Or.inl
          ⟨v, hvPrefix, by simpa [hva] using ha⟩⟩
      · exact Or.inr ⟨z, hzW, hzEdge, Or.inl
          ⟨v, hvPrefix, by simpa [hvb] using hb⟩⟩
      · have hvInside : v ∈ jec_leftRegion
            (c.mapLe (faceBoundaryGraph_le
              (rlc_twoChannelFullFilledReachSet gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A)))) := by
          rw [← rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
            gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
                c hcycle]
          exact rlc_twoChannelFullReachSet_subset_filled gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
              (hwReach v
                (w.support_takeUntil_subset_support hzW hvPrefix))
        exact False.elim (hvOff.2 hvInside)
    · rcases hclean v hvH with hva | hvb | hvOff
      · exact Or.inr ⟨z, hzW, hzEdge, Or.inr
          ⟨v, hvSource, by simpa [hva] using ha⟩⟩
      · exact Or.inr ⟨z, hzW, hzEdge, Or.inr
          ⟨v, hvSource, by simpa [hvb] using hb⟩⟩
      · have hvInside : v ∈ jec_leftRegion
            (c.mapLe (faceBoundaryGraph_le
              (rlc_twoChannelFullFilledReachSet gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A)))) := by
          rw [← rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
            gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
                c hcycle]
          exact rlc_twoChannelFullReachSet_subset_filled gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
              (hsourceReach v hvSource)
        exact False.elim (hvOff.2 hvInside)


theorem
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_twoTerminalPrefixReroute_cleanContacts
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {u a b p p' x y q q' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))))
    (w : (hypercubicLattice 2).Walk p p')
    (hwReach : ∀ v ∈ w.support,
      v ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hxy : s(x, y) ∈ w.edges)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpq' : (hypercubicLattice 2).Adj p' q')
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val =
      s(rlc_flipX x, rlc_flipX y))
    (physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma')
    (hphysical : physical.1 = target)
    (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
      (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
    ((q ∈ c.support ∨ q ∈ H.support) ∨
      ∃ (z : Site 2) (hzW : z ∈ w.support),
        z ∈ s(x, y) ∧
          ((∃ v ∈ (w.takeUntil z hzW).support, v ∈ c.support) ∨
            ∃ v ∈
                (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
                  Subtype.val,
              v ∈ c.support)) ∧
      ((q' ∈ c.support ∨ q' ∈ H.support) ∨
        ∃ (z : Site 2) (hzW : z ∈ w.reverse.support),
          z ∈ s(x, y) ∧
            ((∃ v ∈ (w.reverse.takeUntil z hzW).support,
                v ∈ c.support) ∨
              ∃ v ∈
                  (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
                    Subtype.val,
                v ∈ c.support)) := by
  have hright :=
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_terminalPrefixReroute_cleanContact
      A hAright hAleft c hcycle ha hb H hclean w hwReach hxy hpq hqOut
        target htarget physical hphysical hnotCross
  have hwReachRev : ∀ v ∈ w.reverse.support,
      v ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
    intro v hv
    exact hwReach v (by
      simpa [SimpleGraph.Walk.support_reverse] using hv)
  have hxyRev : s(x, y) ∈ w.reverse.edges := by
    simpa [SimpleGraph.Walk.edges_reverse] using hxy
  have hleft :=
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_terminalPrefixReroute_cleanContact
      A hAright hAleft c hcycle ha hb H hclean w.reverse hwReachRev
        hxyRev hpq' hqOut' target htarget physical hphysical hnotCross
  exact ⟨hright, hleft⟩


theorem
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_twoTerminalReroute_contactInterval
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {u a b p p' x y q q' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))))
    (w : (hypercubicLattice 2).Walk p p')
    (hwReach : ∀ v ∈ w.support,
      v ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hxy : s(x, y) ∈ w.edges)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpq' : (hypercubicLattice 2).Adj p' q')
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val =
      s(rlc_flipX x, rlc_flipX y))
    (physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma')
    (hphysical : physical.1 = target)
    (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
      (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
    (q ∈ c.support ∨ q ∈ H.support) ∨
      (q' ∈ c.support ∨ q' ∈ H.support) ∨
      (∃ v ∈
          (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val,
        v ∈ c.support) ∨
      (∃ z ∈ s(x, y), z ∈ c.support) ∨
      ∃ k i j : Nat,
        k < w.length ∧
          s(w.getVert k, w.getVert (k + 1)) = s(x, y) ∧
          i < k ∧ k + 1 < j ∧ j ≤ w.length ∧
          w.getVert i ∈ c.support ∧ w.getVert j ∈ c.support ∧
          ∀ l : Nat, i < l → l < j → w.getVert l ∉ c.support := by
  have hcontacts :=
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_twoTerminalPrefixReroute_cleanContacts
      A hAright hAleft c hcycle ha hb H hclean w hwReach hxy hpq hpq'
        hqOut hqOut' target htarget physical hphysical hnotCross
  rcases hcontacts.1 with hq | ⟨zR, hzRW, hzR, hprefix | hsource⟩
  · exact Or.inl hq
  · rcases hcontacts.2 with hq' | ⟨zL, hzLWRev, hzL, hsuffix | hsource'⟩
    · exact Or.inr (Or.inl hq')
    · by_cases hedgeOff : ∀ z ∈ s(x, y), z ∉ c.support
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (rlc_walk_edge_prefix_reversePrefix_contact_interval
            w c hxy hzR hzL hedgeOff hzRW hzLWRev hprefix hsuffix))))
      · push Not at hedgeOff
        exact Or.inr (Or.inr (Or.inr (Or.inl hedgeOff)))
    · exact Or.inr (Or.inr (Or.inl hsource'))
  · exact Or.inr (Or.inr (Or.inl hsource))


theorem
    rlc_twoChannelFullPhysical_noPair_crossingTarget_pairedSource_contactInterval
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
        rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {u a b p p' x y q q' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))))
    (w : (hypercubicLattice 2).Walk p p')
    (hwReach : ∀ v ∈ w.support,
      v ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hxy : s(x, y) ∈ w.edges)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpq' : (hypercubicLattice 2).Adj p' q')
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val =
      s(rlc_flipX x, rlc_flipX y))
    (physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma')
    (hphysical : physical.1 = target)
    (hcrossB : rlc_twoChannelFullPhysicalEdgeCrossesCut
      (rlc_twoChannelFullPhysicalLiftVertexCut B)
        (target.1.map Subtype.val)) :
    (¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
        (rlc_twoChannelFullPhysicalSourceEdge physical).1) ∧
      ((q ∈ c.support ∨ q ∈ H.support) ∨
        (q' ∈ c.support ∨ q' ∈ H.support) ∨
        (∃ v ∈
            (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val,
          v ∈ c.support) ∨
        (∃ z ∈ s(x, y), z ∈ c.support) ∨
        ∃ k i j : Nat,
          k < w.length ∧
            s(w.getVert k, w.getVert (k + 1)) = s(x, y) ∧
            i < k ∧ k + 1 < j ∧ j ≤ w.length ∧
            w.getVert i ∈ c.support ∧ w.getVert j ∈ c.support ∧
            ∀ l : Nat, i < l → l < j →
              w.getVert l ∉ c.support) := by
  have hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
      (rlc_twoChannelFullPhysicalSourceEdge physical).1 := by
    intro hcrossA
    apply hnoPair
    refine ⟨physical, hcrossA, ?_⟩
    exact (rlc_twoChannelFullPhysicalEdgeCrossesCut_liftVertexCut_iff
      B physical.1).2 (by simpa [hphysical] using hcrossB)
  exact ⟨hnotCross,
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_twoTerminalReroute_contactInterval
      A hAright hAleft c hcycle ha hb H hclean w hwReach hxy hpq hpq'
        hqOut hqOut' target htarget physical hphysical hnotCross⟩


theorem
    rlc_twoChannelFullPhysical_noPair_crossingTarget_pairedSource_reachableContactInterval
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
        rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {u a b p p' x y q q' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))))
    (w : (hypercubicLattice 2).Walk p p')
    (hwReach : ∀ v ∈ w.support,
      v ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hxy : s(x, y) ∈ w.edges)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpq' : (hypercubicLattice 2).Adj p' q')
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val =
      s(rlc_flipX x, rlc_flipX y))
    (physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma')
    (hphysical : physical.1 = target)
    (hcrossB : rlc_twoChannelFullPhysicalEdgeCrossesCut
      (rlc_twoChannelFullPhysicalLiftVertexCut B)
        (target.1.map Subtype.val)) :
    let Reach := rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
    (¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
        (rlc_twoChannelFullPhysicalSourceEdge physical).1) ∧
      ((q ∈ c.support ∨ q ∈ H.support) ∨
        (q' ∈ c.support ∨ q' ∈ H.support) ∨
        (∃ v ∈
            (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val,
          v ∈ c.support ∧ v ∈ Reach) ∨
        (∃ z ∈ s(x, y), z ∈ c.support ∧ z ∈ Reach) ∨
        ∃ k i j : Nat,
          k < w.length ∧
            s(w.getVert k, w.getVert (k + 1)) = s(x, y) ∧
            i < k ∧ k + 1 < j ∧ j ≤ w.length ∧
            w.getVert i ∈ c.support ∧ w.getVert j ∈ c.support ∧
            (∀ l : Nat, i < l → l < j →
              w.getVert l ∉ c.support) ∧
            ∀ l : Nat, i ≤ l → l ≤ j → w.getVert l ∈ Reach) := by
  dsimp only
  have hclassified :=
    rlc_twoChannelFullPhysical_noPair_crossingTarget_pairedSource_contactInterval
      A B hAright hAleft hnoPair c hcycle ha hb H hclean w hwReach hxy
        hpq hpq' hqOut hqOut' target htarget physical hphysical hcrossB
  have hxyAdj : (hypercubicLattice 2).Adj x y :=
    w.adj_of_mem_edges hxy
  have hxReach := hwReach x (w.fst_mem_support_of_mem_edges hxy)
  have hyReach := hwReach y (w.snd_mem_support_of_mem_edges hxy)
  have hsourceReach :=
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_endpoints_reachable
      A hAright hAleft hxyAdj hxReach hyReach target htarget physical
        hphysical hclassified.1
  refine ⟨hclassified.1, ?_⟩
  rcases hclassified.2 with hq | hq' | hsource | hselected | hinterval
  · exact Or.inl hq
  · exact Or.inr (Or.inl hq')
  · obtain ⟨v, hvSource, hvC⟩ := hsource
    exact Or.inr (Or.inr (Or.inl
      ⟨v, hvSource, hvC, hsourceReach v hvSource⟩))
  · obtain ⟨z, hzEdge, hzC⟩ := hselected
    have hzEdge' := hzEdge
    have hzReach : z ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
      rw [Sym2.mem_iff] at hzEdge
      rcases hzEdge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxReach
      · exact hyReach
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨z, hzEdge', hzC, hzReach⟩)))
  · obtain ⟨k, i, j, hk, hedge, hik, hkj, hj, hiC, hjC, hoff⟩ :=
      hinterval
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨k, i, j, hk, hedge, hik, hkj, hj, hiC, hjC, hoff,
        fun l _hil _hlj ↦ hwReach (w.getVert l) (w.getVert_mem_support l)⟩)))


theorem
    rlc_twoChannelFullPhysical_shiftedSourceEdge_status_twoCut_reachableContactInterval
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
        rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {u a b p p' q q' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))))
    (w : (hypercubicLattice 2).Walk p p')
    (hwReach : ∀ v ∈ w.support,
      v ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    {e : Sym2 (Site 2)} (he : e ∈ w.edges)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpq' : (hypercubicLattice 2).Adj p' q')
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val = Sym2.map rlc_flipX e)
    (hcrossB : rlc_twoChannelFullPhysicalEdgeCrossesCut
      (rlc_twoChannelFullPhysicalLiftVertexCut B)
        (target.1.map Subtype.val))
    (hstatus :
      (∃ z ∈ e,
          RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' z) ∨
        ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
          physical.1 = target ∧
            ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
              (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧
            ∀ z ∈
                (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
                  Subtype.val,
              z ∈ rlc_twoChannelFullReachSet gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A)) :
    let Reach := rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
    let Classified := fun physical :
        RlcTwoChannelFullPhysicalTargetEdge gamma gamma' =>
      (q ∈ c.support ∨ q ∈ H.support) ∨
        (q' ∈ c.support ∨ q' ∈ H.support) ∨
        (∃ v ∈
            (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val,
          v ∈ c.support ∧ v ∈ Reach) ∨
        (∃ z ∈ e, z ∈ c.support ∧ z ∈ Reach) ∨
        ∃ k i j : Nat,
          k < w.length ∧
            s(w.getVert k, w.getVert (k + 1)) = e ∧
            i < k ∧ k + 1 < j ∧ j ≤ w.length ∧
            w.getVert i ∈ c.support ∧ w.getVert j ∈ c.support ∧
            (∀ l : Nat, i < l → l < j →
              w.getVert l ∉ c.support) ∧
            ∀ l : Nat, i ≤ l → l ≤ j → w.getVert l ∈ Reach
    (∃ z ∈ e,
        RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' z) ∨
      ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
        physical.1 = target ∧
          ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
            (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧
          (∀ z ∈
              (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
                Subtype.val,
            z ∈ Reach) ∧
          Classified physical := by
  dsimp only
  rcases hstatus with hbad |
      ⟨physical, hphysical, _hnotCross, hsourceReach⟩
  · exact Or.inl hbad
  · right
    refine ⟨physical, hphysical, _hnotCross, hsourceReach, ?_⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
        have htarget' : target.1.map Subtype.val =
            s(rlc_flipX x, rlc_flipX y) := by
          simpa only [Sym2.map_mk] using htarget
        have hclassified :=
          rlc_twoChannelFullPhysical_noPair_crossingTarget_pairedSource_reachableContactInterval
            A B hAright hAleft hnoPair c hcycle ha hb H hclean w hwReach
              he hpq hpq' hqOut hqOut' target htarget' physical hphysical
                hcrossB
        exact hclassified.2


theorem
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_twoTerminalReroute_cleanContacts
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {u a b p p' x y q q' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))))
    (w : (hypercubicLattice 2).Walk p p')
    (hwReach : ∀ v ∈ w.support,
      v ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hxy : s(x, y) ∈ w.edges)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpq' : (hypercubicLattice 2).Adj p' q')
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val =
      s(rlc_flipX x, rlc_flipX y))
    (physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma')
    (hphysical : physical.1 = target)
    (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
      (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
    let Contact := fun t : Site 2 =>
      (t ∈ c.support ∨ t ∈ H.support) ∨
        ∃ v : Site 2,
          (v ∈ w.support ∨
            v ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
              Subtype.val) ∧
          v ∈ c.support
    Contact q ∧ Contact q' := by
  dsimp only
  have hright :=
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_terminalReroute_cleanContact
      A hAright hAleft c hcycle ha hb H hclean w hwReach hxy hpq hqOut
        target htarget physical hphysical hnotCross
  have hwReachRev : ∀ v ∈ w.reverse.support,
      v ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
    intro v hv
    exact hwReach v (by
      simpa [SimpleGraph.Walk.support_reverse] using hv)
  have hxyRev : s(x, y) ∈ w.reverse.edges := by
    simpa [SimpleGraph.Walk.edges_reverse] using hxy
  have hleft :=
    rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_terminalReroute_cleanContact
      A hAright hAleft c hcycle ha hb H hclean w.reverse hwReachRev
        hxyRev hpq' hqOut' target htarget physical hphysical hnotCross
  refine ⟨hright, ?_⟩
  rcases hleft with hq' | ⟨v, hvW | hvSource, hvContact⟩
  · exact Or.inl hq'
  · exact Or.inr ⟨v, Or.inl (by
      simpa [SimpleGraph.Walk.support_reverse] using hvW), hvContact⟩
  · exact Or.inr ⟨v, Or.inr hvSource, hvContact⟩


theorem
    rlc_twoChannelFullPhysical_shiftedSourceEdge_status_rightArcBad_or_twoTerminalContacts
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {u a b p p' q q' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))))
    (w : (hypercubicLattice 2).Walk p p')
    (hwReach : ∀ v ∈ w.support,
      v ∈ rlc_twoChannelFullReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    {e : Sym2 (Site 2)} (he : e ∈ w.edges)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpq' : (hypercubicLattice 2).Adj p' q')
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (htarget : target.1.map Subtype.val = Sym2.map rlc_flipX e)
    (hstatus :
      (∃ z ∈ e,
          RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' z) ∨
        ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
          physical.1 = target ∧
            ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
              (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧
            ∀ z ∈
                (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
                  Subtype.val,
              z ∈ rlc_twoChannelFullReachSet gamma gamma'
                (rlc_twoChannelFullPhysicalCutInteriorConfig
                  gamma gamma' A)) :
    let Contact := fun physical :
        RlcTwoChannelFullPhysicalTargetEdge gamma gamma' =>
      fun t : Site 2 =>
        (t ∈ c.support ∨ t ∈ H.support) ∨
          ∃ v : Site 2,
            (v ∈ w.support ∨
              v ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
                Subtype.val) ∧
            v ∈ c.support
    (∃ z ∈ e,
        RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' z) ∨
      ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
        physical.1 = target ∧
          ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
            (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧
          (∀ z ∈
              (rlc_twoChannelFullPhysicalSourceEdge physical).1.map
                Subtype.val,
            z ∈ rlc_twoChannelFullReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A)) ∧
          Contact physical q ∧ Contact physical q' := by
  dsimp only
  rcases hstatus with hbad | ⟨physical, hphysical, hnotCross, hsourceReach⟩
  · exact Or.inl hbad
  · right
    refine ⟨physical, hphysical, hnotCross, hsourceReach, ?_⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
        have htarget' : target.1.map Subtype.val =
            s(rlc_flipX x, rlc_flipX y) := by
          simpa only [Sym2.map_mk] using htarget
        exact
          rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_twoTerminalReroute_cleanContacts
            A hAright hAleft c hcycle ha hb H hclean w hwReach he hpq hpq'
              hqOut hqOut' target htarget' physical hphysical hnotCross


end
end StatMech.Universality
