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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part82
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelFullPhysical_rowOneExactSourceSpliceEdgeResidue_cleanSeparatorContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A B : Set (RlcConnectorVertex n))
    {u a b ur vr ul vl p p' f g : Site 2}
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
    (hres : RlcTwoChannelFullPhysicalRowOneExactSourceSpliceEdgeResidue
      gamma gamma' A B ur vr ul vl w f g) :
    RlcTwoChannelFullPhysicalRowOneCleanExactSourceSpliceEdgeResidue
      gamma gamma' A B c H ur vr ul vl w f g := by
  change (s(f, g) = s(ur, vr) ∧ _) ∨
    (s(f, g) = s(ul, vl) ∧ _) ∨ _ ∨ _ ∨ _ at hres
  change (s(f, g) = s(ur, vr) ∧ _) ∨
    (s(f, g) = s(ul, vl) ∧ _) ∨ _ ∨ _ ∨ _
  rcases hres with hright | hleft | htetherR | hsource | htetherL
  · exact Or.inl ⟨hright.1, by
      simpa [RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact]
        using
          rlc_twoChannelFullPhysical_reflectedLeftTerminalExactResidue_cleanSeparatorContact
            A B c hcycle ha hb H hclean hright.2⟩
  · exact Or.inr (Or.inl ⟨hleft.1, by
      simpa [RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact]
        using
          rlc_twoChannelFullPhysical_reflectedLeftTerminalExactResidue_cleanSeparatorContact
            A B c hcycle ha hb H hclean hleft.2⟩)
  · exact Or.inr (Or.inr (Or.inl htetherR))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hsource)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr htetherL)))


theorem
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedExactSourceSplice_cleanSeparator
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
        RlcTwoChannelFullPhysicalRowOneCleanExactSourceSpliceEdgeResidue
          gamma gamma' A B c H ur vr ul vl w f g := by
  obtain ⟨p, q, p', q', w, T, V, f, g, hpq, hpq', hpqAdj, hpqAdj',
      hpReach, hpReach', hqOut, hqOut', hwReach, hwT, heT, hTprov, hTedge,
      hfgV, hcross, horder, hres⟩ :=
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedExactSourceSplice
      hn hfaith A B hAright hAleft hBright hBleft hnoPair hzRight hzLeft
        hxPath hyPath qr ql hxz hyAxis hrow hurv hulv
  have hstart : rlc_dualReflect.symm z ∈ c.support := by
    rw [← hxz]
    simpa using hx
  have hend : rlc_dualReflect.symm (gamma'.1.2.1 : Site 2) ∈
      c.support := by
    rw [← hyAxis]
    simpa using hy
  obtain ⟨i, j, H, hi, hj, hHPath, hdH, hdC, hHB, hclean,
      hordered, hcomplementary⟩ :=
    rlc_bookRowOnePhysicalTraceNetworkBracket_separatorCycles
      hn hfaith hzRight c hcycle hstart hend
  have hres' :=
    rlc_twoChannelFullPhysical_rowOneExactSourceSpliceEdgeResidue_cleanSeparatorContact
      A B c hcycle hi hj H hclean w hres
  exact ⟨p, q, p', q', w, T, V, f, g, i, j, H, hi, hj,
    hpq, hpq', hpqAdj, hpqAdj', hpReach, hpReach', hqOut, hqOut',
    hwReach, hwT, heT, hTprov, hTedge, hfgV, hcross, horder, hHPath, hdH, hdC,
    hHB, hclean, hordered, hcomplementary, hres'⟩


theorem
    rlc_twoChannelFullPhysical_exclusiveReflectedLeft_ne_rowOneBracketBoundaryContact
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {t v : Site 2}
    (ht : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
      gamma gamma' (rlc_dualReflect t))
    (hv : rlc_dualReflect v ∈ rlc_pathVertices gamma.1 ∨
      rlc_dualReflect v ∈ rlc_pathVertices gamma'.1 ∨
      v = rlc_dualReflect.symm
        (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) :
    t ≠ v := by
  intro htv
  rcases hv with hvRight | hvLeft | hvCollar
  · exact ht.2.2.1 (by simpa [htv] using hvRight)
  · exact ht.2.2.2 (by simpa [htv] using hvLeft)
  · have hcoord := congrArg (fun z : Site 2 => z 0)
        (congrArg rlc_dualReflect (htv.trans hvCollar))
    have hpositive := ht.1
    simp only [rlc_dualReflect.apply_symm_apply,
      Matrix.cons_val_zero] at hcoord
    omega


theorem rlc_twoChannelFullPhysical_rowOne_reflectedLeftTerminals_ne_chordEndpoints
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u z x y ur ul : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      omega).Walk y ul)
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma' omega qr ql)
    {i j : Nat}
    (hi : (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).getVert i ∈ c.support)
    (hj : (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).getVert j ∈ c.support) :
    (ur ≠ (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).getVert i ∧
      ur ≠ (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).getVert j) ∧
    (ul ≠ (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).getVert i ∧
      ul ≠ (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).getVert j) := by
  have hiProv :=
    rlc_bookRowOnePhysicalTraceNetworkBracket_cycleEndpoint_provenance
      hn gamma gamma' omega hzRight c hcycle
        ((rlc_bookRowOnePhysicalTraceNetworkBracket
          gamma gamma' hzRight).getVert_mem_support i) hi
  have hjProv :=
    rlc_bookRowOnePhysicalTraceNetworkBracket_cycleEndpoint_provenance
      hn gamma gamma' omega hzRight c hcycle
        ((rlc_bookRowOnePhysicalTraceNetworkBracket
          gamma gamma' hzRight).getVert_mem_support j) hj
  exact ⟨⟨
    rlc_twoChannelFullPhysical_exclusiveReflectedLeft_ne_rowOneBracketBoundaryContact
      hn hrow.2.1 hiProv,
    rlc_twoChannelFullPhysical_exclusiveReflectedLeft_ne_rowOneBracketBoundaryContact
      hn hrow.2.1 hjProv⟩,
    ⟨rlc_twoChannelFullPhysical_exclusiveReflectedLeft_ne_rowOneBracketBoundaryContact
      hn hrow.2.2.2 hiProv,
    rlc_twoChannelFullPhysical_exclusiveReflectedLeft_ne_rowOneBracketBoundaryContact
      hn hrow.2.2.2 hjProv⟩⟩


theorem rlc_twoChannelFullPhysical_rowOne_reflectedLeftTerminals_not_mem_bracket
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u z x y ur ul : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) (hurC : ur ∈ c.support) (hulC : ul ∈ c.support)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma' omega qr ql) :
    ur ∉ (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).support ∧
      ul ∉ (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).support := by
  constructor
  · intro hurB
    have hprov :=
      rlc_bookRowOnePhysicalTraceNetworkBracket_boundaryContact_provenance
        hn gamma gamma' omega hzRight hurB
          (rlc_cycleVertex_mem_graphSupport c hcycle hurC)
    exact
      (rlc_twoChannelFullPhysical_exclusiveReflectedLeft_ne_rowOneBracketBoundaryContact
        hn hrow.2.1 hprov) rfl
  · intro hulB
    have hprov :=
      rlc_bookRowOnePhysicalTraceNetworkBracket_boundaryContact_provenance
        hn gamma gamma' omega hzRight hulB
          (rlc_cycleVertex_mem_graphSupport c hcycle hulC)
    exact
      (rlc_twoChannelFullPhysical_exclusiveReflectedLeft_ne_rowOneBracketBoundaryContact
        hn hrow.2.2.2 hprov) rfl


theorem
    rlc_twoChannelFullPhysical_rowOne_reflectedLeftTerminals_ne_bracketSubwalkEndpoints
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u z x y ur vr ul vl a b : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma' omega qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    (H : (hypercubicLattice 2).Walk a b)
    (hHB : H.support ⊆
      (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).support) :
    (ur ≠ a ∧ ur ≠ b) ∧ (ul ≠ a ∧ ul ≠ b) := by
  have huGraph : u ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support :=
    rlc_cycleVertex_mem_graphSupport c hcycle c.start_mem_support
  have hurvC : s(ur, vr) ∈ c.edges :=
    rlc_twoChannelFullPhysical_contactCycle_covers
      gamma gamma' omega c hcycle huGraph c.start_mem_support s(ur, vr)
        ((SimpleGraph.mem_edgeSet _).2 hurv)
  have hulvC : s(ul, vl) ∈ c.edges :=
    rlc_twoChannelFullPhysical_contactCycle_covers
      gamma gamma' omega c hcycle huGraph c.start_mem_support s(ul, vl)
        ((SimpleGraph.mem_edgeSet _).2 hulv)
  have hterminalOff :=
    rlc_twoChannelFullPhysical_rowOne_reflectedLeftTerminals_not_mem_bracket
      hn c hcycle (c.fst_mem_support_of_mem_edges hurvC)
        (c.fst_mem_support_of_mem_edges hulvC) hzRight hrow
  constructor
  · constructor
    · intro hur
      exact hterminalOff.1 (hHB (hur ▸ H.start_mem_support))
    · intro hur
      exact hterminalOff.1 (hHB (hur ▸ H.end_mem_support))
  · constructor
    · intro hul
      exact hterminalOff.2 (hHB (hul ▸ H.start_mem_support))
    · intro hul
      exact hterminalOff.2 (hHB (hul ▸ H.end_mem_support))


theorem rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_meets_bracket_or_orderedArc
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
      (rlc_complementaryContourArc c hx hy).edges) :
    (∃ a ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket
          gamma gamma' hzRight).support,
        a = p ∨ a = p' ∨ a = q ∨ a = q' ∨
          a ∈ rlc_pathVertices gamma'.1) ∨
      ∃ a ∈ (rlc_orderedContourArc c hx hy).support,
        a = p ∨ a = p' ∨ a = q ∨ a = q' ∨
          a ∈ rlc_pathVertices gamma'.1 := by
  let B0 := rlc_bookRowOnePhysicalTraceNetworkBracket
    gamma gamma' hzRight
  have hBx : rlc_dualReflect.symm z = x := by
    rw [← hxz]
    exact rlc_dualReflect.symm_apply_apply x
  have hBy : rlc_dualReflect.symm (gamma'.1.2.1 : Site 2) = y := by
    rw [← hyAxis]
    exact rlc_dualReflect.symm_apply_apply y
  let B : (hypercubicLattice 2).Walk x y := B0.copy hBx hBy
  obtain ⟨Q, W, hQW, hQprov, hWprov⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk
      hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpShift hpShift' horder
  have hWclass : ∀ a ∈ W.support,
      a = p ∨ a = p' ∨ a = q ∨ a = q' ∨
        a ∈ rlc_pathVertices gamma'.1 := by
    intro a ha
    rcases hWprov a ha with rfl | rfl | haQ
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact hQprov a haQ
  have hurC : ur ∈ c.support := c.fst_mem_support_of_mem_edges
    (rlc_orderedContourArc_edges_subset c hx hy hRArc)
  have hulC : ul ∈ c.support := c.fst_mem_support_of_mem_edges
    (rlc_complementaryContourArc_edges_subset c hx hy hLArc)
  have hterminalOff :=
    rlc_twoChannelFullPhysical_rowOne_reflectedLeftTerminals_not_mem_bracket
      hn c hc hurC hulC hzRight hrow
  have hurB : ur ∉ B.support := by
    simpa only [B, SimpleGraph.Walk.support_copy] using hterminalOff.1
  have hulB : ul ∉ B.support := by
    simpa only [B, SimpleGraph.Walk.support_copy] using hterminalOff.2
  rcases rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_orderedArc
      (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
      c hc hx hy B hRArc hLArc hurB hulB hurv hulv hpqAdj hpqAdj'
        hpq hpq' Q W hQW with hB | hArc
  · left
    obtain ⟨a, haW, haB⟩ := hB
    exact ⟨a, by simpa only [B, SimpleGraph.Walk.support_copy] using haB,
      hWclass a haW⟩
  · right
    obtain ⟨a, haW, haArc⟩ := hArc
    exact ⟨a, haArc, hWclass a haW⟩


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_meets_bracket_or_bothOriginalArcs
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
      (rlc_complementaryContourArc c hx hy).edges) :
    ∃ (Q : (hypercubicLattice 2).Walk q q')
      (W : (hypercubicLattice 2).Walk p p'),
      Q.support ⊆ W.support ∧
        (∀ a ∈ Q.support,
          a = p ∨ a = p' ∨ a = q ∨ a = q' ∨
            a ∈ rlc_pathVertices gamma'.1) ∧
        (∀ a ∈ W.support, a = p ∨ a = p' ∨ a ∈ Q.support) ∧
        ((∃ a ∈ W.support,
            a ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket
              gamma gamma' hzRight).support) ∨
          ((∃ a ∈ W.support,
              a ∈ (rlc_orderedContourArc c hx hy).support) ∧
            ∃ a ∈ W.support,
              a ∈ (rlc_complementaryContourArc c hx hy).support)) := by
  let B0 := rlc_bookRowOnePhysicalTraceNetworkBracket
    gamma gamma' hzRight
  have hBx : rlc_dualReflect.symm z = x := by
    rw [← hxz]
    exact rlc_dualReflect.symm_apply_apply x
  have hBy : rlc_dualReflect.symm (gamma'.1.2.1 : Site 2) = y := by
    rw [← hyAxis]
    exact rlc_dualReflect.symm_apply_apply y
  let B : (hypercubicLattice 2).Walk x y := B0.copy hBx hBy
  obtain ⟨Q, W, hQW, hQprov, hWprov⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk
      hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpShift hpShift' horder
  have hurC : ur ∈ c.support := c.fst_mem_support_of_mem_edges
    (rlc_orderedContourArc_edges_subset c hx hy hRArc)
  have hulC : ul ∈ c.support := c.fst_mem_support_of_mem_edges
    (rlc_complementaryContourArc_edges_subset c hx hy hLArc)
  have hterminalOff :=
    rlc_twoChannelFullPhysical_rowOne_reflectedLeftTerminals_not_mem_bracket
      hn c hc hurC hulC hzRight hrow
  have hurB : ur ∉ B.support := by
    simpa only [B, SimpleGraph.Walk.support_copy] using hterminalOff.1
  have hulB : ul ∉ B.support := by
    simpa only [B, SimpleGraph.Walk.support_copy] using hterminalOff.2
  have hordered :=
    rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_orderedArc
      (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
      c hc hx hy B hRArc hLArc hurB hulB hurv hulv hpqAdj hpqAdj'
        hpq hpq' Q W hQW
  have hcomplementary :=
    rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_complementaryArc
      (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
      c hc hx hy B hRArc hLArc hurB hulB hurv hulv hpqAdj hpqAdj'
        hpq hpq' Q W hQW
  refine ⟨Q, W, hQW, hQprov, hWprov, ?_⟩
  rcases hordered with hB | hordered
  · left
    obtain ⟨a, haW, haB⟩ := hB
    exact ⟨a, haW, by
      simpa only [B, B0, SimpleGraph.Walk.support_copy] using haB⟩
  rcases hcomplementary with hB | hcomplementary
  · left
    obtain ⟨a, haW, haB⟩ := hB
    exact ⟨a, haW, by
      simpa only [B, B0, SimpleGraph.Walk.support_copy] using haB⟩
  · exact Or.inr ⟨hordered, hcomplementary⟩


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_indexedContact_or_bothOriginalArcs
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
    ∃ (Q : (hypercubicLattice 2).Walk q q')
      (W : (hypercubicLattice 2).Walk p p'),
      Q.support ⊆ W.support ∧
        (∀ a ∈ Q.support,
          a = p ∨ a = p' ∨ a = q ∨ a = q' ∨
            a ∈ rlc_pathVertices gamma'.1) ∧
        (∀ a ∈ W.support, a = p ∨ a = p' ∨ a ∈ Q.support) ∧
        ((∃ a ∈ W.support, a ∈ H.support) ∨
          (∃ k : Nat, k < i ∧ B.getVert k ∈ W.support) ∨
          (∃ k : Nat, j < k ∧ k ≤ B.length ∧
            B.getVert k ∈ W.support) ∨
          ((∃ a ∈ W.support,
              a ∈ (rlc_orderedContourArc c hx hy).support) ∧
            ∃ a ∈ W.support,
              a ∈ (rlc_complementaryContourArc c hx hy).support)) := by
  dsimp only
  let B := rlc_bookRowOnePhysicalTraceNetworkBracket
    gamma gamma' hzRight
  obtain ⟨Q, W, hQW, hQprov, hWprov, hcontact⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_meets_bracket_or_bothOriginalArcs
      hn c hc hx hy hzRight hxz hyAxis hrow hurv hulv hpq hpq'
        hpqAdj hpqAdj' hpShift hpShift' horder hRArc hLArc
  refine ⟨Q, W, hQW, hQprov, hWprov, ?_⟩
  rcases hcontact with ⟨a, haW, haB⟩ | hboth
  · rcases rlc_walk_mem_indexInterval_or_before_or_after
      B i j hiLength hij hjLength haB with haH | ⟨k, hki, hka⟩ |
        ⟨k, hjk, hkLength, hka⟩
    · exact Or.inl ⟨a, haW, haH⟩
    · exact Or.inr (Or.inl ⟨k, hki, hka.symm ▸ haW⟩)
    · exact Or.inr (Or.inr (Or.inl
        ⟨k, hjk, hkLength, hka.symm ▸ haW⟩))
  · exact Or.inr (Or.inr (Or.inr hboth))


theorem rlc_twoChannelFullPhysical_boundary_exteriorEndpoint_of_reachableOrientation
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {f g p q : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
    (hpq : sharedPrimalEdge f g = s(p, q))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega) :
    q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega := by
  obtain ⟨r, s, hrs, _hrsAdj, hrReach, hsOutside⟩ :=
    rlc_twoChannelFullPhysical_boundary_insideSourceWitness
      gamma gamma' omega hfg
  have hpFilled : p ∈ rlc_twoChannelFullFilledReachSet
      gamma gamma' omega :=
    rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega hpReach
  have heq : s(p, q) = s(r, s) := hpq.symm.trans hrs
  have horient := rlc_orientedBoundaryWitness_unique
    hpFilled hsOutside heq
  simpa [horient.2] using hsOutside


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_vertexSideCases
    {n : Int}
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {u p q p' q' v : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hcycle : c.IsCycle)
    (hqOutside : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hqOutside' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (Q : (hypercubicLattice 2).Walk q q')
    (W : (hypercubicLattice 2).Walk p p')
    (hQprov : ∀ a ∈ Q.support,
      a = p ∨ a = p' ∨ a = q ∨ a = q' ∨
        a ∈ rlc_pathVertices gamma'.1)
    (hWprov : ∀ a ∈ W.support, a = p ∨ a = p' ∨ a ∈ Q.support)
    (hvW : v ∈ W.support) :
    v = p ∨ v = p' ∨ v ∈ c.support ∨
      (v ∉ c.support ∧
        v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A))))) := by
  let omega := rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
  have hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma' :=
    rlc_twoChannelFullPhysicalCutInteriorConfig_failure
      gamma gamma' A hAright hAleft
  have hregion :=
    rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
      gamma gamma' omega c hcycle
  have houtside_of_left {a : Site 2}
      (ha : a ∈ rlc_pathVertices gamma'.1) :
      a ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
    rw [← hregion]
    have haExt :=
      rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
        gamma gamma' hfaith.toRlcBookPositionedTracePair omega hno ha
    simpa [rlc_twoChannelFullFilledReachSet] using haExt
  have houtside : v = p ∨ v = p' ∨
      v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
    rcases hWprov v hvW with rfl | rfl | hvQ
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · rcases hQprov v hvQ with rfl | rfl | rfl | rfl | hvLeft
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (by rwa [← hregion]))
      · exact Or.inr (Or.inr (by rwa [← hregion]))
      · exact Or.inr (Or.inr (houtside_of_left hvLeft))
  rcases houtside with rfl | rfl | hvOutside
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · by_cases hvC : v ∈ c.support
    · exact Or.inr (Or.inr (Or.inl hvC))
    · exact Or.inr (Or.inr (Or.inr ⟨hvC, hvOutside⟩))


theorem rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_originalParity_indexedContact
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
    let P : Site 2 → Prop := fun a =>
      a = p ∨ a = p' ∨ a = q ∨ a = q' ∨
        a ∈ rlc_pathVertices gamma'.1
    (∃ a ∈ H.support, P a) ∨
      (∃ k : Nat, k < i ∧ P (B.getVert k)) ∨
      (∃ k : Nat, j < k ∧ k ≤ B.length ∧ P (B.getVert k)) ∨
      ∃ a ∈ (rlc_orderedContourArc c hx hy).support, P a := by
  dsimp only
  let B := rlc_bookRowOnePhysicalTraceNetworkBracket
    gamma gamma' hzRight
  let P : Site 2 → Prop := fun a =>
    a = p ∨ a = p' ∨ a = q ∨ a = q' ∨
      a ∈ rlc_pathVertices gamma'.1
  apply rlc_exteriorBracket_contact_localized_to_indexInterval
    B i j hiLength hij hjLength P
      (rlc_orderedContourArc c hx hy).support
  simpa only [B, P] using
    (rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_meets_bracket_or_orderedArc
      hn c hc hx hy hzRight hxz hyAxis hrow hurv hulv hpq hpq'
        hpqAdj hpqAdj' hpShift hpShift' horder hRArc hLArc)


theorem rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a b ur vr ul vl p p' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
    (w : (hypercubicLattice 2).Walk p p')
    (T : (hypercubicLattice 2).Walk vr vl)
    (hwReach : ∀ z ∈ w.support,
      z ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hTprov : ∀ z ∈ T.support,
      z = vr ∨ z = ur ∨ z = ul ∨ z = vl ∨
        ∃ r ∈ w.support, phb_doubleDualShift r = z)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    {v : Site 2} (hvH : v ∈ H.support) (hvT : v ∈ T.support) :
    v = a ∨ v = b ∨
      ∃ r ∈ w.support,
        phb_doubleDualShift r = v ∧
          (r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) := by
  rcases hclean v hvH with hva | hvb | hvOff
  · exact Or.inl hva
  · exact Or.inr (Or.inl hvb)
  have huGraph : u ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support :=
    rlc_cycleVertex_mem_graphSupport c hcycle c.start_mem_support
  have huvC : s(ur, vr) ∈ c.edges :=
    rlc_twoChannelFullPhysical_contactCycle_covers
      gamma gamma' omega c hcycle huGraph c.start_mem_support s(ur, vr)
        ((SimpleGraph.mem_edgeSet _).2 hurv)
  have hulC : s(ul, vl) ∈ c.edges :=
    rlc_twoChannelFullPhysical_contactCycle_covers
      gamma gamma' omega c hcycle huGraph c.start_mem_support s(ul, vl)
        ((SimpleGraph.mem_edgeSet _).2 hulv)
  have hurC : ur ∈ c.support := c.fst_mem_support_of_mem_edges huvC
  have hvrC : vr ∈ c.support := c.snd_mem_support_of_mem_edges huvC
  have hulC' : ul ∈ c.support := c.fst_mem_support_of_mem_edges hulC
  have hvlC : vl ∈ c.support := c.snd_mem_support_of_mem_edges hulC
  rcases hTprov v hvT with rfl | rfl | rfl | rfl | ⟨r, hrw, hrv⟩
  · exact False.elim (hvOff.1 hvrC)
  · exact False.elim (hvOff.1 hurC)
  · exact False.elim (hvOff.1 hulC')
  · exact False.elim (hvOff.1 hvlC)
  · refine Or.inr (Or.inr ⟨r, hrw, hrv, ?_⟩)
    exact rlc_twoChannelFullPhysical_shiftedReach_shortBoundaryContact
      c hcycle (hwReach r hrw) (by simpa [hrv] using hvOff.2)
        (by simpa [hrv] using hvOff.1)


theorem rlc_bookRowOnePhysicalTraceNetworkBracket_support_cases
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) {z v : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hv : v ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).support) :
    (∃ w ∈ rlc_pathVertices gamma.1,
        v = rlc_dualReflect.symm w) ∨
      (∃ w ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support,
        v = rlc_dualReflect.symm w) ∨
      ∃ w ∈ rlc_pathVertices gamma'.1,
        v = rlc_dualReflect.symm w := by
  simp only [rlc_bookRowOnePhysicalTraceNetworkBracket,
    SimpleGraph.Walk.support_copy] at hv
  let S := rlc_bookSimpleTraceNetworkBracket gamma gamma' hzRight
    (s := rlc_flipX (gamma'.1.2.1 : Site 2))
      (rlc_bookRowOne_flippedLeftEndpoint_mem gamma')
  change v ∈ (S.map rlc_dualReflectSymmLatticeHom).support at hv
  rw [SimpleGraph.Walk.support_map rlc_dualReflectSymmLatticeHom S,
    List.mem_map] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  dsimp only [S, rlc_bookSimpleTraceNetworkBracket] at hw
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hw
  rcases hw with (hwRight | hwDetour) | hwLeft
  · have hwAmbient :=
      (rlc_ambientCrossingWalk gamma.1).support_dropUntil_subset
        ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices
          gamma.1 z).2 hzRight) hwRight
    exact Or.inl ⟨w,
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma.1 w).1 hwAmbient, rfl⟩
  · exact Or.inr (Or.inl ⟨w, hwDetour, rfl⟩)
  · have hwAmbient :=
      (rlc_ambientCrossingWalk gamma'.1).support_takeUntil_subset_support
        ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1
          (rlc_flipX (rlc_flipX (gamma'.1.2.1 : Site 2)))).2
            (rlc_bookRowOne_flippedLeftEndpoint_mem gamma')) hwLeft
    exact Or.inr (Or.inr ⟨w,
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
        gamma'.1 w).1 hwAmbient, rfl⟩)


end
end StatMech.Universality
