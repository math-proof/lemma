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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part80
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_cleanTerminalCallbacks
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
    (W : (hypercubicLattice 2).Walk p p')
    (hchanging :
      ((∃ e₀ ∈ W.edges,
          Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨
        (s(f, g) = s(ur, vr) ∧
          RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue
            gamma gamma' A B ur vr) ∨
        (s(f, g) = s(ul, vl) ∧
          RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue
            gamma gamma' A B ul vl))) :
    ((∃ e₀ ∈ W.edges,
        Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨
      (s(f, g) = s(ur, vr) ∧
        RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
          gamma gamma' A B c H ur vr) ∨
      (s(f, g) = s(ul, vl) ∧
        RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
          gamma gamma' A B c H ul vl)) := by
  rcases hchanging with hW | hright | hleft
  · exact Or.inl hW
  · exact Or.inr (Or.inl ⟨hright.1, by
      simpa [RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact]
        using
          rlc_twoChannelFullPhysical_reflectedLeftTerminalExactResidue_cleanSeparatorContact
            A B c hcycle ha hb H hclean hright.2⟩)
  · exact Or.inr (Or.inr ⟨hleft.1, by
      simpa [RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact]
        using
          rlc_twoChannelFullPhysical_reflectedLeftTerminalExactResidue_cleanSeparatorContact
            A B c hcycle ha hb H hclean hleft.2⟩)


theorem
    rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_exteriorBracketContact_reselect_cleanTwoChannel
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (A B : Set (RlcConnectorVertex n))
    {u z ur vr ul vl p p' f g v : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hcycle : c.IsCycle)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hstart : rlc_dualReflect.symm z ∈ c.support)
    (hend : rlc_dualReflect.symm (gamma'.1.2.1 : Site 2) ∈ c.support)
    (W : (hypercubicLattice 2).Walk p p')
    (hvW : v ∈ W.support)
    (hvB : v ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket
      gamma gamma' hzRight).support)
    (hvC : v ∉ c.support)
    (hvOutside : v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))))
    (hchanging :
      ((∃ e₀ ∈ W.edges,
          Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨
        (s(f, g) = s(ur, vr) ∧
          RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue
            gamma gamma' A B ur vr) ∨
        (s(f, g) = s(ul, vl) ∧
          RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue
            gamma gamma' A B ul vl))) :
    ∃ (i j : Nat)
      (H : (hypercubicLattice 2).Walk
        ((rlc_bookRowOnePhysicalTraceNetworkBracket
          gamma gamma' hzRight).getVert i)
        ((rlc_bookRowOnePhysicalTraceNetworkBracket
          gamma gamma' hzRight).getVert j))
      (hi : (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).getVert i ∈ c.support)
      (hj : (rlc_bookRowOnePhysicalTraceNetworkBracket
        gamma gamma' hzRight).getVert j ∈ c.support),
      H.IsPath ∧ v ∈ W.support ∧ v ∈ H.support ∧
        H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket
          gamma gamma' hzRight).support ∧
        (∀ w ∈ H.support,
          w = (rlc_bookRowOnePhysicalTraceNetworkBracket
              gamma gamma' hzRight).getVert i ∨
            w = (rlc_bookRowOnePhysicalTraceNetworkBracket
              gamma gamma' hzRight).getVert j ∨
            (w ∉ c.support ∧
              w ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
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
        ((∃ e₀ ∈ W.edges,
            Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨
          (s(f, g) = s(ur, vr) ∧
            RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
              gamma gamma' A B c H ur vr) ∨
          (s(f, g) = s(ul, vl) ∧
            RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
              gamma gamma' A B c H ul vl)) := by
  let B0 := rlc_bookRowOnePhysicalTraceNetworkBracket
    gamma gamma' hzRight
  obtain ⟨i, j, _hiLength, _hij, _hjLength, hi, hj, hHPath,
      _hvW, hvH, hHB, hclean, hordered, hcomplementary⟩ :=
    rlc_exteriorWalk_exteriorContact_reselect_separatorCycles_indexed
      (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))
      c hcycle B0
        (rlc_bookRowOnePhysicalTraceNetworkBracket_isPath
          hn hfaith hzRight)
        hstart hend W hvW hvB hvC hvOutside
  have hchanging' :=
    rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_cleanTerminalCallbacks
      A B c hcycle hi hj
        (rlc_walkIndexInterval B0 i j _hiLength _hij _hjLength)
          hclean W hchanging
  exact ⟨i, j,
    rlc_walkIndexInterval B0 i j _hiLength _hij _hjLength,
    hi, hj, hHPath, hvW, hvH, hHB, hclean, hordered, hcomplementary,
    hchanging'⟩


theorem
    rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_cleanTerminalCallbacks_fullBracket
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A B : Set (RlcConnectorVertex n))
    {u a b z x y ur vr ul vl p q p' q' f g : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ v ∈ H.support,
      v = a ∨ v = b ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig
                gamma gamma' A))))))
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hxz : rlc_dualReflect x = z)
    (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A) qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpqAdj' : (hypercubicLattice 2).Adj p' q')
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c hx hy).edges)
    (hLArc : s(ul, vl) ∈
      (rlc_complementaryContourArc c hx hy).edges)
    (Q : (hypercubicLattice 2).Walk q q')
    (W : (hypercubicLattice 2).Walk p p')
    (hQW : Q.support ⊆ W.support)
    (hchanging :
      ((∃ e₀ ∈ W.edges,
          Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨
        (s(f, g) = s(ur, vr) ∧
          RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue
            gamma gamma' A B ur vr) ∨
        (s(f, g) = s(ul, vl) ∧
          RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue
            gamma gamma' A B ul vl))) :
    (((∃ e₀ ∈ W.edges,
          Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨
        (s(f, g) = s(ur, vr) ∧
          RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
            gamma gamma' A B c H ur vr) ∨
        (s(f, g) = s(ul, vl) ∧
          RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
            gamma gamma' A B c H ul vl)) ∧
      ((∃ v ∈ W.support,
          v ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket
            gamma gamma' hzRight).support) ∨
        ((∃ v ∈ W.support,
          v ∈ (rlc_orderedContourArc c hx hy).support) ∧
          ∃ v ∈ W.support,
            v ∈ (rlc_complementaryContourArc c hx hy).support))) := by
  have hchanging' :=
    rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_cleanTerminalCallbacks
      A B c hcycle ha hb H hclean W hchanging
  let B0 := rlc_bookRowOnePhysicalTraceNetworkBracket
    gamma gamma' hzRight
  have hBx : rlc_dualReflect.symm z = x := by
    rw [← hxz]
    exact rlc_dualReflect.symm_apply_apply x
  have hBy : rlc_dualReflect.symm (gamma'.1.2.1 : Site 2) = y := by
    rw [← hyAxis]
    exact rlc_dualReflect.symm_apply_apply y
  let Bxy : (hypercubicLattice 2).Walk x y := B0.copy hBx hBy
  have hurC : ur ∈ c.support := c.fst_mem_support_of_mem_edges
    (rlc_orderedContourArc_edges_subset c hx hy hRArc)
  have hulC : ul ∈ c.support := c.fst_mem_support_of_mem_edges
    (rlc_complementaryContourArc_edges_subset c hx hy hLArc)
  have hterminalOff : ur ∉ B0.support ∧ ul ∉ B0.support := by
    constructor
    · intro hurB
      have hprov :=
        rlc_bookRowOnePhysicalTraceNetworkBracket_boundaryContact_provenance
          hn gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
              hzRight hurB
                (rlc_cycleVertex_mem_graphSupport c hcycle hurC)
      rcases hprov with hright | hleft | hcollar
      · exact hrow.2.1.2.2.1 hright
      · exact hrow.2.1.2.2.2 hleft
      · have hcoord := congrArg (fun z : Site 2 => z 0)
            (congrArg rlc_dualReflect hcollar)
        have hpositive := hrow.2.1.1
        simp only [rlc_dualReflect.apply_symm_apply,
          Matrix.cons_val_zero] at hcoord
        omega
    · intro hulB
      have hprov :=
        rlc_bookRowOnePhysicalTraceNetworkBracket_boundaryContact_provenance
          hn gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)
              hzRight hulB
                (rlc_cycleVertex_mem_graphSupport c hcycle hulC)
      rcases hprov with hright | hleft | hcollar
      · exact hrow.2.2.2.2.2.1 hright
      · exact hrow.2.2.2.2.2.2 hleft
      · have hcoord := congrArg (fun z : Site 2 => z 0)
            (congrArg rlc_dualReflect hcollar)
        have hpositive := hrow.2.2.2.1
        simp only [rlc_dualReflect.apply_symm_apply,
          Matrix.cons_val_zero] at hcoord
        omega
  have hurB : ur ∉ Bxy.support := by
    simpa only [Bxy, SimpleGraph.Walk.support_copy] using hterminalOff.1
  have hulB : ul ∉ Bxy.support := by
    simpa only [Bxy, SimpleGraph.Walk.support_copy] using hterminalOff.2
  have hcyclic :=
    rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_bothArcs
      (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))
      c hcycle hx hy Bxy hRArc hLArc hurB hulB hurv hulv hpqAdj
        hpqAdj' hpq hpq' Q W hQW
  refine ⟨hchanging', ?_⟩
  rcases hcyclic with ⟨v, hvW, hvB⟩ | hboth
  · exact Or.inl ⟨v, hvW, by
      simpa only [Bxy, B0, SimpleGraph.Walk.support_copy] using hvB⟩
  · exact Or.inr hboth


theorem
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_automaticFullBracketCleanTwoChannel
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
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
    {u z x y ur vr ul vl p q p' q' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hc : c.IsCycle) (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
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
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpqAdj' : (hypercubicLattice 2).Adj p' q')
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
    (hpShift : phb_doubleDualShift p = vr)
    (hpShift' : phb_doubleDualShift p' = vl)
    (horder : ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) <
      ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
    (hxz : rlc_dualReflect x = z)
    (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
    (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c hx hy).edges)
    (hLArc : s(ul, vl) ∈
      (rlc_complementaryContourArc c hx hy).edges) :
    ∃ (Q : (hypercubicLattice 2).Walk q q')
      (W : (hypercubicLattice 2).Walk p p')
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
      Q.support ⊆ W.support ∧
        (∀ v ∈ Q.support,
          v = p ∨ v = p' ∨ v = q ∨ v = q' ∨
            v ∈ rlc_pathVertices gamma'.1) ∧
        (∀ v ∈ W.support, v = p ∨ v = p' ∨ v ∈ Q.support) ∧
        s(f, g) ∈ V.edges ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut
          (rlc_twoChannelFullPhysicalLiftVertexCut B)
            s(rlc_dualReflect f, rlc_dualReflect g) ∧
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
        (((∃ e₀ ∈ W.edges,
              Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨
            (s(f, g) = s(ur, vr) ∧
              RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
                gamma gamma' A B c H ur vr) ∨
            (s(f, g) = s(ul, vl) ∧
              RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
                gamma gamma' A B c H ul vl)) ∧
          ((∃ v ∈ W.support,
              v ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket
                gamma gamma' hzRight).support) ∨
            ((∃ v ∈ W.support,
                v ∈ (rlc_orderedContourArc c hx hy).support) ∧
              ∃ v ∈ W.support,
                v ∈ (rlc_complementaryContourArc c hx hy).support))) := by
  obtain ⟨Q, W, V, f, g, hQW, hQprov, hWprov, hfgV, hcross,
      hchanging⟩ :=
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_BChanging
      hn hfaith A B hAright hAleft hBright hBleft hnoPair hxPath hyPath
        qr ql hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpReach hpReach'
          hpShift hpShift' horder
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
      hn hfaith hzRight c hc hstart hend
  have hphysical :=
    rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_cleanTerminalCallbacks_fullBracket
      hn A B c hc hi hj hx hy H hclean hzRight hxz hyAxis hrow
        hurv.1 hulv.1 hpqAdj hpqAdj' hpq hpq' hRArc hLArc Q W hQW
          hchanging
  exact ⟨Q, W, V, f, g, i, j, H, hi, hj, hQW, hQprov, hWprov,
    hfgV, hcross, hHPath, hdH, hdC, hHB, hclean, hordered,
    hcomplementary, hphysical⟩


end
end StatMech.Universality
