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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part81
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_unconditionalPhysicalTwoChannel
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
        ((∃ e₀ ∈ W.edges,
            Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨
          (s(f, g) = s(ur, vr) ∧
            RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
              gamma gamma' A B c H ur vr) ∨
          (s(f, g) = s(ul, vl) ∧
            RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
              gamma gamma' A B c H ul vl)) ∧
        RlcTwoChannelFullPhysicalRowOneSelectedPrimalFlankContactConclusion
          gamma gamma' c hx hy hzRight H W := by
  let omega := rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
  let B0 := rlc_bookRowOnePhysicalTraceNetworkBracket
    gamma gamma' hzRight
  obtain ⟨Q, W, V, f, g, hQW, hQprov, hWprov, hfgV, hcross,
      hchanging⟩ :=
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_BChanging
      hn hfaith A B hAright hAleft hBright hBleft hnoPair hxPath hyPath
        qr ql hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpReach hpReach'
          hpShift hpShift' horder
  have hqOutside : q ∉ rlc_twoChannelFullFilledReachSet
      gamma gamma' omega := by
    obtain ⟨r, s, hrs, _hrsAdj, _hrReach, hsOutside⟩ :=
      rlc_twoChannelFullPhysical_boundary_insideSourceWitness
        gamma gamma' omega hurv
    have hpFilled : p ∈ rlc_twoChannelFullFilledReachSet
        gamma gamma' omega :=
      rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega hpReach
    have heq : s(p, q) = s(r, s) := hpq.symm.trans hrs
    have horient := rlc_orientedBoundaryWitness_unique
      hpFilled hsOutside heq
    simpa [horient.2] using hsOutside
  have hqOutside' : q' ∉ rlc_twoChannelFullFilledReachSet
      gamma gamma' omega := by
    obtain ⟨r, s, hrs, _hrsAdj, _hrReach, hsOutside⟩ :=
      rlc_twoChannelFullPhysical_boundary_insideSourceWitness
        gamma gamma' omega hulv
    have hpFilled : p' ∈ rlc_twoChannelFullFilledReachSet
        gamma gamma' omega :=
      rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega hpReach'
    have heq : s(p', q') = s(r, s) := hpq'.symm.trans hrs
    have horient := rlc_orientedBoundaryWitness_unique
      hpFilled hsOutside heq
    simpa [horient.2] using hsOutside
  have hstart : rlc_dualReflect.symm z ∈ c.support := by
    rw [← hxz]
    simpa using hx
  have hend : rlc_dualReflect.symm (gamma'.1.2.1 : Site 2) ∈
      c.support := by
    rw [← hyAxis]
    simpa using hy
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
          hn gamma gamma' omega hzRight hurB
            (rlc_cycleVertex_mem_graphSupport c hc hurC)
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
          hn gamma gamma' omega hzRight hulB
            (rlc_cycleVertex_mem_graphSupport c hc hulC)
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
  have hparity :=
    rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_bothArcs
      (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
      c hc hx hy Bxy hRArc hLArc hurB hulB hurv.1 hulv.1 hpqAdj
        hpqAdj' hpq hpq' Q W hQW
  obtain ⟨i0, j0, H0, hi0, hj0, hH0Path, _hdH, _hdC, hH0B,
      hclean0, hordered0, hcomplementary0⟩ :=
    rlc_bookRowOnePhysicalTraceNetworkBracket_separatorCycles
      hn hfaith hzRight c hc hstart hend
  have hchanging0 :=
    rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_cleanTerminalCallbacks
      A B c hc hi0 hj0 H0 hclean0 W hchanging
  rcases hparity with ⟨v, hvW, hvBxy⟩ | hboth
  · have hvB : v ∈ B0.support := by
      simpa only [Bxy, B0, SimpleGraph.Walk.support_copy] using hvBxy
    have hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
        rlc_finiteTwoChannelConnectorEvent gamma gamma' :=
      rlc_twoChannelFullPhysicalCutInteriorConfig_failure
        gamma gamma' A hAright hAleft
    have hregion :=
      rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
        gamma gamma' omega c hc
    have houtside_of_left {a : Site 2}
        (ha : a ∈ rlc_pathVertices gamma'.1) :
        a ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
      rw [← hregion]
      have haExt :=
        rlc_leftPathVertex_mem_twoChannelFullExteriorSet_of_failure
          gamma gamma' hfaith.toRlcBookPositionedTracePair omega hno ha
      simpa [rlc_twoChannelFullFilledReachSet] using haExt
    have hvside : v = p ∨ v = p' ∨ v ∈ c.support ∨
        (v ∉ c.support ∧
          v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
            (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) := by
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
    rcases hvside with hvp | hvp' | hvC | ⟨hvC, hvOutside⟩
    · refine ⟨Q, W, V, f, g, i0, j0, H0, hi0, hj0, hQW, hQprov,
        hWprov, hfgV, hcross, hH0Path, hH0B, hclean0, hordered0,
        hcomplementary0, hchanging0, ?_⟩
      exact Or.inr (Or.inl ⟨v, hvW, hvB, Or.inl hvp⟩)
    · refine ⟨Q, W, V, f, g, i0, j0, H0, hi0, hj0, hQW, hQprov,
        hWprov, hfgV, hcross, hH0Path, hH0B, hclean0, hordered0,
        hcomplementary0, hchanging0, ?_⟩
      exact Or.inr (Or.inl ⟨v, hvW, hvB, Or.inr hvp'⟩)
    · refine ⟨Q, W, V, f, g, i0, j0, H0, hi0, hj0, hQW, hQprov,
        hWprov, hfgV, hcross, hH0Path, hH0B, hclean0, hordered0,
        hcomplementary0, hchanging0, ?_⟩
      exact Or.inr (Or.inr (Or.inl ⟨v, hvW, hvB, hvC⟩))
    · obtain ⟨i, j, H, hi, hj, hHPath, _hvW, hvH, hHB, hclean,
          hordered, hcomplementary, hchanging'⟩ :=
        rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_exteriorBracketContact_reselect_cleanTwoChannel
          hn hfaith A B c hc hzRight hstart hend W hvW hvB hvC hvOutside
            hchanging
      exact ⟨Q, W, V, f, g, i, j, H, hi, hj, hQW, hQprov, hWprov,
        hfgV, hcross, hHPath, hHB, hclean, hordered, hcomplementary,
        hchanging', Or.inl ⟨v, hvW, hvH⟩⟩
  · exact ⟨Q, W, V, f, g, i0, j0, H0, hi0, hj0, hQW, hQprov,
      hWprov, hfgV, hcross, hH0Path, hH0B, hclean0, hordered0,
      hcomplementary0, hchanging0,
      Or.inr (Or.inr (Or.inr hboth))⟩


theorem
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_cleanTwoChannel
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
    {u a b x y ur vr ul vl p q p' q' : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Walk u u)
    (hc : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hclean : ∀ z ∈ H.support,
      z = a ∨ z = b ∨ (z ∉ c.support ∧
        z ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A))))))
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
    (hterminalNe : (ur ≠ a ∧ ur ≠ b) ∧ (ul ≠ a ∧ ul ≠ b))
    (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c ha hb).edges)
    (hLArc : s(ul, vl) ∈
      (rlc_complementaryContourArc c ha hb).edges)
    (hcycles :
      (H.append ((rlc_orderedContourArc c ha hb).mapLe
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A)))).reverse).IsCycle ∧
      (H.append ((rlc_complementaryContourArc c ha hb).mapLe
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig
              gamma gamma' A)))).reverse).IsCycle) :
    ∃ (Q : (hypercubicLattice 2).Walk q q')
      (W : (hypercubicLattice 2).Walk p p')
      (V : (hypercubicLattice 2).Walk
        (rlc_dualReflect.symm (gamma.1.1 : Site 2))
        (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2)))
      (f g : Site 2),
      Q.support ⊆ W.support ∧
        (∀ z ∈ Q.support,
          z = p ∨ z = p' ∨ z = q ∨ z = q' ∨
            z ∈ rlc_pathVertices gamma'.1) ∧
        (∀ z ∈ W.support, z = p ∨ z = p' ∨ z ∈ Q.support) ∧
        s(f, g) ∈ V.edges ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut
          (rlc_twoChannelFullPhysicalLiftVertexCut B)
            s(rlc_dualReflect f, rlc_dualReflect g) ∧
        (((∃ e₀ ∈ W.edges,
              Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨
            (s(f, g) = s(ur, vr) ∧
              RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
                gamma gamma' A B c H ur vr) ∨
            (s(f, g) = s(ul, vl) ∧
              RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact
                gamma gamma' A B c H ul vl)) ∧
          ((∃ z ∈ W.support, z ∈ H.support) ∨
            ((∃ z ∈ W.support,
                z ∈ (rlc_orderedContourArc c ha hb).support) ∧
              ∃ z ∈ W.support,
                z ∈ (rlc_complementaryContourArc c ha hb).support))) := by
  obtain ⟨Q, W, V, f, g, hQW, hQprov, hWprov, hfgV, hcross,
      hchanging, hcyclic⟩ :=
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_twoChannel
      hn hfaith A B hAright hAleft hBright hBleft hnoPair c hc ha hb H
        hclean hxPath hyPath qr ql hrow hurv hulv hpq hpq' hpqAdj hpqAdj'
          hpReach hpReach' hpShift hpShift' horder hterminalNe hRArc hLArc
            hcycles
  have hchanging' :=
    rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_cleanTerminalCallbacks
      A B c hc ha hb H hclean W hchanging
  exact ⟨Q, W, V, f, g, hQW, hQprov, hWprov, hfgV, hcross,
    hchanging', hcyclic⟩


theorem
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_cleanSeparator_terminalResidue_or_bridge
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
    ∃ (T : (hypercubicLattice 2).Walk vr vl)
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
      (∀ v ∈ T.support,
        v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
          ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma'
              (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A),
            phb_doubleDualShift a = v) ∧
      ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) <
        ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul) ∧
      s(f, g) ∈ V.edges ∧
      rlc_twoChannelFullPhysicalEdgeCrossesCut
        (rlc_twoChannelFullPhysicalLiftVertexCut B)
          s(rlc_dualReflect f, rlc_dualReflect g) ∧
      (s(f, g) ∈ T.edges ∨
        (s(f, g) = s(ur, vr) ∧
          RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue
            gamma gamma' A B ur vr) ∨
        (s(f, g) = s(ul, vl) ∧
          RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue
            gamma gamma' A B ul vl)) ∧
      H.IsPath ∧
      rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∈ H.support ∧
      rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∉ c.support ∧
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
              gamma gamma' A)))).reverse).IsCycle := by
  obtain ⟨T, V, f, g, hTprov, horder, hfgV, hcross, hlocation⟩ :=
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedBChangingSplice
      hn hfaith A B hAright hAleft hBright hBleft hnoPair hzRight hzLeft
        hxPath hyPath qr ql hxz hyAxis hrow hurv hulv
  have hterminal :=
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_exactTerminalResidue_or_bridge
      hn A B hAright hAleft hnoPair qr ql hrow hurv hulv hcross hlocation
  have hstart : rlc_dualReflect.symm z ∈ c.support := by
    rw [← hxz]
    simpa using hx
  have hend : rlc_dualReflect.symm (gamma'.1.2.1 : Site 2) ∈ c.support := by
    rw [← hyAxis]
    simpa using hy
  obtain ⟨i, j, H, hi, hj, hHPath, hdH, hdC, hHB, hclean,
      hordered, hcomplementary⟩ :=
    rlc_bookRowOnePhysicalTraceNetworkBracket_separatorCycles
      hn hfaith hzRight c hcycle hstart hend
  exact ⟨T, V, f, g, i, j, H, hi, hj, hTprov, horder, hfgV,
    hcross, hterminal, hHPath, hdH, hdC, hHB, hclean,
    hordered, hcomplementary⟩


end
end StatMech.Universality
