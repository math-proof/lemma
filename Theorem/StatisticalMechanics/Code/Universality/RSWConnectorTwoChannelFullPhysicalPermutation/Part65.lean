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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part65
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelFullPhysical_noPair_sourceSplice_BChanging_exactSourceEdge
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
    {x y ur vr ul vl : Site 2}
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk y ul)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig
          gamma gamma' A))).Adj ul vl)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
    ∃ (p q p' q' : Site 2)
      (w : (hypercubicLattice 2).Walk p p')
      (T : (hypercubicLattice 2).Walk vr vl)
      (V : (hypercubicLattice 2).Walk
        (rlc_dualReflect.symm (gamma.1.1 : Site 2))
        (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2)))
      (f g : Site 2),
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
        (∀ z ∈ T.support,
          z = vr ∨ z = ur ∨ z = ul ∨ z = vl ∨
            ∃ a ∈ w.support, phb_doubleDualShift a = z) ∧
        (∀ e ∈ T.edges,
          (∀ z ∈ e, z = vr ∨ z = ur ∨
            z = phb_doubleDualShift p) ∨
          (∃ e₀ ∈ w.edges, Sym2.map phb_doubleDualShift e₀ = e) ∨
          ∀ z ∈ e, z = vl ∨ z = ul ∨
            z = phb_doubleDualShift p') ∧
        s(f, g) ∈ V.edges ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut
          (rlc_twoChannelFullPhysicalLiftVertexCut B)
            s(rlc_dualReflect f, rlc_dualReflect g) ∧
        RlcTwoChannelFullPhysicalExactSourceSpliceEdgeResidue
          gamma gamma' A B ur vr ul vl w f g := by
  let omega :=
    rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A
  obtain ⟨p, q, p', q', w, T, hpq, hpq', hpqAdj, hpqAdj', hpReach,
      hpReach', hqOut, hqOut', hwReach, hwOpen, hwT, heT, _hqT, _hqT',
      hTprov, hTedge⟩ :=
    rlc_twoChannelFullPhysical_boundary_directedReachableShiftWalk_withEdges
      hurv hulv
  have hTBox : ∀ v ∈ T.support,
      v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
    intro v hv
    rcases hTprov v hv with rfl | rfl | rfl | rfl | ⟨a, ha, rfl⟩
    · have hbox :=
        rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox
          hn gamma gamma' omega hurv.mem_support_right
      rw [mem_rect] at hbox ⊢
      omega
    · have hbox :=
        rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox
          hn gamma gamma' omega hurv.mem_support_left
      rw [mem_rect] at hbox ⊢
      omega
    · have hbox :=
        rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox
          hn gamma gamma' omega hulv.mem_support_left
      rw [mem_rect] at hbox ⊢
      omega
    · have hbox :=
        rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox
          hn gamma gamma' omega hulv.mem_support_right
      rw [mem_rect] at hbox ⊢
      omega
    · have hbox := rlc_doubleDualShift_mem_translatedRect
        (rlc_twoChannelFullReachSet_subset_box
          gamma gamma' omega (hwReach a ha))
      rw [mem_rect] at hbox ⊢
      omega
  obtain ⟨V, f, g, hfgV, hcross, hlocation⟩ :=
    rlc_twoChannelFullPhysical_sourceSplice_BChanging_terminal_or_bridge
      hfaith A B hAright hAleft hBright hBleft hnoPair qr ql T hurv hulv
        hxPath hyPath hTBox
  refine ⟨p, q, p', q', w, T, V, f, g, hpq, hpq', hpqAdj, hpqAdj',
    hpReach, hpReach', hqOut, hqOut', hwReach, hwT, heT, hTprov, hTedge,
    hfgV, hcross, ?_⟩
  change s(f, g) = s(ur, vr) ∨
    s(f, g) = s(ul, vl) ∨
    (s(f, g) = s(vr, phb_doubleDualShift p) ∨
      s(f, g) = s(ur, phb_doubleDualShift p)) ∨
    (∃ e₀ ∈ w.edges,
      Sym2.map phb_doubleDualShift e₀ = s(f, g) ∧
        rlc_twoChannelFullAmbientConfig gamma gamma' omega e₀ = true ∧
        ((∃ source :
            (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
            source.1.map Subtype.val = e₀) ∨
          e₀ ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∧
        e₀ ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut
          (rlc_twoChannelFullPhysicalLiftVertexCut B)
            (Sym2.map rlc_flipX e₀) ∧
        ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
          target.1.map Subtype.val = Sym2.map rlc_flipX e₀ ∧
            ((¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
                (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) ∨
              ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
                physical.1 = target ∧
                  ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
                    (rlc_twoChannelFullPhysicalSourceEdge physical).1)) ∨
    (s(f, g) = s(vl, phb_doubleDualShift p') ∨
      s(f, g) = s(ul, phb_doubleDualShift p'))
  rcases hlocation with hright | hbridge | hleft
  · exact Or.inl hright
  · rcases hTedge s(f, g) hbridge with htetherR | hsource | htetherL
    · rcases rlc_latticeEdge_threeSupport_cases
          (V.adj_of_mem_edges hfgV) htetherR with
        hterminal | hvrShift | hurShift
      · exact Or.inl (by simpa [Sym2.eq_swap] using hterminal)
      · exact Or.inr (Or.inr (Or.inl (Or.inl hvrShift)))
      · exact Or.inr (Or.inr (Or.inl (Or.inr hurShift)))
    · obtain ⟨e₀, he₀, hshift⟩ := hsource
      have hcrossMap : rlc_twoChannelFullPhysicalEdgeCrossesCut
          (rlc_twoChannelFullPhysicalLiftVertexCut B)
            (Sym2.map rlc_dualReflect s(f, g)) := by
        simpa [Sym2.map_mk] using hcross
      rw [← hshift, Sym2.map_map] at hcrossMap
      have hsourceCross : rlc_twoChannelFullPhysicalEdgeCrossesCut
          (rlc_twoChannelFullPhysicalLiftVertexCut B)
            (Sym2.map rlc_flipX e₀) := by
        simpa [Function.comp_def] using hcrossMap
      have he₀Open := hwOpen e₀ he₀
      have hsourceOrTrace :=
        rlc_twoChannelFullAmbientConfig_open_source_or_originalTrace
          gamma gamma' omega he₀Open
      have he₀Planar :=
        rlc_twoChannelFullAmbientConfig_open_mem_planarEdges
          gamma gamma' omega he₀Open
      have htargetOrNot :
          (∃ target :
              (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
              target.1.map Subtype.val = Sym2.map rlc_flipX e₀) ∨
            Sym2.map rlc_flipX e₀ ∉
              rlc_connectorCentralFacePlanarEdges gamma gamma' := by
        induction e₀ using Sym2.inductionOn with
        | _ a b =>
            have hab := w.adj_of_mem_edges he₀
            rcases rlc_flipXEdge_target_or_originalTrace_or_notPlanar
                gamma gamma' hab with htarget | htrace | hnotPlanar
            · exact Or.inl (by simpa [Sym2.map_mk] using htarget)
            · exact False.elim
                ((rlc_originalTraceEdge_not_crosses_liftVertexCut
                  gamma gamma' B hBright hBleft htrace) (by
                    simpa [Sym2.map_mk] using hsourceCross))
            · exact Or.inr (by simpa [Sym2.map_mk] using hnotPlanar)
      have hreflectedPlanar : Sym2.map rlc_flipX e₀ ∈
          rlc_connectorCentralFacePlanarEdges gamma gamma' := by
        induction e₀ using Sym2.inductionOn with
        | _ a b =>
            simpa [Sym2.map_mk] using
              hfaith.centralFacePlanarEdges_flipX
                (w.adj_of_mem_edges he₀) he₀Planar
      have htarget : ∃ target :
          (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
          target.1.map Subtype.val = Sym2.map rlc_flipX e₀ :=
        htargetOrNot.resolve_right (fun hnot ↦ hnot hreflectedPlanar)
      obtain ⟨target, htarget⟩ := htarget
      have hcrossTarget : rlc_twoChannelFullPhysicalEdgeCrossesCut
          (rlc_twoChannelFullPhysicalLiftVertexCut B)
            (target.1.map Subtype.val) := by
        rw [htarget]
        exact hsourceCross
      have hphysicalStatus :=
        rlc_twoChannelFullPhysical_noPair_rawTarget_sourceMissing_or_notAcrossA
          A B hnoPair target hcrossTarget
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨e₀, he₀, hshift, he₀Open, hsourceOrTrace, he₀Planar,
          hsourceCross, target, htarget, hphysicalStatus⟩)))
    · rcases rlc_latticeEdge_threeSupport_cases
          (V.adj_of_mem_edges hfgV) htetherL with
        hterminal | hvlShift | hulShift
      · exact Or.inr (Or.inl (by
          simpa [Sym2.eq_swap] using hterminal))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hvlShift))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hulShift))))
  · exact Or.inr (Or.inl hleft)


theorem
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_exactSourceSpliceResidue
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (A B : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    {x y ur vr ul vl p p' f g : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma'
      (rlc_twoChannelFullPhysicalCutInteriorConfig
        gamma gamma' A)).Walk y ul}
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
    (w : (hypercubicLattice 2).Walk p p')
    (hcross : rlc_twoChannelFullPhysicalEdgeCrossesCut
      (rlc_twoChannelFullPhysicalLiftVertexCut B)
        s(rlc_dualReflect f, rlc_dualReflect g))
    (hres : RlcTwoChannelFullPhysicalExactSourceSpliceEdgeResidue
      gamma gamma' A B ur vr ul vl w f g) :
    RlcTwoChannelFullPhysicalRowOneExactSourceSpliceEdgeResidue
      gamma gamma' A B ur vr ul vl w f g := by
  change s(f, g) = s(ur, vr) ∨
    s(f, g) = s(ul, vl) ∨
    (s(f, g) = s(vr, phb_doubleDualShift p) ∨
      s(f, g) = s(ur, phb_doubleDualShift p)) ∨
    _ ∨
    (s(f, g) = s(vl, phb_doubleDualShift p') ∨
      s(f, g) = s(ul, phb_doubleDualShift p')) at hres
  change (s(f, g) = s(ur, vr) ∧ _) ∨
    (s(f, g) = s(ul, vl) ∧ _) ∨
    (s(f, g) = s(vr, phb_doubleDualShift p) ∨
      s(f, g) = s(ur, phb_doubleDualShift p)) ∨
    _ ∨
    (s(f, g) = s(vl, phb_doubleDualShift p') ∨
      s(f, g) = s(ul, phb_doubleDualShift p'))
  rcases hres with hright | hleft | htetherR | hsource | htetherL
  · have hmap := congrArg (Sym2.map rlc_dualReflect) hright
    simp only [Sym2.map_mk] at hmap
    have hfailure :=
      rlc_twoChannelFullPhysical_noPair_exclusiveReflectedLeft_terminalFailure
        gamma gamma' A B hAright hAleft hnoPair hurv hrow.2.1 (by
          rw [← hmap]
          exact hcross)
    exact Or.inl ⟨hright,
      rlc_twoChannelFullPhysical_reflectedLeftTerminalFailure_exactResidue
        hn gamma gamma' A B hAright hAleft hurv hrow.2.1 hfailure⟩
  · have hmap := congrArg (Sym2.map rlc_dualReflect) hleft
    simp only [Sym2.map_mk] at hmap
    have hfailure :=
      rlc_twoChannelFullPhysical_noPair_exclusiveReflectedLeft_terminalFailure
        gamma gamma' A B hAright hAleft hnoPair hulv hrow.2.2.2 (by
          rw [← hmap]
          exact hcross)
    exact Or.inr (Or.inl ⟨hleft,
      rlc_twoChannelFullPhysical_reflectedLeftTerminalFailure_exactResidue
        hn gamma gamma' A B hAright hAleft hulv hrow.2.2.2 hfailure⟩)
  · exact Or.inr (Or.inr (Or.inl htetherR))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hsource)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr htetherL)))


theorem
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedExactSourceSplice
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
    {z x y ur vr ul vl : Site 2}
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
      (f g : Site 2),
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
        RlcTwoChannelFullPhysicalRowOneExactSourceSpliceEdgeResidue
          gamma gamma' A B ur vr ul vl w f g := by
  obtain ⟨p, q, p', q', w, T, V, f, g, hpq, hpq', hpqAdj, hpqAdj',
      hpReach, hpReach', hqOut, hqOut', hwReach, hwT, heT, hTprov, hTedge,
      hfgV, hcross, hres⟩ :=
    rlc_twoChannelFullPhysical_noPair_sourceSplice_BChanging_exactSourceEdge
      hn hfaith A B hAright hAleft hBright hBleft hnoPair qr ql hurv hulv
        hxPath hyPath
  have hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) :=
    rlc_twoChannelFullPhysical_noGoodComponent_of_noPair
      gamma gamma' A B hAright hAleft hBright hBleft hnoPair
  have horder := rlc_twoChannelFullPhysical_sameReflectedLeft_end_order
    hnoGood z hzRight hzLeft hxPath hyPath qr ql hxz hyAxis
      hrow.1 hrow.2.2.1 hrow.2.1 hrow.2.2.2
  have hres' :=
    rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_exactSourceSpliceResidue
      hn A B hAright hAleft hnoPair hrow hurv hulv w hcross hres
  exact ⟨p, q, p', q', w, T, V, f, g, hpq, hpq', hpqAdj, hpqAdj',
    hpReach, hpReach', hqOut, hqOut', hwReach, hwT, heT, hTprov, hTedge,
    hfgV, hcross, horder, hres'⟩


theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateBracket
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {z x y ur ul : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hxOrder : rlc_flipX (rlc_dualReflect x) ∈
      (right.map rlc_flipXLatticeHom).support)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hrightPrefix : RlcBookRightPrefixRankAt gamma right)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (hqrLeft : ∀ e ∈ qr.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
    (hqlRight : ∀ e ∈ ql.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
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
    RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket
      gamma gamma' (z := z) (x := x) (y := y) flipLeft := by
  have hurLeft :=
    rlc_twoChannelFullPhysical_reflectedLeftWalk_terminal_location
      hfaith qr (Or.inl hxPath) hqrLeft hurLoc
  have hulRight :=
    rlc_twoChannelFullPhysical_reflectedRightWalk_terminal_location
      hfaith ql (Or.inr hyPath) hqlRight hulLoc
  exact ⟨
    rlc_twoChannelFullPhysical_rightContact_reflectedLeft_candidateRetreat
      right qr hzCandidate hxPath hxOrder hrightPrefix hqrLeft hurLeft.2.1,
    rlc_twoChannelFullPhysical_leftContact_reflectedRight_candidateProgress
      flipLeft ql hzCandidate hyPath hyOrder hflipLeftRank hqlRight
        hulRight.2.1⟩


theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_minCandidate_bracket
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {z x y ur ul : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hzMin : ∀ q ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma',
      (rlc_ambientCrossingWalk gamma.1).support.idxOf z ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf q)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hxOrder : rlc_flipX (rlc_dualReflect x) ∈
      (right.map rlc_flipXLatticeHom).support)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hrightPrefix : RlcBookRightPrefixRankAt gamma right)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql) :
    rlc_dualReflect x = z ∧
      RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket
        gamma gamma' (z := z) (x := x) (y := y) flipLeft := by
  have hxEq :=
    rlc_twoChannelFullPhysical_rightContact_reflectedLeft_eq_of_minCandidate
      right qr hzCandidate hzMin hxPath hxOrder hrightPrefix hrow.1
        hrow.2.1.2.1
  exact ⟨hxEq,
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateBracket
      hfaith right flipLeft qr ql hzCandidate hxPath hyPath hxOrder hyOrder
        hrightPrefix hflipLeftRank hrow.1 hrow.2.2.1
          (Or.inl hrow.2.1) (Or.inr hrow.2.2.2)⟩


theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_maxCandidate_bracket
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {z x y ur ul : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hzMax : ∀ q ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma',
      (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hxOrder : rlc_flipX (rlc_dualReflect x) ∈
      (right.map rlc_flipXLatticeHom).support)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hrightPrefix : RlcBookRightPrefixRankAt gamma right)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql) :
    rlc_dualReflect y = rlc_flipX z ∧
      RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket
        gamma gamma' (z := z) (x := x) (y := y) flipLeft := by
  have hyEq :=
    rlc_twoChannelFullPhysical_leftContact_reflectedRight_eq_of_maxCandidate
      flipLeft ql hzCandidate hzMax hyPath hyOrder hflipLeftRank
        hrow.2.2.1 hrow.2.2.2.2.1
  exact ⟨hyEq,
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateBracket
      hfaith right flipLeft qr ql hzCandidate hxPath hyPath hxOrder hyOrder
        hrightPrefix hflipLeftRank hrow.1 hrow.2.2.1
          (Or.inl hrow.2.1) (Or.inr hrow.2.2.2)⟩


theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateProgress
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {z x y ur ul : Site 2}
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (hqrLeft : ∀ e ∈ qr.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
    (hxz : rlc_dualReflect x = z)
    (hqlRight : ∀ e ∈ ql.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
    (hulLoc :
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
          gamma gamma' (rlc_dualReflect ul) ∨
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' (rlc_dualReflect ul)) :
    (∀ e ∈ qr.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_reflectedPathEdges gamma'.1) ∧
      rlc_dualReflect x = z ∧
      (∀ e ∈ ql.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_reflectedPathEdges gamma.1) ∧
      ∃ r ∈ rlc_pathVertices gamma.1,
        rlc_dualReflect y = rlc_flipX r ∧
          r ∈ flipLeft.support ∧
          (r = z ∨
            (rlc_ambientCrossingWalk gamma.1).support.idxOf z <
              (rlc_ambientCrossingWalk gamma.1).support.idxOf r) := by
  have hulRight :=
    rlc_twoChannelFullPhysical_reflectedRightWalk_terminal_location
      hfaith ql (Or.inr hyPath) hqlRight hulLoc
  refine ⟨hqrLeft, hxz, hqlRight, ?_⟩
  exact rlc_twoChannelFullPhysical_leftContact_reflectedRight_candidateProgress
    flipLeft ql hzCandidate hyPath hyOrder hflipLeftRank hqlRight
      hulRight.2.1


theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_maxCandidate_contacts
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {z x y u ur ul : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hzCandidate : z ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma')
    (hzMax : ∀ q ∈
      rlc_bookOrderedIntersectionCandidateSet gamma gamma',
      (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤
        (rlc_ambientCrossingWalk gamma.1).support.idxOf z)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
    (hqrLeft : ∀ e ∈ qr.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
    (hxz : rlc_dualReflect x = z)
    (hqlRight : ∀ e ∈ ql.edges,
      Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
    (hulLoc :
      RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
          gamma gamma' (rlc_dualReflect ul) ∨
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' (rlc_dualReflect ul)) :
    (∀ e ∈ qr.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_reflectedPathEdges gamma'.1) ∧
      rlc_dualReflect x = z ∧
      (∀ e ∈ ql.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_reflectedPathEdges gamma.1) ∧
      rlc_dualReflect y = rlc_flipX z ∧
      (((x ∈ (rlc_bookShiftedOuterTrace gamma gamma'
              hzRight hzLeft).support ∧
            x ∈ (rlc_orderedContourArc c hx hy).support) ∧
          (y ∈ (rlc_bookShiftedOuterTrace gamma gamma'
              hzRight hzLeft).support ∧
            y ∈ (rlc_orderedContourArc c hx hy).support)) ∧
        x ≠ y) := by
  have hulRight :=
    rlc_twoChannelFullPhysical_reflectedRightWalk_terminal_location
      hfaith ql (Or.inr hyPath) hqlRight hulLoc
  have hyz :=
    rlc_twoChannelFullPhysical_leftContact_reflectedRight_eq_of_maxCandidate
      flipLeft ql hzCandidate hzMax hyPath hyOrder hflipLeftRank hqlRight
        hulRight.2.1
  refine ⟨hqrLeft, hxz, hqlRight, hyz, ?_⟩
  exact rlc_bookShiftedOuterTrace_forced_contacts_distinct
    hfaith c hx hy hzRight hzLeft hxz hyz


theorem rlc_twoChannelFullPhysical_twoArcWallFamilyTruthTable_factor
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {z x y ur ul : Site 2}
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur)
    (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul)
    (h : RlcTwoChannelFullPhysicalTwoArcWallFamilyTruthTable
      gamma gamma' omega flipLeft qr ql) :
    (((∀ e ∈ qr.edges,
          Sym2.map rlc_dualReflect e ∈
            rlc_reflectedPathEdges gamma'.1) ∧
        rlc_dualReflect x = z) ∨
      ((∀ e ∈ qr.edges,
          Sym2.map rlc_dualReflect e ∈
            rlc_reflectedPathEdges gamma.1) ∧
        rlc_dualReflect x = (gamma.1.1 : Site 2))) ∧
    (((∀ e ∈ ql.edges,
          Sym2.map rlc_dualReflect e ∈
            rlc_reflectedPathEdges gamma'.1) ∧
        rlc_dualReflect y = (gamma'.1.2.1 : Site 2)) ∨
      ((∀ e ∈ ql.edges,
          Sym2.map rlc_dualReflect e ∈
            rlc_reflectedPathEdges gamma.1) ∧
        ∃ r ∈ rlc_pathVertices gamma.1,
          rlc_dualReflect y = rlc_flipX r ∧ r ∈ flipLeft.support)) := by
  rcases h with h | h | h | h
  · exact ⟨Or.inl ⟨h.1, h.2.1⟩,
      Or.inl ⟨h.2.2.1, h.2.2.2⟩⟩
  · exact ⟨Or.inl ⟨h.1, h.2.1⟩,
      Or.inr ⟨h.2.2.1, h.2.2.2⟩⟩
  · exact ⟨Or.inr ⟨h.1, h.2.1⟩,
      Or.inl ⟨h.2.2.1, h.2.2.2⟩⟩
  · exact ⟨Or.inr ⟨h.1, h.2.1⟩,
      Or.inr ⟨h.2.2.1, h.2.2.2⟩⟩

theorem rlc_twoChannelFullPhysical_twoArcNoGood_tetheredWallOrientationCases
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {z x y u : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {hx : x ∈ c.support} {hy : y ∈ c.support}
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hxOrder : rlc_flipX (rlc_dualReflect x) ∈
      (right.map rlc_flipXLatticeHom).support)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
    (hfirst : ∀ w ∈ right.support,
      rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z)
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
        (∀ v ∈ W.support,
          v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) ∧
        RlcTwoChannelFullPhysicalTetheredWallOrientationAlternative
          gamma gamma' omega flipLeft qr ql := by
  classical
  obtain ⟨ur, vr, ul, vl, qr, ql, W, hurv, hulv, hne, hWBox⟩ :=
    rlc_twoChannelFullPhysical_twoArcNoGood_badTerminalWalk hbad
  refine ⟨ur, vr, ul, vl, qr, ql, W, hurv, hulv, hne, hWBox, ?_⟩
  by_cases hallR : ∀ e ∈ qr.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma'
  · by_cases hallL : ∀ e ∈ ql.edges,
        Sym2.map rlc_dualReflect e ∈
          rlc_connectorFourTraceEdges gamma gamma'
    · by_cases hurLoc :
          RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
              gamma gamma' (rlc_dualReflect ur) ∨
            RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
              gamma gamma' (rlc_dualReflect ur)
      · by_cases hulLoc :
            RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
                gamma gamma' (rlc_dualReflect ul) ∨
              RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
                gamma gamma' (rlc_dualReflect ul)
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hurLoc, hulLoc,
            rlc_twoChannelFullPhysical_twoArcWallFamilyTruthTable
              hfaith right flipLeft qr ql hxPath hyPath hxOrder hyOrder
                hfirst hallR hallL hurLoc hulLoc⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hulLoc)))
      · exact Or.inr (Or.inr (Or.inl hurLoc))
    · exact Or.inr (Or.inl hallL)
  · exact Or.inl hallR


end
end StatMech.Universality
