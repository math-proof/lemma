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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part85
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelFullPhysical_insideOutside_shiftedEndpointPlacement
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u p q : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOutside : q ∉
      rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
    RlcTwoChannelFullPhysicalShiftedEndpointPlacement
      gamma gamma' omega c p q := by
  have hregion :=
    rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle
      gamma gamma' omega c hcycle
  have hqOutside' : q ∉
      jec_leftRegion (c.mapLe (faceBoundaryGraph_le
        (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
    rwa [← hregion]
  by_cases hp : p ∈ c.support
  · exact Or.inr ⟨p, hp, Or.inl rfl⟩
  by_cases hpWest : (![p 0 - 1, p 1] : Site 2) ∈ c.support
  · exact Or.inr ⟨![p 0 - 1, p 1], hpWest, Or.inr (Or.inl rfl)⟩
  by_cases hpShift : phb_doubleDualShift p ∈ c.support
  · exact Or.inr ⟨phb_doubleDualShift p, hpShift,
      Or.inr (Or.inr (Or.inl rfl))⟩
  by_cases hq : q ∈ c.support
  · exact Or.inr ⟨q, hq, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  by_cases hqWest : (![q 0 - 1, q 1] : Site 2) ∈ c.support
  · exact Or.inr ⟨![q 0 - 1, q 1], hqWest,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  by_cases hqShift : phb_doubleDualShift q ∈ c.support
  · exact Or.inr ⟨phb_doubleDualShift q, hqShift,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩
  left
  constructor
  · rcases
        rlc_twoChannelFullPhysical_shiftedReach_inside_or_shortBoundaryContact
          c hcycle hpReach hpShift with hpInside | hpContact | hpWestContact
    · exact hpInside
    · exact False.elim (hp hpContact)
    · exact False.elim (hpWest hpWestContact)
  · intro hqShiftInside
    rcases rlc_twoChannelFullPhysical_shiftedExterior_shortBoundaryContact
        c hcycle hqOutside' hqShiftInside hqShift with
      hqContact | hqWestContact
    · exact hq hqContact
    · exact hqWest hqWestContact


theorem
    rlc_twoChannelFullPhysical_boundary_twoTerminal_shiftedEndpointPlacement
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u ur vr ul vl : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
    ∃ (p q p' q' : Site 2)
      (w : (hypercubicLattice 2).Walk p p'),
      sharedPrimalEdge ur vr = s(p, q) ∧
        sharedPrimalEdge ul vl = s(p', q') ∧
        (hypercubicLattice 2).Adj p q ∧
        (hypercubicLattice 2).Adj p' q' ∧
        p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧
        q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧
        (∀ z ∈ w.support,
          z ∈ rlc_twoChannelFullReachSet gamma gamma' omega) ∧
        RlcTwoChannelFullPhysicalShiftedEndpointPlacement
          gamma gamma' omega c p q ∧
        RlcTwoChannelFullPhysicalShiftedEndpointPlacement
          gamma gamma' omega c p' q' := by
  obtain ⟨p, q, p', q', w, hpq, hpq', hpqAdj, hpqAdj', hpReach,
      hpReach', hqOutside, hqOutside', hwReach⟩ :=
    rlc_twoChannelFullPhysical_boundary_insideSourceWalk
      gamma gamma' omega hurv hulv
  refine ⟨p, q, p', q', w, hpq, hpq', hpqAdj, hpqAdj', hpReach,
    hpReach', hqOutside, hqOutside', fun z hz ↦ (hwReach z hz).1, ?_, ?_⟩
  · exact
      rlc_twoChannelFullPhysical_insideOutside_shiftedEndpointPlacement
        c hcycle hpReach hqOutside
  · exact
      rlc_twoChannelFullPhysical_insideOutside_shiftedEndpointPlacement
        c hcycle hpReach' hqOutside'


theorem
    rlc_twoChannelFullPhysical_insideOutside_shiftedEdge_meetsChord_or_tetherContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a b p q : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOutside : q ∉
      rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
    (phb_doubleDualShift p ∈ H.support ∨
        phb_doubleDualShift q ∈ H.support) ∨
      ∃ z ∈ c.support,
        z = p ∨ z = ![p 0 - 1, p 1] ∨
          z = phb_doubleDualShift p ∨ z = q ∨
          z = ![q 0 - 1, q 1] ∨ z = phb_doubleDualShift q := by
  rcases
      rlc_twoChannelFullPhysical_insideOutside_shiftedEndpointPlacement
        c hcycle hpReach hqOutside with hplace | hcontact
  · have hpqShift : (hypercubicLattice 2).Adj
        (phb_doubleDualShift p) (phb_doubleDualShift q) :=
      phb_doubleDualShift_latAdj.mpr hpq
    have hmeet :=
      rlc_exteriorChord_inside_to_outside_path_meets_chord_or_cycleArc
        (faceBoundaryGraph_le
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega))
        c ha hb H hpqShift.toWalk hplace.1 hplace.2
    rcases hmeet with ⟨v, hvEdge, hvH | hvArc⟩ |
        ⟨v, hvEdge, hvH | hvArc⟩
    · have hv : v = phb_doubleDualShift p ∨
          v = phb_doubleDualShift q := by
        simpa [SimpleGraph.Adj.toWalk] using hvEdge
      exact Or.inl (hv.elim (fun h ↦ Or.inl (h ▸ hvH))
        (fun h ↦ Or.inr (h ▸ hvH)))
    · have hv : v = phb_doubleDualShift p ∨
          v = phb_doubleDualShift q := by
        simpa [SimpleGraph.Adj.toWalk] using hvEdge
      have hvCycle := rlc_orderedContourArc_support_subset c ha hb hvArc
      rcases hv with rfl | rfl
      · exact Or.inr ⟨phb_doubleDualShift p, hvCycle,
          Or.inr (Or.inr (Or.inl rfl))⟩
      · exact Or.inr ⟨phb_doubleDualShift q, hvCycle,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩
    · have hv : v = phb_doubleDualShift p ∨
          v = phb_doubleDualShift q := by
        simpa [SimpleGraph.Adj.toWalk] using hvEdge
      exact Or.inl (hv.elim (fun h ↦ Or.inl (h ▸ hvH))
        (fun h ↦ Or.inr (h ▸ hvH)))
    · have hv : v = phb_doubleDualShift p ∨
          v = phb_doubleDualShift q := by
        simpa [SimpleGraph.Adj.toWalk] using hvEdge
      have hvCycle :=
        rlc_complementaryContourArc_support_subset c ha hb hvArc
      rcases hv with rfl | rfl
      · exact Or.inr ⟨phb_doubleDualShift p, hvCycle,
          Or.inr (Or.inr (Or.inl rfl))⟩
      · exact Or.inr ⟨phb_doubleDualShift q, hvCycle,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩
  · exact Or.inr hcontact


theorem
    rlc_twoChannelFullPhysical_insideOutside_shiftedEdge_HinterT_or_tetherContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u a b p q s t : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (T : (hypercubicLattice 2).Walk s t)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOutside : q ∉
      rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hpT : phb_doubleDualShift p ∈ T.support)
    (hqT : phb_doubleDualShift q ∈ T.support) :
    (∃ v ∈ H.support, v ∈ T.support) ∨
      ∃ z ∈ c.support,
        z = p ∨ z = ![p 0 - 1, p 1] ∨
          z = phb_doubleDualShift p ∨ z = q ∨
          z = ![q 0 - 1, q 1] ∨ z = phb_doubleDualShift q := by
  rcases
      rlc_twoChannelFullPhysical_insideOutside_shiftedEdge_meetsChord_or_tetherContact
        c hcycle ha hb H hpq hpReach hqOutside with
    (hpH | hqH) | hcontact
  · exact Or.inl ⟨phb_doubleDualShift p, hpH, hpT⟩
  · exact Or.inl ⟨phb_doubleDualShift q, hqH, hqT⟩
  · exact Or.inr hcontact


theorem
    rlc_twoChannelFullPhysical_boundary_shiftedEndpoint_tetherContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u f g p q : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle)
    (hfg : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
    (hpq : sharedPrimalEdge f g = s(p, q))
    (hpqAdj : (hypercubicLattice 2).Adj p q) :
    ∃ z ∈ c.support,
      z = p ∨ z = ![p 0 - 1, p 1] ∨
        z = phb_doubleDualShift p ∨ z = q ∨
        z = ![q 0 - 1, q 1] ∨ z = phb_doubleDualShift q := by
  have huGraph : u ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support :=
    rlc_cycleVertex_mem_graphSupport c hcycle c.start_mem_support
  have hfgCycle : s(f, g) ∈ c.edges :=
    rlc_twoChannelFullPhysical_contactCycle_covers
      gamma gamma' omega c hcycle huGraph c.start_mem_support s(f, g)
        ((SimpleGraph.mem_edgeSet _).2 hfg)
  have hfCycle : f ∈ c.support :=
    c.fst_mem_support_of_mem_edges hfgCycle
  have hgCycle : g ∈ c.support :=
    c.snd_mem_support_of_mem_edges hfgCycle
  rcases rlc_doubleDualShift_endpoint_mem_boundaryEdge
      hfg.1 hpqAdj hpq with hpInc | hqInc
  · rw [Sym2.mem_iff] at hpInc
    rcases hpInc with hpF | hpG
    · exact ⟨phb_doubleDualShift p, hpF ▸ hfCycle,
        Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨phb_doubleDualShift p, hpG ▸ hgCycle,
        Or.inr (Or.inr (Or.inl rfl))⟩
  · rw [Sym2.mem_iff] at hqInc
    rcases hqInc with hqF | hqG
    · exact ⟨phb_doubleDualShift q, hqF ▸ hfCycle,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩
    · exact ⟨phb_doubleDualShift q, hqG ▸ hgCycle,
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowOne_exteriorIncidence_HinterT_or_tetherContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {x y ur vr ul vl p q p' q' : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne
      gamma gamma' omega qr ql)
    {u a b s t : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) (ha : a ∈ c.support) (hb : b ∈ c.support)
    (H : (hypercubicLattice 2).Walk a b)
    (T : (hypercubicLattice 2).Walk s t)
    (hpq : (hypercubicLattice 2).Adj p q)
    (hpq' : (hypercubicLattice 2).Adj p' q')
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOutside : q ∉
      rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hqOutside' : q' ∉
      rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hincR : phb_doubleDualShift p ∈ s(ur, vr) ∨
      phb_doubleDualShift q ∈ s(ur, vr))
    (hincL : phb_doubleDualShift p' ∈ s(ul, vl) ∨
      phb_doubleDualShift q' ∈ s(ul, vl))
    (hpT : phb_doubleDualShift p ∈ T.support)
    (hpT' : phb_doubleDualShift p' ∈ T.support)
    (hqT : phb_doubleDualShift q ∈ s(ur, vr) →
      phb_doubleDualShift q ∈ T.support)
    (hqT' : phb_doubleDualShift q' ∈ s(ul, vl) →
      phb_doubleDualShift q' ∈ T.support) :
    (phb_doubleDualShift p = vr ∧
        phb_doubleDualShift p' = vl) ∨
      (∃ v ∈ H.support, v ∈ T.support) ∨
      (∃ z ∈ c.support,
        z = p ∨ z = ![p 0 - 1, p 1] ∨
          z = phb_doubleDualShift p ∨ z = q ∨
          z = ![q 0 - 1, q 1] ∨ z = phb_doubleDualShift q) ∨
      ∃ z ∈ c.support,
        z = p' ∨ z = ![p' 0 - 1, p' 1] ∨
          z = phb_doubleDualShift p' ∨ z = q' ∨
          z = ![q' 0 - 1, q' 1] ∨ z = phb_doubleDualShift q' := by
  rcases
      rlc_twoChannelFullPhysical_wallFamilyRowOne_reachableIncidence_or_exterior
        hno hrow hpReach hpReach' hincR hincL with
    hmain | hright | hleft
  · exact Or.inl hmain
  · rcases
        rlc_twoChannelFullPhysical_insideOutside_shiftedEdge_HinterT_or_tetherContact
          c hcycle ha hb H T hpq hpReach hqOutside hpT (hqT hright) with
      hHT | hcontact
    · exact Or.inr (Or.inl hHT)
    · exact Or.inr (Or.inr (Or.inl hcontact))
  · rcases
        rlc_twoChannelFullPhysical_insideOutside_shiftedEdge_HinterT_or_tetherContact
          c hcycle ha hb H T hpq' hpReach' hqOutside' hpT' (hqT' hleft) with
      hHT | hcontact
    · exact Or.inr (Or.inl hHT)
    · exact Or.inr (Or.inr (Or.inr hcontact))

end
end StatMech.Universality
