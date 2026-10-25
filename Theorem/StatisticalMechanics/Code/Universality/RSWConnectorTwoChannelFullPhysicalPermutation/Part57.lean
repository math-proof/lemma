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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part57
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_boundaryIncidenceOrientation
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
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hincR : phb_doubleDualShift p ∈ s(ur, vr) ∨
      phb_doubleDualShift q ∈ s(ur, vr))
    (hincL : phb_doubleDualShift p' ∈ s(ul, vl) ∨
      phb_doubleDualShift q' ∈ s(ul, vl)) :
    (phb_doubleDualShift p = vr ∨
        phb_doubleDualShift q ∈ s(ur, vr)) ∧
      (phb_doubleDualShift p' ∈ s(ul, vl) ∨
        phb_doubleDualShift q' = vl) := by
  constructor
  · rcases hincR with hp | hq
    · rw [Sym2.mem_iff] at hp
      rcases hp with hp | hp
      · exact False.elim
          ((rlc_shiftedReach_ne_exclusiveReflectedLeftFace
            hno hpReach hrow.2.1) hp)
      · exact Or.inl hp
    · exact Or.inr hq
  · rcases hincL with hp' | hq'
    · exact Or.inl hp'
    · rw [Sym2.mem_iff] at hq'
      rcases hq' with hq' | hq'
      · exact False.elim
          ((rlc_shiftedExterior_ne_exclusiveReflectedRightFace
            hqOut' hrow.2.2.2) hq')
      · exact Or.inr hq'


theorem rlc_twoChannelFullPhysical_wallFamilyRowOne_boundaryIncidenceOrientation
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
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hincR : phb_doubleDualShift p ∈ s(ur, vr) ∨
      phb_doubleDualShift q ∈ s(ur, vr))
    (hincL : phb_doubleDualShift p' ∈ s(ul, vl) ∨
      phb_doubleDualShift q' ∈ s(ul, vl)) :
    (phb_doubleDualShift p = vr ∨
        phb_doubleDualShift q ∈ s(ur, vr)) ∧
      (phb_doubleDualShift p' = vl ∨
        phb_doubleDualShift q' ∈ s(ul, vl)) := by
  constructor
  · rcases hincR with hp | hq
    · rw [Sym2.mem_iff] at hp
      rcases hp with hp | hp
      · exact False.elim
          ((rlc_shiftedReach_ne_exclusiveReflectedLeftFace
            hno hpReach hrow.2.1) hp)
      · exact Or.inl hp
    · exact Or.inr hq
  · rcases hincL with hp' | hq'
    · rw [Sym2.mem_iff] at hp'
      rcases hp' with hp' | hp'
      · exact False.elim
          ((rlc_shiftedReach_ne_exclusiveReflectedLeftFace
            hno hpReach' hrow.2.2.2) hp')
      · exact Or.inl hp'
    · exact Or.inr hq'


theorem rlc_twoChannelFullPhysical_wallFamilyRowOne_boundaryIncidenceEndpointCases
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
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hincR : phb_doubleDualShift p ∈ s(ur, vr) ∨
      phb_doubleDualShift q ∈ s(ur, vr))
    (hincL : phb_doubleDualShift p' ∈ s(ul, vl) ∨
      phb_doubleDualShift q' ∈ s(ul, vl)) :
    (phb_doubleDualShift p = vr ∨
        phb_doubleDualShift q = ur ∨
        phb_doubleDualShift q = vr) ∧
      (phb_doubleDualShift p' = vl ∨
        phb_doubleDualShift q' = ul ∨
        phb_doubleDualShift q' = vl) := by
  obtain ⟨hR, hL⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowOne_boundaryIncidenceOrientation
      hno hrow hpReach hpReach' hincR hincL
  constructor
  · rcases hR with hp | hq
    · exact Or.inl hp
    · rw [Sym2.mem_iff] at hq
      rcases hq with hq | hq
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr hq)
  · rcases hL with hp' | hq'
    · exact Or.inl hp'
    · rw [Sym2.mem_iff] at hq'
      rcases hq' with hq' | hq'
      · exact Or.inr (Or.inl hq')
      · exact Or.inr (Or.inr hq')


theorem rlc_twoChannelFullPhysical_wallFamilyRowOne_reachableIncidence_or_exterior
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
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hincR : phb_doubleDualShift p ∈ s(ur, vr) ∨
      phb_doubleDualShift q ∈ s(ur, vr))
    (hincL : phb_doubleDualShift p' ∈ s(ul, vl) ∨
      phb_doubleDualShift q' ∈ s(ul, vl)) :
    (phb_doubleDualShift p = vr ∧
        phb_doubleDualShift p' = vl) ∨
      phb_doubleDualShift q ∈ s(ur, vr) ∨
      phb_doubleDualShift q' ∈ s(ul, vl) := by
  obtain ⟨hR, hL⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowOne_boundaryIncidenceOrientation
      hno hrow hpReach hpReach' hincR hincL
  rcases hR with hp | hq
  · rcases hL with hp' | hq'
    · exact Or.inl ⟨hp, hp'⟩
    · exact Or.inr (Or.inr hq')
  · exact Or.inr (Or.inl hq)


theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_boundaryIncidenceEndpointCases
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
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hincR : phb_doubleDualShift p ∈ s(ur, vr) ∨
      phb_doubleDualShift q ∈ s(ur, vr))
    (hincL : phb_doubleDualShift p' ∈ s(ul, vl) ∨
      phb_doubleDualShift q' ∈ s(ul, vl)) :
    (phb_doubleDualShift p = vr ∨
        phb_doubleDualShift q = ur ∨
        phb_doubleDualShift q = vr) ∧
      (phb_doubleDualShift p' = ul ∨
        phb_doubleDualShift p' = vl ∨
        phb_doubleDualShift q' = vl) := by
  obtain ⟨hR, hL⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_boundaryIncidenceOrientation
      hno hrow hpReach hqOut' hincR hincL
  constructor
  · rcases hR with hp | hq
    · exact Or.inl hp
    · rw [Sym2.mem_iff] at hq
      rcases hq with hq | hq
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr hq)
  · rcases hL with hp' | hq'
    · rw [Sym2.mem_iff] at hp'
      rcases hp' with hp' | hp'
      · exact Or.inl hp'
      · exact Or.inr (Or.inl hp')
    · exact Or.inr (Or.inr hq')


theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_droppedEndpointGeometry
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
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
    ((vr = ![ur 0 + 1, ur 1] ∧
        phb_doubleDualShift p = ![ur 0, ur 1 - 1] ∧
        phb_doubleDualShift q = ur) ∨
      (vr = ![ur 0 - 1, ur 1] ∧
        ((phb_doubleDualShift p = vr ∧
            phb_doubleDualShift q = ![ur 0 - 1, ur 1 - 1]) ∨
          (phb_doubleDualShift p = ![ur 0 - 1, ur 1 - 1] ∧
            phb_doubleDualShift q = vr))) ∨
      (vr = ![ur 0, ur 1 + 1] ∧
        phb_doubleDualShift p = ![ur 0 - 1, ur 1] ∧
        phb_doubleDualShift q = ur) ∨
      (vr = ![ur 0, ur 1 - 1] ∧
        ((phb_doubleDualShift p = vr ∧
            phb_doubleDualShift q = ![ur 0 - 1, ur 1 - 1]) ∨
          (phb_doubleDualShift p = ![ur 0 - 1, ur 1 - 1] ∧
            phb_doubleDualShift q = vr)))) ∧
    ((vl = ![ul 0 + 1, ul 1] ∧
        phb_doubleDualShift p' = ul ∧
        phb_doubleDualShift q' = ![ul 0, ul 1 - 1]) ∨
      (vl = ![ul 0 - 1, ul 1] ∧
        ((phb_doubleDualShift p' = vl ∧
            phb_doubleDualShift q' = ![ul 0 - 1, ul 1 - 1]) ∨
          (phb_doubleDualShift p' = ![ul 0 - 1, ul 1 - 1] ∧
            phb_doubleDualShift q' = vl))) ∨
      (vl = ![ul 0, ul 1 + 1] ∧
        phb_doubleDualShift p' = ul ∧
        phb_doubleDualShift q' = ![ul 0 - 1, ul 1]) ∨
      (vl = ![ul 0, ul 1 - 1] ∧
        ((phb_doubleDualShift p' = vl ∧
            phb_doubleDualShift q' = ![ul 0 - 1, ul 1 - 1]) ∨
          (phb_doubleDualShift p' = ![ul 0 - 1, ul 1 - 1] ∧
            phb_doubleDualShift q' = vl)))) := by
  have hpNe : phb_doubleDualShift p ≠ ur :=
    rlc_shiftedReach_ne_exclusiveReflectedLeftFace
      hno hpReach hrow.2.1
  have hqNe : phb_doubleDualShift q' ≠ ul :=
    rlc_shiftedExterior_ne_exclusiveReflectedRightFace
      hqOut' hrow.2.2.2
  have hgeomR :=
    rlc_sharedPrimalEdge_doubleDualShift_endpoint_geometry hurv hpq
  have hgeomL :=
    rlc_sharedPrimalEdge_doubleDualShift_endpoint_geometry hulv hpq'
  constructor
  · rcases hgeomR with ⟨hdir, hord⟩ | ⟨hdir, hord⟩ |
        ⟨hdir, hord⟩ | ⟨hdir, hord⟩
    · left
      rcases hord with hord | hord
      · exact False.elim (hpNe hord.1)
      · exact ⟨hdir, hord.1, hord.2⟩
    · right; left
      exact ⟨hdir, hord⟩
    · right; right; left
      rcases hord with hord | hord
      · exact False.elim (hpNe hord.1)
      · exact ⟨hdir, hord.1, hord.2⟩
    · right; right; right
      exact ⟨hdir, hord⟩
  · rcases hgeomL with ⟨hdir, hord⟩ | ⟨hdir, hord⟩ |
        ⟨hdir, hord⟩ | ⟨hdir, hord⟩
    · left
      rcases hord with hord | hord
      · exact ⟨hdir, hord.1, hord.2⟩
      · exact False.elim (hqNe hord.2)
    · right; left
      exact ⟨hdir, hord⟩
    · right; right; left
      rcases hord with hord | hord
      · exact ⟨hdir, hord.1, hord.2⟩
      · exact False.elim (hqNe hord.2)
    · right; right; right
      exact ⟨hdir, hord⟩


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_cases
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
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
    phb_doubleDualShift p = vr ∨ p = ur ∨ p = vr := by
  have hright :=
    (rlc_twoChannelFullPhysical_wallFamilyRowTwo_droppedEndpointGeometry
      hno hrow hurv hulv hpq hpq' hpReach hqOut').1
  rcases hright with ⟨hdir, hpShift, _hqShift⟩ |
      ⟨hdir, hord⟩ | ⟨hdir, hpShift, _hqShift⟩ |
      ⟨hdir, hord⟩
  · right; right
    have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
    have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
    have hd0 := congrArg (fun z : Site 2 => z 0) hdir
    have hd1 := congrArg (fun z : Site 2 => z 1) hdir
    simp [phb_doubleDualShift] at hp0 hp1 hd0 hd1
    funext i
    fin_cases i
    · change p 0 = vr 0
      omega
    · change p 1 = vr 1
      omega
  · rcases hord with ⟨hpShift, _hqShift⟩ |
        ⟨hpShift, _hqShift⟩
    · exact Or.inl hpShift
    · right; left
      have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      simp [phb_doubleDualShift] at hp0 hp1
      funext i
      fin_cases i
      · change p 0 = ur 0
        omega
      · change p 1 = ur 1
        omega
  · right; right
    have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
    have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
    have hd0 := congrArg (fun z : Site 2 => z 0) hdir
    have hd1 := congrArg (fun z : Site 2 => z 1) hdir
    simp [phb_doubleDualShift] at hp0 hp1 hd0 hd1
    funext i
    fin_cases i
    · change p 0 = vr 0
      omega
    · change p 1 = vr 1
      omega
  · rcases hord with ⟨hpShift, _hqShift⟩ |
        ⟨hpShift, _hqShift⟩
    · exact Or.inl hpShift
    · right; left
      have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      simp [phb_doubleDualShift] at hp0 hp1
      funext i
      fin_cases i
      · change p 0 = ur 0
        omega
      · change p 1 = ur 1
        omega


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_exact_cases
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
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
    (phb_doubleDualShift p = vr ∧ q = ur) ∨
      (p = ur ∧ phb_doubleDualShift q = vr) ∨
      (p = vr ∧ phb_doubleDualShift q = ur) := by
  have hright :=
    (rlc_twoChannelFullPhysical_wallFamilyRowTwo_droppedEndpointGeometry
      hno hrow hurv hulv hpq hpq' hpReach hqOut').1
  rcases hright with ⟨hdir, hpShift, hqShift⟩ |
      ⟨hdir, hord⟩ | ⟨hdir, hpShift, hqShift⟩ |
      ⟨hdir, hord⟩
  · right; right
    constructor
    · have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp [phb_doubleDualShift] at hp0 hp1 hd0 hd1
      funext i
      fin_cases i
      · change p 0 = vr 0
        omega
      · change p 1 = vr 1
        omega
    · exact hqShift
  · rcases hord with ⟨hpShift, hqShift⟩ | ⟨hpShift, hqShift⟩
    · left
      refine ⟨hpShift, ?_⟩
      have hq0 := congrArg (fun z : Site 2 => z 0) hqShift
      have hq1 := congrArg (fun z : Site 2 => z 1) hqShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp [phb_doubleDualShift] at hq0 hq1 hd0 hd1
      funext i
      fin_cases i
      · change q 0 = ur 0
        omega
      · change q 1 = ur 1
        omega
    · right; left
      refine ⟨?_, hqShift⟩
      have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      simp [phb_doubleDualShift] at hp0 hp1
      funext i
      fin_cases i
      · change p 0 = ur 0
        omega
      · change p 1 = ur 1
        omega
  · right; right
    constructor
    · have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp [phb_doubleDualShift] at hp0 hp1 hd0 hd1
      funext i
      fin_cases i
      · change p 0 = vr 0
        omega
      · change p 1 = vr 1
        omega
    · exact hqShift
  · rcases hord with ⟨hpShift, hqShift⟩ | ⟨hpShift, hqShift⟩
    · left
      refine ⟨hpShift, ?_⟩
      have hq0 := congrArg (fun z : Site 2 => z 0) hqShift
      have hq1 := congrArg (fun z : Site 2 => z 1) hqShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp [phb_doubleDualShift] at hq0 hq1 hd0 hd1
      funext i
      fin_cases i
      · change q 0 = ur 0
        omega
      · change q 1 = ur 1
        omega
    · right; left
      refine ⟨?_, hqShift⟩
      have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      simp [phb_doubleDualShift] at hp0 hp1
      funext i
      fin_cases i
      · change p 0 = ur 0
        omega
      · change p 1 = ur 1
        omega


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_shiftedExteriorAtUr_mem_leftTrace
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur ul q : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hqShift : phb_doubleDualShift q = ur) :
    q ∈ rlc_pathVertices gamma'.1 := by
  obtain ⟨w, hwLeft, hur⟩ := hrow.2.1.2.1
  have hqFlip : q = rlc_flipX (rlc_dualReflect ur) :=
    (rlc_doubleDualShift_eq_dualReflect_symm_iff
      q (rlc_dualReflect ur)).1 (by
        simpa using hqShift)
  have hq : q = w := by
    rw [hqFlip, hur]
    exact rlc_flipX_involutive w
  simpa [hq] using hwLeft


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_exteriorNeighbour_of_p_eq_ur
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
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hpUr : p = ur) :
    ∃ w ∈ rlc_pathVertices gamma'.1,
      q = ![w 0 - 1, w 1] ∨ q = ![w 0, w 1 - 1] := by
  obtain ⟨w, hwLeft, hur⟩ := hrow.2.1.2.1
  refine ⟨w, hwLeft, ?_⟩
  have hright :=
    (rlc_twoChannelFullPhysical_wallFamilyRowTwo_droppedEndpointGeometry
      hno hrow hurv hulv hpq hpq' hpReach hqOut').1
  rcases hright with ⟨hdir, hpShift, _hqShift⟩ |
      ⟨hdir, hord⟩ | ⟨hdir, hpShift, _hqShift⟩ |
      ⟨hdir, hord⟩
  · exfalso
    have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
    have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
    have hd0 := congrArg (fun z : Site 2 => z 0) hdir
    have hd1 := congrArg (fun z : Site 2 => z 1) hdir
    simp [hpUr, phb_doubleDualShift] at hp0 hp1 hd0 hd1
  · rcases hord with ⟨hpShift, hqShift⟩ | ⟨_hpShift, hqShift⟩
    · exfalso
      have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp [hpUr, phb_doubleDualShift] at hp0 hp1 hd0 hd1
      omega
    · left
      have hq0 := congrArg (fun z : Site 2 => z 0) hqShift
      have hq1 := congrArg (fun z : Site 2 => z 1) hqShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      have hu0 := congrArg (fun z : Site 2 => z 0) hur
      have hu1 := congrArg (fun z : Site 2 => z 1) hur
      simp [phb_doubleDualShift, rlc_dualReflect, rlc_dualReflectFun,
        rlc_flipX, rlc_flipXFun] at hq0 hq1 hd0 hd1 hu0 hu1
      funext i
      fin_cases i
      · simp
        omega
      · simp
        omega
  · exfalso
    have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
    have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
    have hd0 := congrArg (fun z : Site 2 => z 0) hdir
    have hd1 := congrArg (fun z : Site 2 => z 1) hdir
    simp [hpUr, phb_doubleDualShift] at hp0 hp1 hd0 hd1
  · rcases hord with ⟨hpShift, hqShift⟩ | ⟨_hpShift, hqShift⟩
    · exfalso
      have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp [hpUr, phb_doubleDualShift] at hp0 hp1 hd0 hd1
      omega
    · right
      have hq0 := congrArg (fun z : Site 2 => z 0) hqShift
      have hq1 := congrArg (fun z : Site 2 => z 1) hqShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      have hu0 := congrArg (fun z : Site 2 => z 0) hur
      have hu1 := congrArg (fun z : Site 2 => z 1) hur
      simp [phb_doubleDualShift, rlc_dualReflect, rlc_dualReflectFun,
        rlc_flipX, rlc_flipXFun] at hq0 hq1 hd0 hd1 hu0 hu1
      funext i
      fin_cases i
      · simp
        omega
      · simp
        omega


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_ur_sourceCarrier_or_location
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {x y ur vr ul p q : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hpUr : p = ur) :
    RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        gamma gamma' p ∨
      (p 0 = -2 * n ∨ p 0 = 2 * n ∨
        p 1 = -n ∨ p 1 = n) := by
  have hpNeg : p 0 < 0 := by
    have hpos := hrow.2.1.1
    simp [rlc_dualReflect, rlc_dualReflectFun] at hpos
    rw [hpUr]
    omega
  have hpBox := rlc_twoChannelFullReachSet_subset_box
    gamma gamma' omega hpReach
  by_cases hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧
      -n < p 1 ∧ p 1 < n
  · have hqBox : q ∈ rlc_connectorBox n := by
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
      rw [mem_rect]
      rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpqAdj
      omega
    by_cases hpBarrier : p ∈ rlc_connectorBarrier gamma gamma'
    · rcases rlc_connectorBarrier_original_or_exclusive_strict_reflected
          gamma gamma' hpBarrier with
        hpRight | hpLeft | hpFlipLeft | hpFlipRight
      · have hpRect := rlc_pathVertex_mem_rect gamma.1 hpRight
        rw [mem_rect] at hpRect
        omega
      · exact False.elim
          ((rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
            gamma gamma' omega hno hpLeft) hpReach)
      · exact False.elim (by
          have hpPos := hpFlipLeft.1
          omega)
      · exact Or.inr (Or.inl hpFlipRight)
    · left
      apply rlc_twoChannelFullPhysical_sourceCarrier_of_planar
        gamma gamma' omega hurv
      rw [hpq]
      exact
        rlc_twoChannelFullPhysical_reachable_interior_nonbarrier_edge_planar
          gamma gamma' omega hpReach hpInterior hpBarrier hqBox hpqAdj
  · right; right
    rw [mem_rect] at hpBox
    push Not at hpInterior
    omega


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_q_eq_ur_sourceCarrier_or_location
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {x y ur vr ul p q : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqUr : q = ur) :
    RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        gamma gamma' p ∨
      (p 0 = -2 * n ∨ p 0 = 2 * n ∨
        p 1 = -n ∨ p 1 = n) := by
  have hqNeg : q 0 + 1 < 0 := by
    have hpos := hrow.2.1.1
    simp [rlc_dualReflect, rlc_dualReflectFun] at hpos
    rw [hqUr]
    omega
  have hpNeg : p 0 < 0 := by
    have hpqCoord := hpqAdj
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpqCoord
    omega
  have hpBox := rlc_twoChannelFullReachSet_subset_box
    gamma gamma' omega hpReach
  by_cases hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧
      -n < p 1 ∧ p 1 < n
  · have hqBox : q ∈ rlc_connectorBox n := by
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
      rw [mem_rect]
      have hpqCoord := hpqAdj
      rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpqCoord
      omega
    by_cases hpBarrier : p ∈ rlc_connectorBarrier gamma gamma'
    · rcases rlc_connectorBarrier_original_or_exclusive_strict_reflected
          gamma gamma' hpBarrier with
        hpRight | hpLeft | hpFlipLeft | hpFlipRight
      · have hpRect := rlc_pathVertex_mem_rect gamma.1 hpRight
        rw [mem_rect] at hpRect
        omega
      · exact False.elim
          ((rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
            gamma gamma' omega hno hpLeft) hpReach)
      · exact False.elim (by
          have hpPos := hpFlipLeft.1
          omega)
      · exact Or.inr (Or.inl hpFlipRight)
    · left
      apply rlc_twoChannelFullPhysical_sourceCarrier_of_planar
        gamma gamma' omega hurv
      rw [hpq]
      exact
        rlc_twoChannelFullPhysical_reachable_interior_nonbarrier_edge_planar
          gamma gamma' omega hpReach hpInterior hpBarrier hqBox hpqAdj
  · right; right
    rw [mem_rect] at hpBox
    push Not at hpInterior
    omega


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceEdge_traceGap
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
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hpVr : p = vr) :
    ∃ w ∈ rlc_pathVertices gamma'.1, q = w ∧
      ((sharedPrimalEdge ur vr =
          s((![w 0, w 1 - 1] : Site 2), w) ∧
        s((![w 0, w 1 - 1] : Site 2), w) ∉
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∨
       (sharedPrimalEdge ur vr =
          s((![w 0 - 1, w 1] : Site 2), w) ∧
        s((![w 0 - 1, w 1] : Site 2), w) ∉
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)) := by
  obtain ⟨w, hwLeft, hur⟩ := hrow.2.1.2.1
  have hpreimage := rlc_twoChannelFullFilledBoundary_preimage_not_exposed
    gamma gamma' omega hurv
  have hright :=
    (rlc_twoChannelFullPhysical_wallFamilyRowTwo_droppedEndpointGeometry
      hno hrow hurv.1 hulv hpq hpq' hpReach hqOut').1
  rcases hright with ⟨hdir, _hpShift, hqShift⟩ |
      ⟨hdir, hord⟩ | ⟨hdir, _hpShift, hqShift⟩ |
      ⟨hdir, hord⟩
  · have hqw : q = w := by
      have hq0 := congrArg (fun z : Site 2 => z 0) hqShift
      have hq1 := congrArg (fun z : Site 2 => z 1) hqShift
      have hu0 := congrArg (fun z : Site 2 => z 0) hur
      have hu1 := congrArg (fun z : Site 2 => z 1) hur
      simp [phb_doubleDualShift, rlc_dualReflect, rlc_dualReflectFun,
        rlc_flipX, rlc_flipXFun] at hq0 hq1 hu0 hu1
      funext i
      fin_cases i <;> simp <;> omega
    refine ⟨w, hwLeft, hqw, Or.inl ?_⟩
    have hsource : sharedPrimalEdge ur vr =
        s((![w 0, w 1 - 1] : Site 2), w) := by
      rw [hdir]
      exact rlc_reflectedHit_sharedPrimalEdge_right hur
    exact ⟨hsource, fun hedge => hpreimage (by
      rw [hsource]
      exact hedge)⟩
  · rcases hord with ⟨hpShift, _hqShift⟩ | ⟨hpShift, _hqShift⟩
    · exfalso
      have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp [hpVr, phb_doubleDualShift] at hp0 hp1 hd0 hd1
    · exfalso
      have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp [hpVr, phb_doubleDualShift] at hp0 hp1 hd0 hd1
      omega
  · have hqw : q = w := by
      have hq0 := congrArg (fun z : Site 2 => z 0) hqShift
      have hq1 := congrArg (fun z : Site 2 => z 1) hqShift
      have hu0 := congrArg (fun z : Site 2 => z 0) hur
      have hu1 := congrArg (fun z : Site 2 => z 1) hur
      simp [phb_doubleDualShift, rlc_dualReflect, rlc_dualReflectFun,
        rlc_flipX, rlc_flipXFun] at hq0 hq1 hu0 hu1
      funext i
      fin_cases i <;> simp <;> omega
    refine ⟨w, hwLeft, hqw, Or.inr ?_⟩
    have hsource : sharedPrimalEdge ur vr =
        s((![w 0 - 1, w 1] : Site 2), w) := by
      rw [hdir]
      exact rlc_reflectedHit_sharedPrimalEdge_top hur
    exact ⟨hsource, fun hedge => hpreimage (by
      rw [hsource]
      exact hedge)⟩
  · rcases hord with ⟨hpShift, _hqShift⟩ | ⟨hpShift, _hqShift⟩
    · exfalso
      have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp [hpVr, phb_doubleDualShift] at hp0 hp1 hd0 hd1
    · exfalso
      have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp [hpVr, phb_doubleDualShift] at hp0 hp1 hd0 hd1
      omega


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceCarrier_or_location
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
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hpVr : p = vr) :
    RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        gamma gamma' p ∨
      (p 0 = -2 * n ∨ p 0 = 2 * n ∨
        p 1 = -n ∨ p 1 = n) := by
  have hpNeg : p 0 < 0 := by
    have hpos := hrow.2.1.1
    simp [rlc_dualReflect, rlc_dualReflectFun] at hpos
    have huv := hurv.1
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at huv
    rw [hpVr]
    omega
  have hpBox := rlc_twoChannelFullReachSet_subset_box
    gamma gamma' omega hpReach
  by_cases hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧
      -n < p 1 ∧ p 1 < n
  · have hqBox : q ∈ rlc_connectorBox n := by
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
      rw [mem_rect]
      have hpqCoord := hpqAdj
      rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpqCoord
      omega
    by_cases hpBarrier : p ∈ rlc_connectorBarrier gamma gamma'
    · rcases rlc_connectorBarrier_original_or_exclusive_strict_reflected
          gamma gamma' hpBarrier with
        hpRight | hpLeft | hpFlipLeft | hpFlipRight
      · have hpRect := rlc_pathVertex_mem_rect gamma.1 hpRight
        rw [mem_rect] at hpRect
        omega
      · exact False.elim
          ((rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
            gamma gamma' omega hno hpLeft) hpReach)
      · exact False.elim (by
          have hpPos := hpFlipLeft.1
          omega)
      · exact Or.inr (Or.inl hpFlipRight)
    · left
      apply rlc_twoChannelFullPhysical_sourceCarrier_of_planar
        gamma gamma' omega hurv
      rw [hpq]
      exact
        rlc_twoChannelFullPhysical_reachable_interior_nonbarrier_edge_planar
          gamma gamma' omega hpReach hpInterior hpBarrier hqBox hpqAdj
  · right; right
    rw [mem_rect] at hpBox
    push Not at hpInterior
    omega


theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_sourceCarrier_or_location
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
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
    RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨
      RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
        gamma gamma' p ∨
      (p 0 = -2 * n ∨ p 0 = 2 * n ∨
        p 1 = -n ∨ p 1 = n) := by
  rcases
      rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_exact_cases
        hno hrow hurv.1 hulv hpq hpq' hpReach hqOut' with
    hqUr | hpUr | hpVr
  · exact
      rlc_twoChannelFullPhysical_wallFamilyRowTwo_q_eq_ur_sourceCarrier_or_location
        hno hrow hurv hpq hpqAdj hpReach hqUr.2
  · exact
      rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_ur_sourceCarrier_or_location
        hno hrow hurv hpq hpqAdj hpReach hpUr.1
  · exact
      rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceCarrier_or_location
        hno hrow hurv hulv hpq hpq' hpqAdj hpReach hqOut' hpVr.1


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceCarrier_or_nonwall_location
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {x y ur vr ul vl p q p' q' : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hpVr : p = vr) :
    RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨
      ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
          gamma gamma' p ∨
        p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧
       sharedPrimalEdge ur vr ∉
          rlc_connectorFourTraceEdges gamma gamma') := by
  have hpNeg : p 0 < 0 := by
    have hpos := hrow.2.1.1
    simp [rlc_dualReflect, rlc_dualReflectFun] at hpos
    have huv := hurv.1
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at huv
    rw [hpVr]
    omega
  rcases
      rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceCarrier_or_location
        hno hrow hurv hulv hpq hpq' hpqAdj hpReach hqOut' hpVr with
    hsource | hpExclusive | hpBoundary
  · exact Or.inl hsource
  · by_cases hwall : sharedPrimalEdge ur vr ∈
        rlc_connectorFourTraceEdges gamma gamma'
    · left
      exact rlc_twoChannelFullPhysical_sourceCarrier_of_planar
        gamma gamma' omega hurv (by
          rw [rlc_connectorCentralFacePlanarEdges]
          exact Finset.mem_union_right _ hwall)
    · exact Or.inr ⟨Or.inl hpExclusive, hwall⟩
  · have hpBoundary' : p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n := by
      rcases hpBoundary with hpLeft | hpRight | hpBottom | hpTop
      · exact Or.inl hpLeft
      · exact False.elim (by omega)
      · exact Or.inr (Or.inl hpBottom)
      · exact Or.inr (Or.inr hpTop)
    by_cases hwall : sharedPrimalEdge ur vr ∈
        rlc_connectorFourTraceEdges gamma gamma'
    · left
      exact rlc_twoChannelFullPhysical_sourceCarrier_of_planar
        gamma gamma' omega hurv (by
          rw [rlc_connectorCentralFacePlanarEdges]
          exact Finset.mem_union_right _ hwall)
    · exact Or.inr ⟨Or.inr hpBoundary', hwall⟩


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourcePrefix_capstone
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {x y ur vr ul vl p q p' q' : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hpVr : p = vr) :
    RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨
      (p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∨
      ∃ z : Site 2,
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
            gamma gamma' p ∧
          sharedPrimalEdge ur vr ∉
            rlc_connectorFourTraceEdges gamma gamma' ∧
          (hypercubicLattice 2).Adj p z ∧
          rlc_twoChannelFullAmbientConfig gamma gamma' omega
              s(p, z) = true ∧
          (s(p, z) ∈ rlc_connectorFourTraceEdges gamma gamma' ∨
            (z 0 + q 0 = 2 * p 0 ∧
              z 1 + q 1 = 2 * p 1)) := by
  rcases
      rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceCarrier_or_nonwall_location
        hn hno hrow hurv hulv hpq hpq' hpqAdj hpReach hqOut' hpVr with
    hsource | ⟨hpPlace, hcurrentNonwall⟩
  · exact Or.inl hsource
  rcases hpPlace with hpExclusive | hpBoundary
  · by_cases hpOnBoundary : p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n
    · exact Or.inr (Or.inl hpOnBoundary)
    · have hpBox := rlc_twoChannelFullReachSet_subset_box
        gamma gamma' omega hpReach
      have hpNeg := hpExclusive.1
      have hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧
          -n < p 1 ∧ p 1 < n := by
        rw [mem_rect] at hpBox
        push Not at hpOnBoundary
        omega
      have hqBox : q ∈ rlc_connectorBox n := by
        simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
        rw [mem_rect]
        have hpqCoord := hpqAdj
        rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpqCoord
        omega
      have hpAnchor : p ≠ (rlc_connectorRightAnchor gamma : Site 2) := by
        intro hpEq
        have haxis : ((rlc_connectorRightAnchor gamma :
            RlcConnectorVertex n) : Site 2) 0 = 0 := by
          exact gamma.1.1.2.2
        rw [hpEq] at hpNeg
        omega
      have hpqClosed : rlc_twoChannelFullAmbientConfig gamma gamma' omega
          s(p, q) = false := by
        have hopen := rlc_twoChannelFullFilledBoundary_le_openFaceDual
          gamma gamma' omega hurv
        rw [openSubgraph_adj] at hopen
        have h := hopen.2
        rw [fci_faceDualConfig,
          fci_faceEdgeEquiv_mk_of_adj hurv.1, hpq] at h
        simpa using h
      rcases
          rlc_twoChannelFullPhysical_reachable_interior_edge_planar_or_last_wall_or_opposite
            gamma gamma' omega hpReach hpInterior hqBox hpqAdj
              hpAnchor hpqClosed with
        hplanar | ⟨z, hpzAdj, hpzOpen, hpzPlace⟩
      · left
        exact rlc_twoChannelFullPhysical_sourceCarrier_of_planar
          gamma gamma' omega hurv (by simpa [hpq] using hplanar)
      · exact Or.inr (Or.inr
          ⟨z, hpExclusive, hcurrentNonwall, hpzAdj, hpzOpen, hpzPlace⟩)
  · exact Or.inr (Or.inl hpBoundary)


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceTraceCross_capstone
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {x y ur vr ul vl p q p' q' : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hpVr : p = vr) :
    RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨
      (p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∨
      ∃ z : Site 2,
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
            gamma gamma' p ∧
          sharedPrimalEdge ur vr ∉
            rlc_connectorFourTraceEdges gamma gamma' ∧
          (hypercubicLattice 2).Adj p z ∧
          rlc_twoChannelFullAmbientConfig gamma gamma' omega
              s(p, z) = true ∧
          (s(p, z) ∈ rlc_reflectedPathEdges gamma.1 ∨
            (s(p, z) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧
              z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1 ∧
              ∀ y : Site 2,
                (hypercubicLattice 2).Adj p y → y ≠ z → y ≠ q →
                  s(p, y) ∈ rlc_reflectedPathEdges gamma.1)) := by
  rcases
      rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceCarrier_or_nonwall_location
        hn hno hrow hurv hulv hpq hpq' hpqAdj hpReach hqOut' hpVr with
    hsource | ⟨hpPlace, hcurrentNonwall⟩
  · exact Or.inl hsource
  rcases hpPlace with hpExclusive | hpBoundary
  · by_cases hpOnBoundary : p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n
    · exact Or.inr (Or.inl hpOnBoundary)
    · have hpBox := rlc_twoChannelFullReachSet_subset_box
        gamma gamma' omega hpReach
      have hpNeg := hpExclusive.1
      have hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧
          -n < p 1 ∧ p 1 < n := by
        rw [mem_rect] at hpBox
        push Not at hpOnBoundary
        omega
      have hqBox : q ∈ rlc_connectorBox n := by
        simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
        rw [mem_rect]
        have hpqCoord := hpqAdj
        rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpqCoord
        omega
      have hpAnchor : p ≠ (rlc_connectorRightAnchor gamma : Site 2) := by
        intro hpEq
        have haxis : ((rlc_connectorRightAnchor gamma :
            RlcConnectorVertex n) : Site 2) 0 = 0 := gamma.1.1.2.2
        rw [hpEq] at hpNeg
        omega
      have hpqClosed : rlc_twoChannelFullAmbientConfig gamma gamma' omega
          s(p, q) = false := by
        have hopen := rlc_twoChannelFullFilledBoundary_le_openFaceDual
          gamma gamma' omega hurv
        rw [openSubgraph_adj] at hopen
        have h := hopen.2
        rw [fci_faceDualConfig,
          fci_faceEdgeEquiv_mk_of_adj hurv.1, hpq] at h
        simpa using h
      rcases
          rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedRight_edge_planar_or_traceCross
            gamma gamma' omega hpReach hpInterior hpExclusive hqBox hpqAdj
              hpAnchor hpqClosed with
        hplanar | ⟨z, hpzAdj, hpzOpen, hpzTrace⟩
      · left
        exact rlc_twoChannelFullPhysical_sourceCarrier_of_planar
          gamma gamma' omega hurv (by simpa [hpq] using hplanar)
      · exact Or.inr (Or.inr
          ⟨z, hpExclusive, hcurrentNonwall, hpzAdj, hpzOpen, hpzTrace⟩)
  · exact Or.inr (Or.inl hpBoundary)


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceCoordinate_capstone
    {n : Int} (hn : 0 < n)
    {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {x y ur vr ul vl p q p' q' : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpqAdj : (hypercubicLattice 2).Adj p q)
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hpVr : p = vr) :
    RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨
      (p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∨
      ∃ z : Site 2,
        RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
            gamma gamma' p ∧
          sharedPrimalEdge ur vr ∉
            rlc_connectorFourTraceEdges gamma gamma' ∧
          (hypercubicLattice 2).Adj p z ∧
          rlc_twoChannelFullAmbientConfig gamma gamma' omega
              s(p, z) = true ∧
          ((∃ source :
              (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
              source.1.map Subtype.val = s(p, z)) ∨
            (s(p, z) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧
              z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1 ∧
              ∀ y : Site 2,
                (hypercubicLattice 2).Adj p y → y ≠ z → y ≠ q →
                  ∃ source :
                    (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
                    source.1.map Subtype.val = s(p, y))) := by
  rcases
      rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceTraceCross_capstone
        hn hno hrow hurv hulv hpq hpq' hpqAdj hpReach hqOut' hpVr with
    hsource | hpBoundary | ⟨z, hpExclusive, hcurrentNonwall,
      hpzAdj, hpzOpen, hpzTrace | hpzCross⟩
  · exact Or.inl hsource
  · exact Or.inr (Or.inl hpBoundary)
  · exact Or.inr (Or.inr ⟨z, hpExclusive, hcurrentNonwall,
      hpzAdj, hpzOpen, Or.inl
        (rlc_twoChannelFullPhysical_exclusiveReflectedRightEdge_sourceWitness
          gamma gamma' hpExclusive hpzAdj hpzTrace)⟩)
  · refine Or.inr (Or.inr ⟨z, hpExclusive, hcurrentNonwall,
      hpzAdj, hpzOpen, Or.inr
        ⟨hpzCross.1, hpzCross.2.1, hpzCross.2.2.1, ?_⟩⟩)
    intro y hpyAdj hyz hyq
    exact
      rlc_twoChannelFullPhysical_exclusiveReflectedRightEdge_sourceWitness
        gamma gamma' hpExclusive hpyAdj
          (hpzCross.2.2.2 y hpyAdj hyz hyq)


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_cycleContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {x y ur vr ul vl p q p' q' u : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hurC : ur ∈ c.support) (hvrC : vr ∈ c.support) :
    phb_doubleDualShift p ∈ c.support ∨ p ∈ c.support := by
  rcases
      rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_cases
        hno hrow hurv hulv hpq hpq' hpReach hqOut' with
      hpShift | hpUr | hpVr
  · exact Or.inl (hpShift.symm ▸ hvrC)
  · exact Or.inr (hpUr.symm ▸ hurC)
  · exact Or.inr (hpVr.symm ▸ hvrC)


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_noncarrierEdge
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {x y ur vr ul vl p q p' q' u : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {hx : x ∈ c.support} {hy : y ∈ c.support}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {rr : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hbad : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
      gamma gamma' ur vr)
    (hdecR : rlc_orderedContourArc c hx hy =
      (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hurv rr)) :
    (∃ w : Site 2,
        (hypercubicLattice 2).Adj (phb_doubleDualShift p) w ∧
          s(phb_doubleDualShift p, w) ∈
            (rlc_orderedContourArc c hx hy).edges ∧
          ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
            gamma gamma' (phb_doubleDualShift p) w) ∨
      ∃ w : Site 2,
        (hypercubicLattice 2).Adj p w ∧
          s(p, w) ∈ (rlc_orderedContourArc c hx hy).edges ∧
          ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
            gamma gamma' p w := by
  have hedge : s(ur, vr) ∈
      (rlc_orderedContourArc c hx hy).edges := by
    rw [hdecR, SimpleGraph.Walk.edges_append]
    simp
  have hbadRev :
      ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
        gamma gamma' vr ur := by
    intro hcarrier
    exact hbad
      ((rlc_twoChannelFullPhysical_boundaryCarrierGeometry_comm
        gamma gamma' hurv.1).2 hcarrier)
  rcases
      rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_exact_cases
        hno hrow hurv.1 hulv hpq hpq' hpReach hqOut' with
    hshift | hpUr | hpVr
  · left
    refine ⟨ur, ?_, ?_, ?_⟩
    · simpa [hshift.1] using hurv.1.symm
    · simpa [hshift.1, Sym2.eq_swap] using hedge
    · simpa [hshift.1] using hbadRev
  · right
    refine ⟨vr, ?_, ?_, ?_⟩
    · simpa [hpUr.1] using hurv.1
    · simpa [hpUr.1] using hedge
    · simpa [hpUr.1] using hbad
  · right
    refine ⟨ur, ?_, ?_, ?_⟩
    · simpa [hpVr.1] using hurv.1.symm
    · simpa [hpVr.1, Sym2.eq_swap] using hedge
    · simpa [hpVr.1] using hbadRev


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_leftDroppedEndpoint_cases
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
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
    phb_doubleDualShift p' = ul ∨
      phb_doubleDualShift p' = vl ∨ p' = ul := by
  have hleft :=
    (rlc_twoChannelFullPhysical_wallFamilyRowTwo_droppedEndpointGeometry
      hno hrow hurv hulv hpq hpq' hpReach hqOut').2
  rcases hleft with ⟨_hdir, hpShift, _hqShift⟩ |
      ⟨hdir, hord⟩ | ⟨_hdir, hpShift, _hqShift⟩ |
      ⟨hdir, hord⟩
  · exact Or.inl hpShift
  · rcases hord with ⟨hpShift, _hqShift⟩ |
        ⟨hpShift, _hqShift⟩
    · exact Or.inr (Or.inl hpShift)
    · right; right
      have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp [phb_doubleDualShift] at hp0 hp1 hd0 hd1
      funext i
      fin_cases i <;> simp <;> omega
  · exact Or.inl hpShift
  · rcases hord with ⟨hpShift, _hqShift⟩ |
        ⟨hpShift, _hqShift⟩
    · exact Or.inr (Or.inl hpShift)
    · right; right
      have hp0 := congrArg (fun z : Site 2 => z 0) hpShift
      have hp1 := congrArg (fun z : Site 2 => z 1) hpShift
      have hd0 := congrArg (fun z : Site 2 => z 0) hdir
      have hd1 := congrArg (fun z : Site 2 => z 1) hdir
      simp [phb_doubleDualShift] at hp0 hp1 hd0 hd1
      funext i
      fin_cases i <;> simp <;> omega


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_leftDroppedEndpoint_noncarrierEdge
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {x y ur vr ul vl p q p' q' u : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {hx : x ∈ c.support} {hy : y ∈ c.support}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    {rl : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hbad : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
      gamma gamma' ul vl)
    (hdecL : (rlc_complementaryContourArc c hx hy).reverse =
      (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hulv rl)) :
    (∃ w : Site 2,
        (hypercubicLattice 2).Adj (phb_doubleDualShift p') w ∧
          s(phb_doubleDualShift p', w) ∈
            (rlc_complementaryContourArc c hx hy).edges ∧
          ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
            gamma gamma' (phb_doubleDualShift p') w) ∨
      ∃ w : Site 2,
        (hypercubicLattice 2).Adj p' w ∧
          s(p', w) ∈ (rlc_complementaryContourArc c hx hy).edges ∧
          ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
            gamma gamma' p' w := by
  have hedgeReverse : s(ul, vl) ∈
      (rlc_complementaryContourArc c hx hy).reverse.edges := by
    rw [hdecL, SimpleGraph.Walk.edges_append]
    simp
  have hedge : s(ul, vl) ∈
      (rlc_complementaryContourArc c hx hy).edges := by
    simpa [SimpleGraph.Walk.edges_reverse] using hedgeReverse
  have hbadRev :
      ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
        gamma gamma' vl ul := by
    intro hcarrier
    exact hbad
      ((rlc_twoChannelFullPhysical_boundaryCarrierGeometry_comm
        gamma gamma' hulv.1).2 hcarrier)
  rcases
      rlc_twoChannelFullPhysical_wallFamilyRowTwo_leftDroppedEndpoint_cases
        hno hrow hurv hulv.1 hpq hpq' hpReach hqOut' with
    hpUl | hpVl | hpUl
  · left
    refine ⟨vl, ?_, ?_, ?_⟩
    · simpa [hpUl] using hulv.1
    · simpa [hpUl] using hedge
    · simpa [hpUl] using hbad
  · left
    refine ⟨ul, ?_, ?_, ?_⟩
    · simpa [hpVl] using hulv.1.symm
    · simpa [hpVl, Sym2.eq_swap] using hedge
    · simpa [hpVl] using hbadRev
  · right
    refine ⟨vl, ?_, ?_, ?_⟩
    · simpa [hpUl] using hulv.1
    · simpa [hpUl] using hedge
    · simpa [hpUl] using hbad


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_twoDroppedEndpoint_noncarrierEdges
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {x y ur vr ul vl p q p' q' u : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {hx : x ∈ c.support} {hy : y ∈ c.support}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {rr : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    {rl : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
    (hulv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q'))
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hbadR : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
      gamma gamma' ur vr)
    (hbadL : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
      gamma gamma' ul vl)
    (hdecR : rlc_orderedContourArc c hx hy =
      (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hurv rr))
    (hdecL : (rlc_complementaryContourArc c hx hy).reverse =
      (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le
        gamma gamma' omega)).append (.cons hulv rl)) :
    ((∃ w : Site 2,
          (hypercubicLattice 2).Adj (phb_doubleDualShift p) w ∧
            s(phb_doubleDualShift p, w) ∈
              (rlc_orderedContourArc c hx hy).edges ∧
            ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
              gamma gamma' (phb_doubleDualShift p) w) ∨
        ∃ w : Site 2,
          (hypercubicLattice 2).Adj p w ∧
            s(p, w) ∈ (rlc_orderedContourArc c hx hy).edges ∧
            ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
              gamma gamma' p w) ∧
      ((∃ w : Site 2,
          (hypercubicLattice 2).Adj (phb_doubleDualShift p') w ∧
            s(phb_doubleDualShift p', w) ∈
              (rlc_complementaryContourArc c hx hy).edges ∧
            ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
              gamma gamma' (phb_doubleDualShift p') w) ∨
        ∃ w : Site 2,
          (hypercubicLattice 2).Adj p' w ∧
            s(p', w) ∈ (rlc_complementaryContourArc c hx hy).edges ∧
            ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
              gamma gamma' p' w) := by
  constructor
  · exact
      rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_noncarrierEdge
        hno hrow hurv hulv.1 hpq hpq' hpReach hqOut' hbadR hdecR
  · exact
      rlc_twoChannelFullPhysical_wallFamilyRowTwo_leftDroppedEndpoint_noncarrierEdge
        hno hrow hurv.1 hulv hpq hpq' hpReach hqOut' hbadL hdecL


theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_incidentFaces_axisSides
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur vr ul vl : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl) :
    vr 0 ≤ -1 ∧ -1 ≤ vl 0 := by
  have hurLeft : ur 0 < -1 := by
    have hpos := hrow.2.1.1
    simp only [rlc_dualReflect_zero] at hpos
    omega
  have hulRight : 0 ≤ ul 0 := by
    have hneg := hrow.2.2.2.1
    simp only [rlc_dualReflect_zero] at hneg
    omega
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hurv hulv
  constructor <;> omega


theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_sourceEndpoints_axisSides
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur vr ul vl p q p' q' : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q')) :
    p 0 < 0 ∧ 0 ≤ p' 0 := by
  have hurLeft : ur 0 < -1 := by
    have hpos := hrow.2.1.1
    simp only [rlc_dualReflect_zero] at hpos
    omega
  have hulRight : 0 ≤ ul 0 := by
    have hneg := hrow.2.2.2.1
    simp only [rlc_dualReflect_zero] at hneg
    omega
  have hpBounds :=
    rlc_sharedPrimalEdge_endpoint_horizontal_bounds hurv hpq
  have hp'Bounds :=
    rlc_sharedPrimalEdge_endpoint_horizontal_bounds hulv hpq'
  exact ⟨by omega, by omega⟩


theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_transverseWalk_meets_axis
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur vr ul vl : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (T : (hypercubicLattice 2).Walk vr vl) :
    ∃ a ∈ T.support, a 0 = -1 := by
  obtain ⟨hvr, hvl⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_incidentFaces_axisSides
      hrow hurv hulv
  by_cases hvrEq : vr 0 = -1
  · exact ⟨vr, T.start_mem_support, hvrEq⟩
  by_cases hvlEq : vl 0 = -1
  · exact ⟨vl, T.end_mem_support, hvlEq⟩
  exact hwalk_meets_column (k := -1) (α := vr 0) (β := vl 0)
    rfl rfl hvr (lt_of_le_of_ne hvl (Ne.symm hvlEq)) T


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_transverseWalk_axisProvenance
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur vr ul vl : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (T : (hypercubicLattice 2).Walk vr vl)
    (hTprov : ∀ v ∈ T.support,
      v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
        ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
          phb_doubleDualShift a = v) :
    ∃ v ∈ T.support, v 0 = -1 ∧
      (v = vr ∨ v = vl ∨
        ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
          a 0 = 0 ∧ phb_doubleDualShift a = v) := by
  obtain ⟨v, hvT, hv0⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_transverseWalk_meets_axis
      hrow hurv hulv T
  refine ⟨v, hvT, hv0, ?_⟩
  rcases hTprov v hvT with hvr | hur | hul | hvl |
      ⟨a, haReach, hav⟩
  · exact Or.inl hvr
  · have hurLeft : ur 0 < -1 := by
      have hpos := hrow.2.1.1
      simp only [rlc_dualReflect_zero] at hpos
      omega
    rw [hur] at hv0
    omega
  · have hulRight : 0 ≤ ul 0 := by
      have hneg := hrow.2.2.2.1
      simp only [rlc_dualReflect_zero] at hneg
      omega
    rw [hul] at hv0
    omega
  · exact Or.inr (Or.inl hvl)
  · right
    right
    refine ⟨a, haReach, ?_, hav⟩
    have hcoord := congrArg (fun z : Site 2 => z 0) hav
    simp [phb_doubleDualShift] at hcoord
    omega


theorem rlc_twoChannelFullPhysical_wallFamilyRowTwo_axisSourceSplice
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur vr ul vl : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo
      gamma gamma' omega qr ql)
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
        (∀ v ∈ T.support,
          v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
            ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
              phb_doubleDualShift a = v) ∧
        ∃ v ∈ T.support, v 0 = -1 ∧
          (v = vr ∨ v = vl ∨
            ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
              a 0 = 0 ∧ phb_doubleDualShift a = v) := by
  obtain ⟨p, q, p', q', T, hpq, hpq', hpqAdj, hpqAdj', hpReach,
      hpReach', hqOut, hqOut', hTprov⟩ :=
    rlc_twoChannelFullPhysical_boundary_directedReachableShiftWalk
      hurv hulv
  have haxis :=
    rlc_twoChannelFullPhysical_wallFamilyRowTwo_transverseWalk_axisProvenance
      hrow hurv.1 hulv.1 T hTprov
  exact ⟨p, q, p', q', T, hpq, hpq', hpqAdj, hpqAdj', hpReach,
    hpReach', hqOut, hqOut', hTprov, haxis⟩


theorem rlc_twoChannelFullPhysical_wallFamilyRowThree_incidentFaces_axisSides
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur vr ul vl : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowThree
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl) :
    vl 0 ≤ -1 ∧ -1 ≤ vr 0 := by
  have hurRight : 0 ≤ ur 0 := by
    have hneg := hrow.2.1.1
    simp only [rlc_dualReflect_zero] at hneg
    omega
  have hulLeft : ul 0 < -1 := by
    have hpos := hrow.2.2.2.1
    simp only [rlc_dualReflect_zero] at hpos
    omega
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hurv hulv
  constructor <;> omega


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowThree_sourceEndpoints_axisSides
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur vr ul vl p q p' q' : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowThree
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (hpq : sharedPrimalEdge ur vr = s(p, q))
    (hpq' : sharedPrimalEdge ul vl = s(p', q')) :
    0 ≤ p 0 ∧ p' 0 < 0 := by
  have hurRight : 0 ≤ ur 0 := by
    have hneg := hrow.2.1.1
    simp only [rlc_dualReflect_zero] at hneg
    omega
  have hulLeft : ul 0 < -1 := by
    have hpos := hrow.2.2.2.1
    simp only [rlc_dualReflect_zero] at hpos
    omega
  have hpBounds :=
    rlc_sharedPrimalEdge_endpoint_horizontal_bounds hurv hpq
  have hp'Bounds :=
    rlc_sharedPrimalEdge_endpoint_horizontal_bounds hulv hpq'
  exact ⟨by omega, by omega⟩


theorem rlc_twoChannelFullPhysical_wallFamilyRowThree_transverseWalk_meets_axis
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur vr ul vl : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowThree
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (T : (hypercubicLattice 2).Walk vr vl) :
    ∃ a ∈ T.support, a 0 = -1 := by
  obtain ⟨hvl, hvr⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowThree_incidentFaces_axisSides
      hrow hurv hulv
  by_cases hvrEq : vr 0 = -1
  · exact ⟨vr, T.start_mem_support, hvrEq⟩
  by_cases hvlEq : vl 0 = -1
  · exact ⟨vl, T.end_mem_support, hvlEq⟩
  obtain ⟨a, ha, ha0⟩ :=
    hwalk_meets_column (k := -1) (α := vl 0) (β := vr 0)
      rfl rfl hvl (lt_of_le_of_ne hvr (Ne.symm hvrEq)) T.reverse
  exact ⟨a, by simpa [SimpleGraph.Walk.support_reverse] using ha, ha0⟩


theorem
    rlc_twoChannelFullPhysical_wallFamilyRowThree_transverseWalk_axisProvenance
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur vr ul vl : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowThree
      gamma gamma' omega qr ql)
    (hurv : (hypercubicLattice 2).Adj ur vr)
    (hulv : (hypercubicLattice 2).Adj ul vl)
    (T : (hypercubicLattice 2).Walk vr vl)
    (hTprov : ∀ v ∈ T.support,
      v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
        ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
          phb_doubleDualShift a = v) :
    ∃ v ∈ T.support, v 0 = -1 ∧
      (v = vr ∨ v = vl ∨
        ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
          a 0 = 0 ∧ phb_doubleDualShift a = v) := by
  obtain ⟨v, hvT, hv0⟩ :=
    rlc_twoChannelFullPhysical_wallFamilyRowThree_transverseWalk_meets_axis
      hrow hurv hulv T
  refine ⟨v, hvT, hv0, ?_⟩
  rcases hTprov v hvT with hvr | hur | hul | hvl |
      ⟨a, haReach, hav⟩
  · exact Or.inl hvr
  · have hurRight : 0 ≤ ur 0 := by
      have hneg := hrow.2.1.1
      simp only [rlc_dualReflect_zero] at hneg
      omega
    rw [hur] at hv0
    omega
  · have hulLeft : ul 0 < -1 := by
      have hpos := hrow.2.2.2.1
      simp only [rlc_dualReflect_zero] at hpos
      omega
    rw [hul] at hv0
    omega
  · exact Or.inr (Or.inl hvl)
  · right
    right
    refine ⟨a, haReach, ?_, hav⟩
    have hcoord := congrArg (fun z : Site 2 => z 0) hav
    simp [phb_doubleDualShift] at hcoord
    omega


theorem rlc_twoChannelFullPhysical_wallFamilyRowThree_axisSourceSplice
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {x y ur vr ul vl : Site 2}
    {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk x ur}
    {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Walk y ul}
    (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowThree
      gamma gamma' omega qr ql)
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
        (∀ v ∈ T.support,
          v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
            ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
              phb_doubleDualShift a = v) ∧
        ∃ v ∈ T.support, v 0 = -1 ∧
          (v = vr ∨ v = vl ∨
            ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega,
              a 0 = 0 ∧ phb_doubleDualShift a = v) := by
  obtain ⟨p, q, p', q', T, hpq, hpq', hpqAdj, hpqAdj', hpReach,
      hpReach', hqOut, hqOut', hTprov⟩ :=
    rlc_twoChannelFullPhysical_boundary_directedReachableShiftWalk
      hurv hulv
  have haxis :=
    rlc_twoChannelFullPhysical_wallFamilyRowThree_transverseWalk_axisProvenance
      hrow hurv.1 hulv.1 T hTprov
  exact ⟨p, q, p', q', T, hpq, hpq', hpqAdj, hpqAdj', hpReach,
    hpReach', hqOut, hqOut', hTprov, haxis⟩


end
end StatMech.Universality
