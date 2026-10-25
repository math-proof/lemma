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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part52
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_rightArcShiftedBad_endpoint_tether
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u v a : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
    (hbad : RlcTwoChannelFullPhysicalRightArcShiftedClassifiedBad
      gamma gamma' omega u v a) :
    (∃ t : Site 2,
      RlcTwoChannelFullPhysicalRightArcBadLocation
        gamma gamma' (rlc_dualReflect t) ∧
      (a = t ∨ (hypercubicLattice 2).Adj a t)) ∨
    ∃ p : Site 2,
      RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p ∧
      (a = phb_doubleDualShift p ∨
        (hypercubicLattice 2).Adj a (phb_doubleDualShift p)) := by
  rcases hbad with ⟨_htarget, hloc, ha⟩ |
      ⟨p, q, _hpq, hpqAdj, _hpReach, _hqOut, hloc, ha⟩
  · left
    refine ⟨u, hloc, ?_⟩
    rw [Sym2.mem_iff] at ha
    rcases ha with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr huv.1.symm
  · right
    refine ⟨p, hloc, ?_⟩
    rcases ha with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (phb_doubleDualShift_latAdj.mpr hpqAdj).symm


theorem rlc_twoChannelFullPhysical_leftArcShiftedBad_endpoint_tether
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u v a : Site 2}
    (huv : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
    (hbad : RlcTwoChannelFullPhysicalLeftArcShiftedClassifiedBad
      gamma gamma' omega u v a) :
    (∃ t : Site 2,
      RlcTwoChannelFullPhysicalLeftArcTargetBadLocation
        gamma gamma' (rlc_dualReflect t) ∧
      (a = t ∨ (hypercubicLattice 2).Adj a t)) ∨
    ∃ p : Site 2,
      RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p ∧
      (a = phb_doubleDualShift p ∨
        (hypercubicLattice 2).Adj a (phb_doubleDualShift p)) := by
  rcases hbad with ⟨_htarget, hloc, ha⟩ |
      ⟨p, q, _hpq, hpqAdj, _hpReach, _hqOut, hloc, ha⟩
  · left
    refine ⟨u, hloc, ?_⟩
    rw [Sym2.mem_iff] at ha
    rcases ha with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr huv.1.symm
  · right
    refine ⟨p, hloc, ?_⟩
    rcases ha with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (phb_doubleDualShift_latAdj.mpr hpqAdj).symm


end
end StatMech.Universality
