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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part68
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem
    rlc_twoChannelFullPhysical_rightNonExclusiveLocalizedBad_atCut
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {u v : Site 2}
    (hbad : RlcTwoChannelFullPhysicalRightArcNonExclusiveLocalizedBad
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) u v) :
    ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v) ∧
        (rlc_dualReflect u ∈ rlc_pathVertices gamma.1 ∨
          (rlc_dualReflect u) 0 = -2 * n ∨
          (rlc_dualReflect u) 0 = 2 * n ∨
          (rlc_dualReflect u) 1 = -n ∨
          (rlc_dualReflect u) 1 = n)) ∨
      ∃ p q : Site 2,
        sharedPrimalEdge u v = s(p, q) ∧
          (hypercubicLattice 2).Adj p q ∧
          p ∈ rlc_twoChannelFullPhysicalLiftVertexCut A ∧
          q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
          RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p := by
  rcases hbad with htarget |
      ⟨p, q, hpq, hpqAdj, hpReach, hqOut, hpPlace⟩
  · exact Or.inl htarget
  · exact Or.inr ⟨p, q, hpq, hpqAdj,
      rlc_twoChannelFullReachSet_subset_staticCut
        gamma gamma' A hAright hAleft hpReach,
      hqOut, hpPlace⟩


theorem
    rlc_twoChannelFullPhysical_leftNonExclusiveLocalizedBad_atCut
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {u v : Site 2}
    (hbad : RlcTwoChannelFullPhysicalLeftArcNonExclusiveLocalizedBad
      gamma gamma'
        (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) u v) :
    ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v) ∧
        (rlc_dualReflect u ∈ rlc_pathVertices gamma'.1 ∨
          (rlc_dualReflect u) 0 = -2 * n ∨
          (rlc_dualReflect u) 0 = 2 * n ∨
          (rlc_dualReflect u) 1 = -n ∨
          (rlc_dualReflect u) 1 = n)) ∨
      ∃ p q : Site 2,
        sharedPrimalEdge u v = s(p, q) ∧
          (hypercubicLattice 2).Adj p q ∧
          p ∈ rlc_twoChannelFullPhysicalLiftVertexCut A ∧
          q ∉ rlc_twoChannelFullFilledReachSet gamma gamma'
            (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧
          RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p := by
  rcases hbad with htarget |
      ⟨p, q, hpq, hpqAdj, hpReach, hqOut, hpPlace⟩
  · exact Or.inl htarget
  · exact Or.inr ⟨p, q, hpq, hpqAdj,
      rlc_twoChannelFullReachSet_subset_staticCut
        gamma gamma' A hAright hAleft hpReach,
      hqOut, hpPlace⟩


theorem rlc_twoChannelFullPhysical_sourceSpliceProvenance_atCut
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {ur vr ul vl : Site 2}
    (T : (hypercubicLattice 2).Walk vr vl)
    (hTprov : ∀ v ∈ T.support,
      v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
        ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A),
          phb_doubleDualShift a = v) :
    ∀ v ∈ T.support,
      v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨
        ∃ a ∈ rlc_twoChannelFullPhysicalLiftVertexCut A,
          phb_doubleDualShift a = v := by
  intro v hv
  rcases hTprov v hv with hvr | hur | hul | hvl | ⟨a, ha, hav⟩
  · exact Or.inl hvr
  · exact Or.inr (Or.inl hur)
  · exact Or.inr (Or.inr (Or.inl hul))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hvl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨a, rlc_twoChannelFullReachSet_subset_staticCut
        gamma gamma' A hAright hAleft ha, hav⟩)))


theorem rlc_twoChannelFullPhysical_axisSourceContact_atCut
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (A : Set (RlcConnectorVertex n))
    (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
    (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
    {vr vl : Site 2}
    (T : (hypercubicLattice 2).Walk vr vl)
    (haxis : ∃ v ∈ T.support, v 0 = -1 ∧
      (v = vr ∨ v = vl ∨
        ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma'
          (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A),
          a 0 = 0 ∧ phb_doubleDualShift a = v)) :
    ∃ v ∈ T.support, v 0 = -1 ∧
      (v = vr ∨ v = vl ∨
        ∃ a ∈ rlc_twoChannelFullPhysicalLiftVertexCut A,
          a 0 = 0 ∧ phb_doubleDualShift a = v) := by
  obtain ⟨v, hv, hv0, hsource⟩ := haxis
  refine ⟨v, hv, hv0, ?_⟩
  rcases hsource with hvr | hvl | ⟨a, ha, ha0, hav⟩
  · exact Or.inl hvr
  · exact Or.inr (Or.inl hvl)
  · exact Or.inr (Or.inr ⟨a,
      rlc_twoChannelFullReachSet_subset_staticCut
        gamma gamma' A hAright hAleft ha, ha0, hav⟩)


end
end StatMech.Universality
