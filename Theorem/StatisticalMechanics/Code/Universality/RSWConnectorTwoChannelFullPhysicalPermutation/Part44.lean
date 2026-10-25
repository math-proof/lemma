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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part44
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_contourArcSide_iff_badEdgesOnOneArc
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hc : c.IsTrail) (hx : x ∈ c.support) (hy : y ∈ c.support) :
    RlcTwoChannelFullPhysicalContourArcSide gamma gamma' omega c hx hy ↔
      RlcTwoChannelFullPhysicalBadEdgesOnOneArcAt
        gamma gamma' omega c hx hy := by
  classical
  have hdisjoint :=
    rlc_orderedContourArc_edges_disjoint_complementary c hc hx hy
  constructor
  · intro hside
    rcases hside with hordered | hcomplementary
    · left
      intro f g he hbad
      rcases (rlc_contourArc_edges_cover c hx hy).mp he with hord | hcomp
      · exact False.elim (hbad (hordered hord))
      · exact hcomp
    · right
      intro f g he hbad
      rcases (rlc_contourArc_edges_cover c hx hy).mp he with hord | hcomp
      · exact hord
      · exact False.elim (hbad (hcomplementary hcomp))
  · rintro (hbadComp | hbadOrd)
    · left
      intro f g he
      by_contra hbad
      have hec := rlc_orderedContourArc_edges_subset c hx hy he
      exact hdisjoint he (hbadComp hec hbad)
    · right
      intro f g he
      by_contra hbad
      have hec := rlc_complementaryContourArc_edges_subset c hx hy he
      exact hdisjoint (hbadOrd hec hbad) he


theorem rlc_twoChannelFullPhysical_goodReachable_of_carriedBoundaryWalk
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {x y : Site 2}
    (a : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk x y)
    (hcarried : ∀ {f g : Site 2}, s(f, g) ∈ a.edges →
      RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g) :
    (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Reachable x y := by
  induction a with
  | nil => exact Reachable.refl _
  | @cons u v z huv p ih =>
      have huvGood : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Adj u v :=
        (rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
          gamma gamma' omega).2 ⟨huv, hcarried (by simp)⟩
      have hpCarried : ∀ {f g : Site 2}, s(f, g) ∈ p.edges →
          RlcTwoChannelFullPhysicalBoundaryCarrierGeometry
            gamma gamma' f g := by
        intro f g hfg
        exact hcarried (by simp [hfg])
      exact huvGood.reachable.trans (ih hpCarried)


theorem rlc_twoChannelFullPhysical_goodReachable_of_repairedBoundaryWalk
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {x y : Site 2}
    (a : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk x y)
    (hrepair : ∀ {f g : Site 2}, s(f, g) ∈ a.edges →
      (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Reachable f g) :
    (rlc_twoChannelFullPhysicalGoodBoundaryGraph
      gamma gamma' omega).Reachable x y := by
  induction a with
  | nil => exact Reachable.refl _
  | @cons u v z huv p ih =>
      have huvReach : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
          gamma gamma' omega).Reachable u v :=
        hrepair (by simp)
      have hpRepair : ∀ {f g : Site 2}, s(f, g) ∈ p.edges →
          (rlc_twoChannelFullPhysicalGoodBoundaryGraph
            gamma gamma' omega).Reachable f g := by
        intro f g hfg
        exact hrepair (by simp [hfg])
      exact huvReach.trans (ih hpRepair)


end
end StatMech.Universality
