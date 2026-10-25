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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part46
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_twoChannelFullPhysical_contourArcRepairSide_of_contourArcSide
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hside : RlcTwoChannelFullPhysicalContourArcSide
      gamma gamma' omega c hx hy) :
    RlcTwoChannelFullPhysicalContourArcRepairSide
      gamma gamma' omega c hx hy := by
  rcases hside with hordered | hcomplementary
  · left
    intro f g hfg
    exact
      (((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
          gamma gamma' omega).2
        ⟨(rlc_orderedContourArc c hx hy).adj_of_mem_edges hfg,
          hordered hfg⟩).reachable)
  · right
    intro f g hfg
    exact
      (((rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry
          gamma gamma' omega).2
        ⟨(rlc_complementaryContourArc c hx hy).adj_of_mem_edges hfg,
          hcomplementary hfg⟩).reachable)


theorem rlc_twoChannelFullPhysical_goodComponent_of_contourArcRepairSide
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hrepair : RlcTwoChannelFullPhysicalContourArcRepairSide
      gamma gamma' omega c hx hy) :
    RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega := by
  rcases hrepair with hordered | hcomplementary
  · exact ⟨x, y,
      rlc_twoChannelFullPhysical_goodReachable_of_repairedBoundaryWalk
        gamma gamma' omega (rlc_orderedContourArc c hx hy) hordered,
      hxPath, hyPath⟩
  · exact ⟨x, y,
      rlc_twoChannelFullPhysical_goodReachable_of_repairedBoundaryWalk
        gamma gamma' omega (rlc_complementaryContourArc c hx hy)
          hcomplementary,
      hxPath, hyPath⟩


theorem rlc_twoChannelFullPhysical_goodComponent_of_contourArcSide
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hside : RlcTwoChannelFullPhysicalContourArcSide
      gamma gamma' omega c hx hy) :
    RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega := by
  rcases hside with hordered | hcomplementary
  · exact ⟨x, y,
      rlc_twoChannelFullPhysical_goodReachable_of_carriedBoundaryWalk
        gamma gamma' omega (rlc_orderedContourArc c hx hy) hordered,
      hxPath, hyPath⟩
  · exact ⟨x, y,
      rlc_twoChannelFullPhysical_goodReachable_of_carriedBoundaryWalk
        gamma gamma' omega (rlc_complementaryContourArc c hx hy)
          hcomplementary,
      hxPath, hyPath⟩


end
end StatMech.Universality
