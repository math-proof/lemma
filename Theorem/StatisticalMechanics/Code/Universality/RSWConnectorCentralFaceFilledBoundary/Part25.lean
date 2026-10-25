/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part21
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_goodComponentContacts_or_lowestAnchorOrderedBadExit_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceLowestAnchorOrderedBadExit gamma gamma' rho := by
  classical
  let L := Classical.choice
    (rlc_centralFace_lowestRetainedAnchoredBoundary_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair rho hno)
  let B := L.boundary
  obtain ⟨x, y, hxSupport, hySupport, hxPath, hyPath⟩ :=
    rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith rho hno
  obtain ⟨x', hxx'⟩ := hxSupport
  obtain ⟨y', hyy'⟩ := hySupport
  have hxe : s(x, x') ∈ B.contour.edges := B.contour_covers _
    (by rw [SimpleGraph.mem_edgeSet]; exact hxx')
  have hye : s(y, y') ∈ B.contour.edges := B.contour_covers _
    (by rw [SimpleGraph.mem_edgeSet]; exact hyy')
  have hx : x ∈ B.contour.support :=
    B.contour.fst_mem_support_of_mem_edges hxe
  have hy : y ∈ B.contour.support :=
    B.contour.fst_mem_support_of_mem_edges hye
  let px := B.contour.takeUntil x hx
  let py := B.contour.takeUntil y hy
  rcases rlc_goodBoundary_prefix_or_first_bad px with
      ⟨qx, hqx⟩ | ⟨ux, vx, qx, huvx, huvxEdge, hbadx, hqx⟩
  · rcases rlc_goodBoundary_prefix_or_first_bad py with
        ⟨qy, hqy⟩ | ⟨uy, vy, qy, huvy, huvyEdge, hbady, hqy⟩
    · left
      exact ⟨x, y, qx.reachable.symm.trans qy.reachable, hxPath, hyPath⟩
    · right
      refine ⟨L, x, y, y, py, uy, vy, qy, hx, hy, hxPath, hyPath,
        Or.inr rfl, ?_, hqy, huvy, huvyEdge, hbady, ?_⟩
      · exact B.contour.edges_takeUntil_subset hy
      · exact rlc_goodBoundary_bad_exit_near_barrier_or_boxBoundary
          B hfaith qy.reachable huvy hbady
  · right
    refine ⟨L, x, y, x, px, ux, vx, qx, hx, hy, hxPath, hyPath,
      Or.inl rfl, ?_, hqx, huvx, huvxEdge, hbadx, ?_⟩
    · exact B.contour.edges_takeUntil_subset hx
    · exact rlc_goodBoundary_bad_exit_near_barrier_or_boxBoundary
        B hfaith qx.reachable huvx hbadx

end
end StatMech.Universality
