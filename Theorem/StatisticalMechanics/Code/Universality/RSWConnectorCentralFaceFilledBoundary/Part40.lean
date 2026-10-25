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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part36
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_goodComponentContacts_or_nonwallEdgeMissingContactIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
    {f g : Site 2}
    (hfgContour : s(f, g) ∈ B.contour.edges)
    (hcarrier : RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' f g)
    (hnonwall : s(rlc_dualReflect f, rlc_dualReflect g) ∉
      rlc_connectorFourTraceEdges gamma gamma') :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceNonwallGoodContourEdgeMissingContactIncidence B f g := by
  have hfgBoundary : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj f g :=
    B.contour.adj_of_mem_edges hfgContour
  have hfgGood : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Adj f g := ⟨hfgBoundary, hcarrier⟩
  have hfgReach := hfgGood.reachable
  by_cases hgood : RlcCentralFaceFilledBoundaryGoodComponentContacts
      gamma gamma' rho
  · exact Or.inl hgood
  right
  refine ⟨hfgContour, hcarrier, hnonwall, ?_⟩
  by_cases hright : ∃ x : Site 2,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable f x
  · right
    obtain ⟨x, hxRight, hfx⟩ := hright
    refine ⟨x, hxRight, hfx, hfgReach.symm.trans hfx, ?_⟩
    intro y hyLeft
    constructor
    · intro hfy
      exact hgood ⟨x, y, hfx.symm.trans hfy, hxRight, hyLeft⟩
    · intro hgy
      have hfy := hfgReach.trans hgy
      exact hgood ⟨x, y, hfx.symm.trans hfy, hxRight, hyLeft⟩
  · left
    intro x hxRight
    constructor
    · intro hfx
      exact hright ⟨x, hxRight, hfx⟩
    · intro hgx
      exact hright ⟨x, hxRight, hfgReach.trans hgx⟩


end
end StatMech.Universality
