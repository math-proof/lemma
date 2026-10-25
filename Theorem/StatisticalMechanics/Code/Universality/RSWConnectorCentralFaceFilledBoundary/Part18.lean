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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part14
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_goodComponentContacts_or_badCarrierSeparation_of_filledContacts
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hcontacts : RlcCentralFaceFilledBoundaryContacts gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryBadCarrierSeparation gamma gamma' rho := by
  obtain ⟨x, y, hxSupport, hySupport, hxPath, hyPath⟩ := hcontacts
  by_cases hxy : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable x y
  · exact Or.inl ⟨x, y, hxy, hxPath, hyPath⟩
  · right
    obtain ⟨w⟩ := rlc_connectorCentralFaceFilledFaceBoundary_reachable
      gamma gamma' rho hxSupport hySupport
    rcases rlc_goodBoundary_prefix_or_first_bad
        (gamma := gamma) (gamma' := gamma') (rho := rho) w with
      ⟨q, _hqEdges⟩ | ⟨u, v, q, huv, _huvEdge, hbad, _hqEdges⟩
    · exact False.elim (hxy q.reachable)
    · refine ⟨x, y, u, v, hxPath, hyPath, q.reachable, huv, hbad, ?_⟩
      exact rlc_connectorCentralFaceFilledFaceBoundary_reachable
        gamma gamma' rho huv.mem_support_right hySupport


theorem rlc_goodComponentContacts_or_badCarrierSeparation_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryBadCarrierSeparation gamma gamma' rho := by
  exact rlc_goodComponentContacts_or_badCarrierSeparation_of_filledContacts
    gamma gamma' rho
      (rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
        gamma gamma' hfaith rho hno)


end
end StatMech.Universality
