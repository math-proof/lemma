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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part38
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_goodComponentContacts_of_retainedAnchorTraceIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
    (hinc : RlcCentralFaceRetainedAnchorTraceIncidence B) :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho := by
  obtain ⟨⟨x, hfirstX, hxRight⟩, y, hfirstY, hyLeft⟩ := hinc
  exact ⟨x, y, hfirstX.symm.trans hfirstY, hxRight, hyLeft⟩


theorem rlc_not_anchoredMissingIncidence_of_retainedAnchorTraceIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
    {f g : Site 2}
    (hinc : RlcCentralFaceRetainedAnchorTraceIncidence B) :
    ¬ RlcCentralFaceAnchoredNonwallGoodContourEdgeMissingContactIncidence
      B f g := by
  rintro ⟨_hfgContour, _hcarrier, _hnonwall, _hfirstF, _hfirstG,
    hmissing⟩
  rcases hinc with ⟨⟨x, hfirstX, hxRight⟩, y, hfirstY, hyLeft⟩
  rcases hmissing with hnoRight | ⟨_x, _hxRight, _hfirstX, hnoLeft⟩
  · exact hnoRight x hxRight hfirstX
  · exact hnoLeft y hyLeft hfirstY


theorem rlc_centralFacePIMS_success_of_retainedAnchorTraceIncidence
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho}
    (hinc : RlcCentralFaceRetainedAnchorTraceIncidence B) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  apply rlc_centralFacePIMS_success_of_goodComponentContacts
  exact rlc_goodComponentContacts_of_retainedAnchorTraceIncidence hinc


end
end StatMech.Universality
