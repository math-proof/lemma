/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualLumpedLaw.Part2
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomainActive
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

noncomputable section

def triHexBrickDualInnerActiveRestrict
    {N m : Nat} (hNm : N < m)
    (rho : ConfigSpace (triHexBrickFullDualGraph m).edgeSet) :
    ConfigSpace (triHexBrickInnerTriangleGraph N).edgeSet :=
  ocd_innerRestrictActive (triHexBrickInnerTriangleGraph N)
    (triHexBrickFullDualGraph m) (triHexBrickInnerFaceMap N m)
    (triHexBrickInnerFaceMap_adjMatch hNm) rho


end
end StatMech.FK.PeriodicPlanar
