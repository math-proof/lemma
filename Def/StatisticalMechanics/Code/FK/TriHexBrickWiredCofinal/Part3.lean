/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualInfiniteDomination
import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessCritical.Part10
import Theorem.StatisticalMechanics.Code.FK.TriHexBrickWiredCofinal.Part2
open Filter Finset MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

open StatMech.OSSS

noncomputable section

def triangularBoxBufferedActiveRestrict (k m : Nat)
    (hkm : 2 * k ≤ triangular.bufferedRadius m)
    (rho : ConfigSpace (triangular.bufferedGraph m).edgeSet) :
    ConfigSpace (triangularBoxGraph (2 * k)).edgeSet :=
  ocd_innerRestrictActive (triangularBoxGraph (2 * k))
    (triangular.bufferedGraph m) (triangularBoxToBufferedAt k m hkm)
    (triangularBoxToBufferedAt_adjMatch k m hkm) rho

end
end StatMech.FK.PeriodicPlanar
