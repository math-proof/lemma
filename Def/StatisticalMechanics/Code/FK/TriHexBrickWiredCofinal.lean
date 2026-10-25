/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickWiredCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualInfiniteDomination
import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessCritical.Part10
open Filter Finset MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

open StatMech.OSSS

noncomputable section

def triangularBoxActiveRestrictLE {n m : Nat} (hnm : n ≤ m)
    (rho : ConfigSpace (triangularBoxGraph m).edgeSet) :
    ConfigSpace (triangularBoxGraph n).edgeSet :=
  restrictConfig (triangularBoxEdgeLE hnm) rho

end
end StatMech.FK.PeriodicPlanar
