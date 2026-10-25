/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceDualPercolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualOpenBoundary.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareAnchoredShell.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.NearestSetGeometry.Part4
open Filter MeasureTheory Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

open StatMech.Universality StatMech.FK.PeriodicPlanar

open StatMech.FrontierA

noncomputable section

def faceDualAxisAnchor (j : Nat) : Site 2 :=
  square.shift ![1, 1] (axisSite j)


def faceDualAxisToOriginShift (j : Nat) : Multiplicative (Site 2) :=
  Multiplicative.ofAdd (-faceDualAxisAnchor j)


def fkQgt4FaceDualAnchoredSphereConnectionEvent (j : Nat) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  (ConfigSpace.shift (faceDualAxisToOriginShift j)) ⁻¹'
    fkQgt4CriticalFreeSphereConnectionEvent j

end
end StatMech.FrontierD
