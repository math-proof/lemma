/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpness.Part5
import Theorem.StatisticalMechanics.Code.FK.HexagonalOffCentre.Part3
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

noncomputable def hexagonalTransBoxEndU (R : Nat) (x : Site 2) :
    (hexagonalTransBoxGraph R x).edgeSet -> HexagonalTransBoxVertex R x :=
  fun e => e.1.out.1

noncomputable def hexagonalTransBoxEndV (R : Nat) (x : Site 2) :
    (hexagonalTransBoxGraph R x).edgeSet -> HexagonalTransBoxVertex R x :=
  fun e => e.1.out.2


def hexagonalTransShellEvent (R k : Nat) (x : HexVertex) :
    Set (ConfigSpace (hexagonalTransBoxGraph R x.1).edgeSet) :=
  openCrossEvent (hexagonalTransBoxEndU R x.1) (hexagonalTransBoxEndV R x.1)
    (hexagonalTransBoxCenter R x) (hexagonalTransBoxShell R k x.1)


def hexagonalCenteredShellEvent (R k : Nat) :
    Set (ConfigSpace (hexagonalBoxGraph R).edgeSet) :=
  openCrossEvent (hexagonalBoxEndU R) (hexagonalBoxEndV R)
    (hexagonalBoxRoot R) (hexagonalBoxShell R k)

end
end StatMech.FK.PeriodicPlanar
