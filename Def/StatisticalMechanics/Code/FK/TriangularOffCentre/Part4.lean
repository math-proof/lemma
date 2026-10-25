/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularSharpness.Part5
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomainActive
import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part3
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

noncomputable def triangularTransBoxEndU (R : Nat) (x : Site 2) :
    (triangularTransBoxGraph R x).edgeSet -> TriangularTransBoxVertex R x :=
  fun e => e.1.out.1

noncomputable def triangularTransBoxEndV (R : Nat) (x : Site 2) :
    (triangularTransBoxGraph R x).edgeSet -> TriangularTransBoxVertex R x :=
  fun e => e.1.out.2


def triangularTransShellEvent (R k : Nat) (x : Site 2) :
    Set (ConfigSpace (triangularTransBoxGraph R x).edgeSet) :=
  openCrossEvent (triangularTransBoxEndU R x) (triangularTransBoxEndV R x)
    (triangularTransBoxCenter R x) (triangularTransBoxShell R k x)


def triangularCenteredShellEvent (R k : Nat) :
    Set (ConfigSpace (triangularBoxGraph R).edgeSet) :=
  openCrossEvent (triangularBoxEndU R) (triangularBoxEndV R)
    (triangularBoxRoot R) (triangularBoxShell R k)

end
end StatMech.FK.PeriodicPlanar
