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
import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part4
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

def triangularCenteredShellFullEvent (R k : Nat) :
    Set (ConfigSpace (Sym2 (TriangularBoxVertex R))) :=
  {omega | ∃ y ∈ triangularBoxShell R k,
    (openSub (triangularBoxGraph R) omega).Reachable (triangularBoxRoot R) y}

def triangularTransShellFullEvent (R k : Nat) (x : Site 2) :
    Set (ConfigSpace (Sym2 (TriangularTransBoxVertex R x))) :=
  {omega | ∃ y ∈ triangularTransBoxShell R k x,
    (openSub (triangularTransBoxGraph R x) omega).Reachable
      (triangularTransBoxCenter R x) y}


end
end StatMech.FK.PeriodicPlanar
