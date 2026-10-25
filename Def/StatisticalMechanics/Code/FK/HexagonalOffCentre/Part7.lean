/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpness.Part5
import Theorem.StatisticalMechanics.Code.FK.HexagonalOffCentre.Part4
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

def hexagonalCenteredShellFullEvent (R k : Nat) :
    Set (ConfigSpace (Sym2 (HexagonalBoxVertex R))) :=
  {omega | ∃ y ∈ hexagonalBoxShell R k,
    (openSub (hexagonalBoxGraph R) omega).Reachable (hexagonalBoxRoot R) y}

def hexagonalTransShellFullEvent (R k : Nat) (x : HexVertex) :
    Set (ConfigSpace (Sym2 (HexagonalTransBoxVertex R x.1))) :=
  {omega | ∃ y ∈ hexagonalTransBoxShell R k x.1,
    (openSub (hexagonalTransBoxGraph R x.1) omega).Reachable
      (hexagonalTransBoxCenter R x) y}


end
end StatMech.FK.PeriodicPlanar
