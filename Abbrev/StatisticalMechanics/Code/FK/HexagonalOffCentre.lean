/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpness.Part5
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

abbrev hexagonalTransBox (R : Nat) (x : Site 2) : Set (Site 2) :=
  StatMech.FK.fvs_transBox 2 R x

abbrev HexagonalTransBoxVertex (R : Nat) (x : Site 2) :=
  ↑((hexagonalTransBox R x) ×ˢ (Set.univ : Set Bool))

end
end StatMech.FK.PeriodicPlanar
