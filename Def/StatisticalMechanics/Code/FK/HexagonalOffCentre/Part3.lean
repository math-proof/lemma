/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpness.Part5
import Instance.StatisticalMechanics.Code.FK.HexagonalOffCentre.Part2
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

def hexagonalTransBoxIncl {R N : Nat} {x : Site 2}
    (hsub : hexagonalTransBox R x ⊆ box 2 N) :
    HexagonalTransBoxVertex R x -> HexagonalBoxVertex N :=
  fun y => ⟨y.1, ⟨hsub y.2.1, Set.mem_univ _⟩⟩

end
end StatMech.FK.PeriodicPlanar
