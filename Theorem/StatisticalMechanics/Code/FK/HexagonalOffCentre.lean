/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpness.Part5
import Def.StatisticalMechanics.Code.FK.HexagonalOffCentre.Part3
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

@[simp] theorem hexagonalTransBoxIncl_val {R N : Nat} {x : Site 2}
    (hsub : hexagonalTransBox R x ⊆ box 2 N)
    (y : HexagonalTransBoxVertex R x) :
    (hexagonalTransBoxIncl hsub y).1.1 = y.1.1 := rfl

theorem hexagonalTransBoxIncl_injective {R N : Nat} {x : Site 2}
    (hsub : hexagonalTransBox R x ⊆ box 2 N) :
    Function.Injective (hexagonalTransBoxIncl hsub) := by
  intro y z hyz
  apply Subtype.ext
  exact congrArg (fun w : HexagonalBoxVertex N => (w : HexVertex)) hyz


end
end StatMech.FK.PeriodicPlanar
