/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpness.Part5
import Abbrev.StatisticalMechanics.Code.FK.HexagonalOffCentre
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

def hexagonalTransBoxVertexEquiv (R : Nat) (x : Site 2) :
    (StatMech.FK.fvs_transBoxVerts 2 R x × Bool) ≃
      HexagonalTransBoxVertex R x where
  toFun y := ⟨(y.1.1, y.2), ⟨y.1.2, Set.mem_univ _⟩⟩
  invFun y := (⟨y.1.1, y.2.1⟩, y.1.2)
  left_inv y := rfl
  right_inv y := rfl

end
end StatMech.FK.PeriodicPlanar
