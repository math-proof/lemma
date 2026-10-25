/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDiagonalLimit
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverageUpgrade
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part12
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

@[simp] theorem triHexPlanarFiniteTriangleRoot_val (n : Nat) :
    (triHexPlanarFiniteTriangleRoot n).1 = triHexPlanarTriRoot := by
  ext k
  fin_cases k <;>
    simp [triHexPlanarFiniteTriangleRoot, triHexPlanarTriRoot,
      triHexPlanarFiniteTerminalMap, triHexPlanarFiniteRootCell,
      triHexPlanarCellTerminal, hexagonalStep]

end
end StatMech.FK.PeriodicPlanar
