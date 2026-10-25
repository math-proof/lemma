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
import Instance.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal
open Finset Set SimpleGraph Filter MeasureTheory Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

theorem triHexPlanarFiniteTriangleGraph_le_induced (n : Nat) :
    triHexPlanarFiniteTriangleGraph n ≤
      triHexPlanarFiniteTriangleInducedGraph n := by
  intro u v huv
  rw [triHexPlanarFiniteTriangleGraph,
    SimpleGraph.fromEdgeSet_adj] at huv
  obtain ⟨⟨⟨z, i⟩, hedge⟩, _⟩ := huv
  change s(triHexPlanarFiniteTerminalMap n z
      (triHexTriangleEdgeTerminal1 i),
    triHexPlanarFiniteTerminalMap n z
      (triHexTriangleEdgeTerminal2 i)) = s(u, v) at hedge
  have hamb := triangularGraph_adj_triHexPlanarCellTerminal z.1
    (triHexTriangleEdgeTerminal1 i)
    (triHexTriangleEdgeTerminal2 i) (by
      fin_cases i <;> decide)
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · subst u
    subst v
    simpa [triHexPlanarFiniteTriangleInducedGraph,
      triHexPlanarFiniteTerminalMap] using hamb
  · subst u
    subst v
    simpa [triHexPlanarFiniteTriangleInducedGraph,
      triHexPlanarFiniteTerminalMap] using hamb.symm


theorem triHexPlanarFiniteRoot_not_boundary_succ (n : Nat) :
    ¬ triHexPlanarFiniteBoundary (n + 1)
      (triHexPlanarFiniteTerminalMap (n + 1)
        (triHexPlanarFiniteRootCell (n + 1)) 0) := by
  rintro ⟨i, hi⟩
  apply hi
  intro k
  fin_cases i <;> fin_cases k <;>
    simp [triHexPlanarFiniteTerminalMap, triHexPlanarFiniteRootCell,
      triHexPlanarCellTerminal, hexagonalStep]


end
end StatMech.FK.PeriodicPlanar
