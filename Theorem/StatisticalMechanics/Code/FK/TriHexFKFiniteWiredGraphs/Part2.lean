/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Instance.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

theorem triHexPlanarFiniteTriangleEdge_ne (n : Nat)
    (a : TriHexPlanarFiniteCell n × Fin 3) :
    (triHexPlanarFiniteTerminalMap n a.1
        (triHexTriangleEdgeTerminal1 a.2)) ≠
      triHexPlanarFiniteTerminalMap n a.1
        (triHexTriangleEdgeTerminal2 a.2) := by
  intro h
  have hval := congrArg Subtype.val h
  rcases a with ⟨z, i⟩
  fin_cases i <;>
    simp [triHexPlanarFiniteTerminalMap, triHexPlanarCellTerminal,
      triHexTriangleEdgeTerminal1, triHexTriangleEdgeTerminal2,
      hexagonalStep, funext_iff] at hval


theorem triHexPlanarFiniteTriangleEdge_mem (n : Nat)
    (a : TriHexPlanarFiniteCell n × Fin 3) :
    triHexPlanarFiniteTriangleEdge n a ∈
      (triHexPlanarFiniteTriangleGraph n).edgeSet := by
  rw [triHexPlanarFiniteTriangleGraph, SimpleGraph.edgeSet_fromEdgeSet]
  refine ⟨⟨a, rfl⟩, ?_⟩
  rw [Sym2.mem_diagSet]
  exact triHexPlanarFiniteTriangleEdge_ne n a


end
end StatMech.FK.PeriodicPlanar
