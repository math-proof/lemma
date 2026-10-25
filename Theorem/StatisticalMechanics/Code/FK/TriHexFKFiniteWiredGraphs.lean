/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs
open Finset Set


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open Universality

noncomputable section

theorem triHexPlanarFiniteTriangleEdge_val (n : Nat)
    (a : TriHexPlanarFiniteCell n × Fin 3) :
    Sym2.map (fun v : TriHexPlanarFiniteTerminal n => v.1)
        (triHexPlanarFiniteTriangleEdge n a) =
      triangularIndexedEdge
        (triHexPlanarTriangleIndexEquiv (a.1.1, a.2)) := by
  rcases a with ⟨z, i⟩
  rw [triHexPlanarFiniteTriangleEdge, Sym2.map_mk]
  fin_cases i
  · apply Sym2.eq_iff.mpr
    left
    constructor <;> ext k <;> fin_cases k <;>
      simp [triHexPlanarFiniteTerminalMap, triHexPlanarCellTerminal,
        triHexTriangleEdgeTerminal1, triHexTriangleEdgeTerminal2,
        triHexPlanarTriangleIndexEquiv, triHexPlanarTriangleEdgeBaseShift,
        triangularIndexedEdge, triangularStep, hexagonalStep]
  · apply Sym2.eq_iff.mpr
    right
    constructor <;> ext k <;> fin_cases k <;>
      simp [triHexPlanarFiniteTerminalMap, triHexPlanarCellTerminal,
        triHexTriangleEdgeTerminal1, triHexTriangleEdgeTerminal2,
        triHexPlanarTriangleIndexEquiv, triHexPlanarTriangleEdgeBaseShift,
        triangularIndexedEdge, triangularStep, hexagonalStep]
  · apply Sym2.eq_iff.mpr
    left
    constructor <;> ext k <;> fin_cases k <;>
      simp [triHexPlanarFiniteTerminalMap, triHexPlanarCellTerminal,
        triHexTriangleEdgeTerminal1, triHexTriangleEdgeTerminal2,
        triHexPlanarTriangleIndexEquiv, triHexPlanarTriangleEdgeBaseShift,
        triangularIndexedEdge, triangularStep, hexagonalStep]


theorem triHexPlanarFiniteTriangleEdge_injective (n : Nat) :
    Function.Injective (triHexPlanarFiniteTriangleEdge n) := by
  rintro ⟨a, i⟩ ⟨b, j⟩ hab
  have hval := congrArg
    (Sym2.map (fun v : TriHexPlanarFiniteTerminal n => v.1)) hab
  rw [triHexPlanarFiniteTriangleEdge_val,
    triHexPlanarFiniteTriangleEdge_val] at hval
  have hchart : triangularEdgeChart
      (triHexPlanarTriangleIndexEquiv (a.1, i)) =
      triangularEdgeChart
        (triHexPlanarTriangleIndexEquiv (b.1, j)) :=
    Subtype.ext hval
  have hindex := triHexPlanarTriangleIndexEquiv.injective
    (triangularEdgeChart_injective hchart)
  have hz : a.1 = b.1 :=
    congrArg (fun x : Site 2 × Fin 3 => x.1) hindex
  have hi : i = j :=
    congrArg (fun x : Site 2 × Fin 3 => x.2) hindex
  exact Prod.ext (Subtype.ext hz) hi


end
end StatMech.FK.PeriodicPlanar
