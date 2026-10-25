/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDuality
import Def.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part6
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice

theorem incidentHexFaces_adj (a : TriHexEdgeIndex) :
    hexagonalGraph.Adj (incidentHexFaces a).1 (incidentHexFaces a).2 := by
  exact hexagonal_adj_neighbor
    ((triHexIndexEquiv a).1, false) (triHexIndexEquiv a).2


theorem triangular_edge_incident_faces (a : TriHexEdgeIndex) :
    let x := a.1
    let y := a.1 + triangularStep a.2
    x ∈ triangularFace (incidentHexFaces a).1 ∧
      y ∈ triangularFace (incidentHexFaces a).1 ∧
      x ∈ triangularFace (incidentHexFaces a).2 ∧
      y ∈ triangularFace (incidentHexFaces a).2 := by
  rcases a with ⟨x, i⟩
  have hx : x = ![x 0, x 1] := by
    funext j
    fin_cases j <;> simp
  rw [hx]
  fin_cases i <;>
    simp [incidentHexFaces, triHexIndexEquiv, triangularFace,
      triangularStep, hexagonalStep, funext_iff]
  all_goals ring

theorem triHexDualEdgeEquiv_chart (a : TriHexEdgeIndex) :
    (triHexDualEdgeEquiv (triangularEdgeChart a) : Sym2 HexVertex) =
      hexagonalIndexedEdge (triHexIndexEquiv a) := by
  simp only [triHexDualEdgeEquiv, Equiv.trans_apply]
  have ht : triangularEdgeChartEquiv a = triangularEdgeChart a := rfl
  rw [← ht, Equiv.symm_apply_apply]
  rfl

end PeriodicPlanar
end FK
end StatMech
