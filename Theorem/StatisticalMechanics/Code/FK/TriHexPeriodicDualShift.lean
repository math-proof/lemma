/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicDualShift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem triangularIndexedEdge_add (z : Site 2) (a : TriHexEdgeIndex) :
    triangularIndexedEdge (a.1 + z, a.2) =
      Sym2.map (siteTranslate z) (triangularIndexedEdge a) := by
  apply Sym2.eq_iff.mpr
  left
  constructor
  · rfl
  · ext i
    simp [siteTranslate_apply, add_comm, add_left_comm]


theorem hexagonalIndexedEdge_add (z : Site 2) (a : TriHexEdgeIndex) :
    hexagonalIndexedEdge (a.1 + z, a.2) =
      Sym2.map (hexTranslate z) (hexagonalIndexedEdge a) := by
  apply Sym2.eq_iff.mpr
  left
  constructor
  · rfl
  · apply Prod.ext
    · ext i
      simp [hexTranslate_apply, add_comm, add_left_comm]
    · rfl


theorem triHexIndexEquiv_add (z : Site 2) (a : TriHexEdgeIndex) :
    triHexIndexEquiv (a.1 + z, a.2) =
      ((triHexIndexEquiv a).1 + z, (triHexIndexEquiv a).2) := by
  rcases a with ⟨x, i⟩
  fin_cases i <;>
    exact Prod.ext (by
      funext j
      simp [triHexIndexEquiv] <;> ring) rfl


theorem triHexDualEdgeEquiv_add_chart (z : Site 2) (a : TriHexEdgeIndex) :
    ((triHexDualEdgeEquiv
          (triangularEdgeChart (a.1 + z, a.2)) :
        hexagonalGraph.edgeSet) : Sym2 HexVertex) =
      Sym2.map (hexTranslate z)
        ((triHexDualEdgeEquiv (triangularEdgeChart a) :
          hexagonalGraph.edgeSet) : Sym2 HexVertex) := by
  rw [triHexDualEdgeEquiv_chart, triHexDualEdgeEquiv_chart]
  rw [triHexIndexEquiv_add]
  exact hexagonalIndexedEdge_add z (triHexIndexEquiv a)


end StatMech.FK.PeriodicPlanar
