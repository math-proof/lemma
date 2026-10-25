/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPairOrbitCharts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicCrossingGeometry
import Def.StatisticalMechanics.Code.FK.TriHexPairOrbitCharts.Part19
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem triHexPairOrbitDataEquiv_add (z : Site 2)
    (a : Site 2 × TriangularPairShape) :
    triHexPairOrbitDataEquiv (a.map (fun b => b + z) id) =
      (triHexPairOrbitDataEquiv a).map (fun b => b + z) id := by
  rcases a with ⟨x, s⟩
  change ((x + z) + triHexPairShapeOffset s, _) =
    ((x + triHexPairShapeOffset s) + z, _)
  apply Prod.ext
  · abel
  · rfl

theorem triHexFullDualEdgeEquiv_shift (z : Site 2)
    (e : Sym2 (Site 2)) :
    triHexFullDualEdgeEquiv (Sym2.map (siteTranslate z) e) =
      Sym2.map (hexTranslate z) (triHexFullDualEdgeEquiv e) := by
  apply hexagonalPairOrbitEquiv.injective
  simp only [triHexFullDualEdgeEquiv, Equiv.trans_apply]
  rw [hexagonalPairOrbitEquiv_add, triangularPairOrbitEquiv_add,
    triHexPairOrbitDataEquiv_add]
  simp

theorem triangularPairOrbitEquiv_indexedEdge (a : TriHexEdgeIndex) :
    triangularPairOrbitEquiv (triangularIndexedEdge a) =
      (a.1 + triangularEdgePairBase a.2,
        triangularEdgePairShape a.2) := by
  rcases a with ⟨x, i⟩
  have hxHead : Matrix.vecHead x = x 0 := rfl
  have hxTail : Matrix.vecHead (Matrix.vecTail x) = x 1 := rfl
  fin_cases i <;>
    simp [triangularPairOrbitEquiv, triangularPairOrbitTo_mk,
      triangularIndexedEdge, triangularEdgePairBase,
      triangularEdgePairShape, triangularPairNormal,
      triangularStep, siteLexNonnegative, hxHead, hxTail]

theorem hexagonalPairOrbitEquiv_indexedEdge (a : TriHexEdgeIndex) :
    hexagonalPairOrbitEquiv (hexagonalIndexedEdge a) =
      (a.1, hexagonalEdgePairShape a.2) := by
  rcases a with ⟨x, i⟩
  have hxHead : Matrix.vecHead x = x 0 := rfl
  have hxTail : Matrix.vecHead (Matrix.vecTail x) = x 1 := rfl
  fin_cases i <;>
    simp [hexagonalPairOrbitEquiv, hexagonalPairOrbitTo_mk,
      hexagonalIndexedEdge, hexagonalEdgePairShape,
      hexagonalPairNormal, hexagonalStep, siteLexPositive,
      boolOrdered, hxHead, hxTail]


theorem triHexFullDualEdgeEquiv_indexedEdge (a : TriHexEdgeIndex) :
    triHexFullDualEdgeEquiv (triangularIndexedEdge a) =
      hexagonalIndexedEdge (triHexIndexEquiv a) := by
  apply hexagonalPairOrbitEquiv.injective
  simp only [triHexFullDualEdgeEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rw [triangularPairOrbitEquiv_indexedEdge,
    hexagonalPairOrbitEquiv_indexedEdge]
  change (a.1 + triangularEdgePairBase a.2 +
      triHexPairShapeOffset (triangularEdgePairShape a.2),
        triHexPairShapeEquiv (triangularEdgePairShape a.2)) = _
  rw [triHexPairShapeEquiv_edge]
  apply Prod.ext
  · change a.1 + triangularEdgePairBase a.2 +
      triHexPairShapeOffset (triangularEdgePairShape a.2) =
        (triHexIndexEquiv a).1
    rw [add_assoc, triHexPairShapeOffset_edge]
    have h := congrArg Prod.fst (triHexIndexEquiv_add a.1 (0, a.2))
    simpa [add_comm] using h.symm
  · change hexagonalEdgePairShape a.2 =
      hexagonalEdgePairShape (triHexIndexEquiv a).2
    rcases a with ⟨x, i⟩
    fin_cases i <;> rfl

theorem triHexFullDualEdgeEquiv_edgeChart (a : TriHexEdgeIndex) :
    triHexFullDualEdgeEquiv (triangularEdgeChart a : Sym2 (Site 2)) =
      (triHexDualEdgeEquiv (triangularEdgeChart a) : Sym2 HexVertex) := by
  rw [triHexDualEdgeEquiv_chart]
  exact triHexFullDualEdgeEquiv_indexedEdge a

theorem triHexFullDualEdgeEquiv_mem_edgeSet (e : Sym2 (Site 2)) :
    e ∈ triangularGraph.edgeSet ↔
      triHexFullDualEdgeEquiv e ∈ hexagonalGraph.edgeSet := by
  constructor
  · intro he
    let et : triangularGraph.edgeSet := ⟨e, he⟩
    obtain ⟨a, ha⟩ := triangularEdgeChart_surjective et
    have hval : triangularIndexedEdge a = e :=
      congrArg Subtype.val ha
    rw [← hval, triHexFullDualEdgeEquiv_indexedEdge]
    exact hexagonalIndexedEdge_mem (triHexIndexEquiv a)
  · intro he
    let ft : hexagonalGraph.edgeSet :=
      ⟨triHexFullDualEdgeEquiv e, he⟩
    obtain ⟨b, hb⟩ := hexagonalEdgeChart_surjective ft
    let a := triHexIndexEquiv.symm b
    have hbval : hexagonalIndexedEdge b = triHexFullDualEdgeEquiv e :=
      congrArg Subtype.val hb
    have hpair : triHexFullDualEdgeEquiv (triangularIndexedEdge a) =
        triHexFullDualEdgeEquiv e := by
      rw [triHexFullDualEdgeEquiv_indexedEdge]
      simpa [a] using hbval
    have ha : triangularIndexedEdge a = e :=
      triHexFullDualEdgeEquiv.injective hpair
    rw [← ha]
    exact triangularIndexedEdge_mem a

theorem triHexFullDualEdgeEquiv_eq_edgeDual
    (e : triangularGraph.edgeSet) :
    triHexFullDualEdgeEquiv (e : Sym2 (Site 2)) =
      (triHexDualEdgeEquiv e : Sym2 HexVertex) := by
  let a := triangularEdgeChartEquiv.symm e
  have ha : triangularEdgeChart a = e :=
    triangularEdgeChartEquiv.apply_symm_apply e
  rw [← ha]
  exact triHexFullDualEdgeEquiv_edgeChart a

end StatMech.FK.PeriodicPlanar
