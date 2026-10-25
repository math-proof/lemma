/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGenericPolygonReduction
import Def.StatisticalMechanics.Code.FrontierA.KacWardPolygonPerturbation.Part2


namespace StatMech.FrontierA

open scoped Convex

open Set

theorem KWRawSimplePolygonData.of_vertex_perturbation
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (vertex : Fin n → ℂ) {eps vertexRadius edgeRadius : ℝ}
    (hvertex : ∀ i : Fin n,
      dist (vertex i) (polygon.vertex i) ≤ eps)
    (hvertexSep : ∀ i j : Fin n, i ≠ j →
      vertexRadius < dist (polygon.vertex i) (polygon.vertex j))
    (hedgeSep : ∀ i j : Fin n, KWEdgesNonincident i j →
      ∀ x ∈ polygon.closedEdge i, ∀ y ∈ polygon.closedEdge j,
        edgeRadius < dist x y)
    (hepsVertex : 2 * eps < vertexRadius)
    (hepsEdge : 2 * eps < edgeRadius)
    (hcross : ∀ i : Fin n,
      kwComplexCross (kwRawEdge vertex i)
        (kwRawEdge vertex (i + 1)) ≠ 0) :
    KWRawSimplePolygonData vertex := by
  refine ⟨polygon.three_le, ?_, hcross, ?_⟩
  · intro i j heq
    by_contra hij
    have hsep := hvertexSep i j hij
    have htri : dist (polygon.vertex i) (polygon.vertex j) ≤
        dist (polygon.vertex i) (vertex i) +
          dist (vertex i) (polygon.vertex j) := dist_triangle _ _ _
    have htri' : dist (vertex i) (polygon.vertex j) ≤
        dist (vertex i) (vertex j) +
          dist (vertex j) (polygon.vertex j) := dist_triangle _ _ _
    have hi : dist (polygon.vertex i) (vertex i) ≤ eps := by
      simpa only [dist_comm] using hvertex i
    have hj := hvertex j
    have hzero : dist (vertex i) (vertex j) = 0 := by rw [heq, dist_self]
    linarith
  · intro i j hij
    exact segment_disjoint_of_perturbation
      (hvertex i) (hvertex (i + 1))
      (hvertex j) (hvertex (j + 1))
      (hedgeSep i j hij) hepsEdge


end StatMech.FrontierA
