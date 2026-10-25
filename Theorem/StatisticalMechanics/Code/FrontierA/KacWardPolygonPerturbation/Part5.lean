/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGenericPolygonReduction
import Structure.StatisticalMechanics.Code.FrontierA.KacWardPolygonPerturbation.Part2


namespace StatMech.FrontierA

open scoped Convex

open Set

theorem KWFiniteSimplePolygon.exists_perturbationCertificate
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i)
      (polygon.edgeVector (i + 1)) ≠ 0) :
    Nonempty (KWPolygonPerturbationCertificate polygon) := by
  obtain ⟨crossRadius, hcrossRadius, hcrossStable⟩ :=
    exists_cross_stability_radius polygon.vertex (by
      simpa only [kwRawEdge, KWFiniteSimplePolygon.edgeVector] using hcross)
  obtain ⟨vertexRadius, hvertexRadius, hvertexSep⟩ :=
    polygon.exists_uniform_vertex_separation
  obtain ⟨edgeRadius, hedgeRadius, hedgeSep⟩ :=
    polygon.exists_uniform_nonincident_edge_dist_separation
  let eps : ℝ := min (crossRadius / 2)
    (min ((vertexRadius : ℝ) / 4) ((edgeRadius : ℝ) / 4))
  have heps : 0 < eps := by
    dsimp only [eps]
    exact lt_min (half_pos hcrossRadius)
      (lt_min (by positivity) (by positivity))
  refine ⟨{
    radius := eps
    radius_pos := heps
    rawSimple := ?_ }⟩
  intro vertex hvertex
  have hpoint (i : Fin n) :
      dist (vertex i) (polygon.vertex i) < eps :=
    (dist_pi_lt_iff heps).mp hvertex i
  have hinjective : Function.Injective vertex := by
    intro i j heq
    by_contra hij
    have hsep := hvertexSep i j hij
    have htri := dist_triangle (polygon.vertex i) (vertex i)
      (polygon.vertex j)
    rw [heq] at htri
    have hepsVertex : eps ≤ (vertexRadius : ℝ) / 4 := by
      dsimp only [eps]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hpath : dist (polygon.vertex i) (polygon.vertex j) <
        (vertexRadius : ℝ) / 2 := by
      calc
        dist (polygon.vertex i) (polygon.vertex j) ≤
            dist (polygon.vertex i) (vertex j) +
              dist (vertex j) (polygon.vertex j) := htri
        _ < eps + eps := add_lt_add (by
              simpa only [heq, dist_comm] using hpoint i) (hpoint j)
        _ ≤ (vertexRadius : ℝ) / 2 := by linarith
    linarith
  have hcross' : ∀ i : Fin n,
      kwComplexCross (kwRawEdge vertex i)
        (kwRawEdge vertex (i + 1)) ≠ 0 := by
    apply hcrossStable vertex
    exact hvertex.trans_le (by
      dsimp only [eps]
      have hhalf : crossRadius / 2 ≤ crossRadius := by linarith
      exact (min_le_left _ _).trans hhalf)
  have hnonincident : ∀ i j : Fin n, KWEdgesNonincident i j →
      Disjoint (kwRawClosedEdge vertex i)
        (kwRawClosedEdge vertex j) := by
    intro i j hij
    apply segment_disjoint_of_perturbation
      (le_of_lt (hpoint i)) (le_of_lt (hpoint (i + 1)))
      (le_of_lt (hpoint j)) (le_of_lt (hpoint (j + 1)))
      (hedgeSep i j hij)
    have hepsEdge : eps ≤ (edgeRadius : ℝ) / 4 := by
      dsimp only [eps]
      exact (min_le_right _ _).trans (min_le_right _ _)
    linarith
  exact {
    three_le := polygon.three_le
    vertex_injective := hinjective
    cross_ne_zero := hcross'
    nonincident_disjoint := hnonincident }


theorem KWFiniteSimplePolygon.exists_close_rational_polygon
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hcross : ∀ i : Fin n, kwComplexCross (polygon.edgeVector i)
      (polygon.edgeVector (i + 1)) ≠ 0) :
    ∃ (q : Fin n → ℚ × ℚ) (rational : KWFiniteSimplePolygon n),
      rational.vertex = kwRatVertex q ∧
      (∀ i : Fin n, dist (rational.vertex i) (polygon.vertex i) < 1) := by
  obtain ⟨crossRadius, hcrossRadius, hcrossStable⟩ :=
    exists_cross_stability_radius polygon.vertex (by
      simpa only [kwRawEdge, KWFiniteSimplePolygon.edgeVector] using hcross)
  obtain ⟨vertexRadius, hvertexRadius, hvertexSep⟩ :=
    polygon.exists_uniform_vertex_separation
  obtain ⟨edgeRadius, hedgeRadius, hedgeSep⟩ :=
    polygon.exists_uniform_nonincident_edge_dist_separation
  let eps : ℝ := min (1 / 2 : ℝ)
    (min (crossRadius / 2)
      (min ((vertexRadius : ℝ) / 4) ((edgeRadius : ℝ) / 4)))
  have heps : 0 < eps := by
    dsimp only [eps]
    exact lt_min (by norm_num) (lt_min (half_pos hcrossRadius)
      (lt_min (by positivity) (by positivity)))
  obtain ⟨q, hq⟩ := (denseRange_kwRatVertex (n := n)).exists_mem_open
    (s := Metric.ball polygon.vertex eps) Metric.isOpen_ball
    (Metric.nonempty_ball.mpr heps)
  have hqdist : dist (kwRatVertex q) polygon.vertex < eps := by
    simpa only [Metric.mem_ball] using hq
  have hqpoint (i : Fin n) :
      dist (kwRatVertex q i) (polygon.vertex i) < eps :=
    (dist_pi_lt_iff heps).mp hqdist i
  have hqinjective : Function.Injective (kwRatVertex q) := by
    intro i j heq
    by_contra hij
    have hsep := hvertexSep i j hij
    have htri := dist_triangle (polygon.vertex i) (kwRatVertex q i)
      (polygon.vertex j)
    rw [heq] at htri
    have hcloseJ := hqpoint j
    have hepsVertex : eps ≤ (vertexRadius : ℝ) / 4 := by
      dsimp only [eps]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (min_le_left _ _))
    have hpath : dist (polygon.vertex i) (polygon.vertex j) <
        (vertexRadius : ℝ) / 2 := by
      calc
        dist (polygon.vertex i) (polygon.vertex j) ≤
            dist (polygon.vertex i) (kwRatVertex q j) +
              dist (kwRatVertex q j) (polygon.vertex j) := htri
        _ < eps + eps := add_lt_add (by
              simpa only [heq, dist_comm] using hqpoint i) hcloseJ
        _ ≤ (vertexRadius : ℝ) / 2 := by linarith
    linarith
  have hqcross : ∀ i : Fin n,
      kwComplexCross (kwRawEdge (kwRatVertex q) i)
        (kwRawEdge (kwRatVertex q) (i + 1)) ≠ 0 := by
    apply hcrossStable (kwRatVertex q)
    exact hqdist.trans_le (by
      dsimp only [eps]
      have hhalf : crossRadius / 2 ≤ crossRadius := by linarith
      exact (min_le_right _ _).trans ((min_le_left _ _).trans hhalf))
  have hqnonincident : ∀ i j : Fin n, KWEdgesNonincident i j →
      Disjoint (kwRawClosedEdge (kwRatVertex q) i)
        (kwRawClosedEdge (kwRatVertex q) j) := by
    intro i j hij
    apply segment_disjoint_of_perturbation
      (le_of_lt (hqpoint i)) (le_of_lt (hqpoint (i + 1)))
      (le_of_lt (hqpoint j)) (le_of_lt (hqpoint (j + 1)))
      (hedgeSep i j hij)
    have hepsEdge : eps ≤ (edgeRadius : ℝ) / 4 := by
      dsimp only [eps]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (min_le_right _ _))
    linarith
  let data : KWRawSimplePolygonData (kwRatVertex q) :=
    { three_le := polygon.three_le
      vertex_injective := hqinjective
      cross_ne_zero := hqcross
      nonincident_disjoint := hqnonincident }
  let rational := data.toFiniteSimplePolygon
  refine ⟨q, rational, rfl, ?_⟩
  intro i
  exact (hqpoint i).trans_le (by
    dsimp only [eps]
    exact (min_le_left _ _).trans (by norm_num))

end StatMech.FrontierA
