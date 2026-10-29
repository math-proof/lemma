/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearHomotopyReduction.Part2
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Def.StatisticalMechanics.Code.FrontierA.KacWardRectilinearSeparation.Part2


namespace StatMech.FrontierA

open scoped Convex Pointwise

open scoped NNReal ENNReal

open Set


theorem KWFiniteSimplePolygon.closedEdgeTube_eq_add_ball
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (r : NNReal) (i : Fin n) :
    polygon.closedEdgeTube r i =
      polygon.closedEdge i + Metric.ball (0 : ℂ) (r : ℝ) := by
  ext z
  constructor
  · rintro ⟨x, hx, hzx⟩
    apply Set.mem_add.mpr
    refine ⟨x, hx, z - x, ?_, by ring⟩
    rw [mem_ball_zero_iff, ← dist_eq_norm]
    exact hzx
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hz
    refine ⟨x, hx, ?_⟩
    rw [dist_eq_norm, add_sub_cancel_left, ← mem_ball_zero_iff]
    exact hy


theorem KWFiniteSimplePolygon.closedEdgeTube_convex
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (r : NNReal) (i : Fin n) :
    Convex ℝ (polygon.closedEdgeTube r i) := by
  rw [polygon.closedEdgeTube_eq_add_ball]
  exact (convex_segment _ _).add (convex_ball (0 : ℂ) (r : ℝ))

theorem KWFiniteSimplePolygon.closedEdge_subset_closedEdgeTube
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {r : NNReal} (hr : 0 < r) (i : Fin n) :
    polygon.closedEdge i ⊆ polygon.closedEdgeTube r i := by
  intro x hx
  exact ⟨x, hx, by simpa using hr⟩


theorem KWFiniteSimplePolygon.closedEdgeTube_disjoint_of_nonincident
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {r : NNReal}
    (hsep : ∀ i j : Fin n, KWEdgesNonincident i j →
      ∀ x ∈ polygon.closedEdge i, ∀ y ∈ polygon.closedEdge j,
        (r : ℝ) < dist x y)
    {i j : Fin n} (hij : KWEdgesNonincident i j) :
    Disjoint (polygon.closedEdgeTube (r / 2) i)
      (polygon.closedEdgeTube (r / 2) j) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, hzx⟩ ⟨y, hy, hzy⟩
  have hxy : (r : ℝ) < dist x y := hsep i j hij x hx y hy
  have hxz : dist x z < (r : ℝ) / 2 := by
    simpa only [dist_comm x z, NNReal.coe_div, NNReal.coe_ofNat] using hzx
  have hzy' : dist z y < (r : ℝ) / 2 := by
    simpa only [NNReal.coe_div, NNReal.coe_ofNat] using hzy
  have htriangle : dist x y ≤ dist x z + dist z y := dist_triangle x z y
  linarith


theorem KWFiniteSimplePolygon.exists_pairwise_disjoint_nonincident_edgeTubes
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    ∃ r : NNReal, 0 < r ∧
      ∀ i j : Fin n, KWEdgesNonincident i j →
        Disjoint (polygon.closedEdgeTube (r / 2) i)
          (polygon.closedEdgeTube (r / 2) j) := by
  obtain ⟨r, hr, hsep⟩ :=
    polygon.exists_uniform_nonincident_edge_dist_separation
  exact ⟨r, hr, fun _ _ hij ↦
    polygon.closedEdgeTube_disjoint_of_nonincident hsep hij⟩

end StatMech.FrontierA
