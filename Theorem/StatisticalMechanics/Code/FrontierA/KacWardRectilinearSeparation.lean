/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearHomotopyReduction.Part2
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Instance.StatisticalMechanics.Code.FrontierA.KacWardRectilinearSeparation


namespace StatMech.FrontierA

open scoped Convex Pointwise

open scoped NNReal ENNReal

open Set


theorem KWEdgesNonincident.symm
    {n : ℕ} [NeZero n] {i j : Fin n}
    (h : KWEdgesNonincident i j) : KWEdgesNonincident j i := by
  rcases h with ⟨hij, hijs, hisj⟩
  refine ⟨hij.symm, hisj.symm, ?_⟩
  intro hsucc
  exact hijs hsucc.symm

theorem KWEdgesNonincident.succ_ne_succ
    {n : ℕ} [NeZero n] {i j : Fin n}
    (h : KWEdgesNonincident i j) : i + 1 ≠ j + 1 := by
  intro hsucc
  exact h.1 (add_right_cancel hsucc)

theorem KWFiniteSimplePolygon.closedEdge_isCompact
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i : Fin n) : IsCompact (polygon.closedEdge i) := by
  rw [KWFiniteSimplePolygon.closedEdge, segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

theorem KWFiniteSimplePolygon.closedEdge_isClosed
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i : Fin n) : IsClosed (polygon.closedEdge i) :=
  (polygon.closedEdge_isCompact i).isClosed


theorem KWFiniteSimplePolygon.closedEdge_disjoint_of_nonincident
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {i j : Fin n} (hij : KWEdgesNonincident i j) :
    Disjoint (polygon.closedEdge i) (polygon.closedEdge j) := by
  rw [Set.disjoint_left]
  intro z hzi hzj
  have hi_ne_j : i ≠ j := hij.1
  have hi_ne_js : i ≠ j + 1 := hij.2.1
  have his_ne_j : i + 1 ≠ j := hij.2.2
  have his_ne_js : i + 1 ≠ j + 1 := hij.succ_ne_succ
  by_cases hzi0 : z = polygon.vertex i
  · subst z
    have hs : Sbtw ℝ (polygon.vertex j) (polygon.vertex i)
        (polygon.vertex (j + 1)) := by
      refine ⟨(mem_segment_iff_wbtw.mp hzj), ?_, ?_⟩
      · exact polygon.vertex_injective.ne hi_ne_j
      · exact polygon.vertex_injective.ne hi_ne_js
    exact polygon.vertex_not_strictly_between j i hi_ne_j hi_ne_js hs
  by_cases hzi1 : z = polygon.vertex (i + 1)
  · subst z
    have hs : Sbtw ℝ (polygon.vertex j) (polygon.vertex (i + 1))
        (polygon.vertex (j + 1)) := by
      refine ⟨(mem_segment_iff_wbtw.mp hzj), ?_, ?_⟩
      · exact polygon.vertex_injective.ne his_ne_j
      · exact polygon.vertex_injective.ne his_ne_js
    exact polygon.vertex_not_strictly_between j (i + 1)
      his_ne_j his_ne_js hs
  have hszi : Sbtw ℝ (polygon.vertex i) z (polygon.vertex (i + 1)) := by
    exact ⟨mem_segment_iff_wbtw.mp hzi, hzi0, hzi1⟩
  by_cases hzj0 : z = polygon.vertex j
  · subst z
    exact polygon.vertex_not_strictly_between i j hi_ne_j.symm
      his_ne_j.symm hszi
  by_cases hzj1 : z = polygon.vertex (j + 1)
  · subst z
    exact polygon.vertex_not_strictly_between i (j + 1) hi_ne_js.symm
      his_ne_js.symm hszi
  have hszj : Sbtw ℝ (polygon.vertex j) z (polygon.vertex (j + 1)) := by
    exact ⟨mem_segment_iff_wbtw.mp hzj, hzj0, hzj1⟩
  exact Set.disjoint_left.mp (polygon.edgeInteriors_disjoint i j hi_ne_j)
    hszi hszj


theorem exists_uniform_radius_finset
    {ι : Type*} (s : Finset ι) (Q : ι → ℝ≥0 → Prop)
    (hQ : ∀ i ∈ s, ∃ r : ℝ≥0, 0 < r ∧ Q i r)
    (hmono : ∀ i ∈ s, ∀ {r r' : ℝ≥0}, r' ≤ r → Q i r → Q i r') :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ i ∈ s, Q i r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨1, by norm_num, by simp⟩
  | @insert j s hj ih =>
      obtain ⟨ri, hri, hQi⟩ := hQ j (by simp)
      obtain ⟨rs, hrs, hQs⟩ := ih
        (fun j hj ↦ hQ j (by simp [hj]))
        (fun j hj r r' hle h ↦ hmono j (by simp [hj]) hle h)
      refine ⟨min ri rs, lt_min hri hrs, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hks
      · exact hmono _ (by simp) (min_le_left _ _) hQi
      · exact hmono k (by simp [hks]) (min_le_right _ _) (hQs k hks)


theorem KWFiniteSimplePolygon.exists_uniform_vertex_separation
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ i j : Fin n, i ≠ j →
      (r : ℝ) < dist (polygon.vertex i) (polygon.vertex j) := by
  classical
  let pairs : Finset (Fin n × Fin n) :=
    Finset.univ.filter (fun p ↦ p.1 ≠ p.2)
  let Q : (Fin n × Fin n) → ℝ≥0 → Prop := fun p r ↦
    (r : ℝ≥0∞) < edist (polygon.vertex p.1) (polygon.vertex p.2)
  have hpair : ∀ p ∈ pairs, ∃ r : ℝ≥0, 0 < r ∧ Q p r := by
    intro p hp
    have hne : p.1 ≠ p.2 := by
      simpa only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] using hp
    obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist
      (s := {polygon.vertex p.1}) (t := {polygon.vertex p.2})
      isCompact_singleton isClosed_singleton
      (Set.disjoint_singleton.mpr (polygon.vertex_injective.ne hne))
    have hp := hsep (polygon.vertex p.1) rfl
      (polygon.vertex p.2) rfl
    exact ⟨r, hr, by simpa using hp⟩
  have hmono : ∀ p ∈ pairs, ∀ {r r' : ℝ≥0},
      r' ≤ r → Q p r → Q p r' := by
    intro p _ r r' hle h
    exact (ENNReal.coe_le_coe.mpr hle).trans_lt h
  obtain ⟨r, hr, hruniform⟩ :=
    exists_uniform_radius_finset pairs Q hpair hmono
  refine ⟨r, hr, ?_⟩
  intro i j hij
  have h := hruniform (i, j) (by simp [pairs, hij])
  dsimp only [Q] at h
  rw [edist_dist] at h
  exact ENNReal.coe_lt_ofReal.mp h


theorem KWFiniteSimplePolygon.exists_uniform_nonincident_edge_separation
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    ∃ r : ℝ≥0, 0 < r ∧
      ∀ i j : Fin n, KWEdgesNonincident i j →
        ∀ x ∈ polygon.closedEdge i, ∀ y ∈ polygon.closedEdge j,
          (r : ℝ≥0∞) < edist x y := by
  classical
  let pairs : Finset (Fin n × Fin n) :=
    Finset.univ.filter (fun p ↦ KWEdgesNonincident p.1 p.2)
  let Q : (Fin n × Fin n) → ℝ≥0 → Prop := fun p r ↦
    ∀ x ∈ polygon.closedEdge p.1, ∀ y ∈ polygon.closedEdge p.2,
      (r : ℝ≥0∞) < edist x y
  have hpair : ∀ p ∈ pairs, ∃ r : ℝ≥0, 0 < r ∧ Q p r := by
    intro p hp
    have hnon : KWEdgesNonincident p.1 p.2 := by
      simpa only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] using hp
    exact Metric.exists_pos_forall_lt_edist
      (polygon.closedEdge_isCompact p.1)
      (polygon.closedEdge_isClosed p.2)
      (polygon.closedEdge_disjoint_of_nonincident hnon)
  have hmono : ∀ p ∈ pairs, ∀ {r r' : ℝ≥0}, r' ≤ r → Q p r → Q p r' := by
    intro p _ r r' hle h x hx y hy
    exact (ENNReal.coe_le_coe.mpr hle).trans_lt (h x hx y hy)
  obtain ⟨r, hr, hruniform⟩ :=
    exists_uniform_radius_finset pairs Q hpair hmono
  refine ⟨r, hr, ?_⟩
  intro i j hij x hx y hy
  apply hruniform (i, j)
  · simp only [pairs, Finset.mem_filter, Finset.mem_univ, hij, and_self]
  · exact hx
  · exact hy


theorem KWFiniteSimplePolygon.exists_uniform_nonincident_edge_dist_separation
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    ∃ r : ℝ≥0, 0 < r ∧
      ∀ i j : Fin n, KWEdgesNonincident i j →
        ∀ x ∈ polygon.closedEdge i, ∀ y ∈ polygon.closedEdge j,
          (r : ℝ) < dist x y := by
  obtain ⟨r, hr, hsep⟩ := polygon.exists_uniform_nonincident_edge_separation
  refine ⟨r, hr, ?_⟩
  intro i j hij x hx y hy
  have h := hsep i j hij x hx y hy
  rw [edist_dist] at h
  exact ENNReal.coe_lt_ofReal.mp h


end StatMech.FrontierA
