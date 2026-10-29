/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Mathlib.Analysis.Convex.StrictConvexSpace
import Def.StatisticalMechanics.Code.FrontierA.KacWardAngularPortGeometry


namespace StatMech.FrontierA

open Set SimpleGraph

open scoped NNReal ENNReal


theorem KWStraightLineEmbedding.dartClosedEdge_isCompact
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) :
    IsCompact (embedding.dartClosedEdge d) := by
  rw [KWStraightLineEmbedding.dartClosedEdge, segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

theorem KWStraightLineEmbedding.dartClosedEdge_isClosed
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) :
    IsClosed (embedding.dartClosedEdge d) :=
  (embedding.dartClosedEdge_isCompact d).isClosed

theorem KWStraightLineEmbedding.vertex_not_mem_dartClosedEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (v : V) (d : G.Dart)
    (hvfst : v ≠ d.fst) (hvsnd : v ≠ d.snd) :
    embedding.vertex v ∉ embedding.dartClosedEdge d := by
  intro hmem
  have hbetween : Wbtw ℝ (embedding.vertex d.fst) (embedding.vertex v)
      (embedding.vertex d.snd) := mem_segment_iff_wbtw.mp hmem
  exact embedding.vertex_not_strictly_between d v hvfst hvsnd
    ⟨hbetween, embedding.vertex_injective.ne hvfst,
      embedding.vertex_injective.ne hvsnd⟩

theorem KWStraightLineEmbedding.singleton_vertex_disjoint_dartClosedEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (v : V) (d : G.Dart)
    (hvfst : v ≠ d.fst) (hvsnd : v ≠ d.snd) :
    Disjoint ({embedding.vertex v} : Set ℂ) (embedding.dartClosedEdge d) :=
  Set.disjoint_singleton_left.mpr
    (embedding.vertex_not_mem_dartClosedEdge v d hvfst hvsnd)

theorem kw_exists_uniform_nnreal_finset
    {α : Type*} (s : Finset α) (Q : α → NNReal → Prop)
    (hQ : ∀ a ∈ s, ∃ r : NNReal, 0 < r ∧ Q a r)
    (hmono : ∀ a ∈ s, ∀ {r r' : NNReal}, r' ≤ r → Q a r → Q a r') :
    ∃ r : NNReal, 0 < r ∧ ∀ a ∈ s, Q a r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨ra, hra, hQa⟩ := hQ a (by simp)
      obtain ⟨rs, hrs, hQs⟩ := ih
        (fun b hb ↦ hQ b (by simp [hb]))
        (fun b hb r r' hle h ↦ hmono b (by simp [hb]) hle h)
      refine ⟨min ra rs, lt_min hra hrs, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hbs
      · exact hmono _ (by simp) (min_le_left _ _) hQa
      · exact hmono b (by simp [hbs]) (min_le_right _ _) (hQs b hbs)

theorem KWStraightLineEmbedding.exists_uniform_vertex_separation
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    ∃ r : NNReal, 0 < r ∧ ∀ v w : V, v ≠ w →
      (r : ℝ) < dist (embedding.vertex v) (embedding.vertex w) := by
  classical
  let pairs : Finset (V × V) :=
    Finset.univ.filter (fun p ↦ p.1 ≠ p.2)
  let Q : (V × V) → NNReal → Prop := fun p r ↦
    (r : ENNReal) < edist (embedding.vertex p.1) (embedding.vertex p.2)
  have hpair : ∀ p ∈ pairs, ∃ r : NNReal, 0 < r ∧ Q p r := by
    intro p hp
    have hne : p.1 ≠ p.2 := by
      simpa only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] using hp
    obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist
      (s := {embedding.vertex p.1}) (t := {embedding.vertex p.2})
      isCompact_singleton isClosed_singleton
      (Set.disjoint_singleton.mpr (embedding.vertex_injective.ne hne))
    refine ⟨r, hr, ?_⟩
    simpa [Q] using
      hsep (embedding.vertex p.1) rfl (embedding.vertex p.2) rfl
  have hmono : ∀ p ∈ pairs, ∀ {r r' : NNReal},
      r' ≤ r → Q p r → Q p r' := by
    intro p _ r r' hle h
    exact (ENNReal.coe_le_coe.mpr hle).trans_lt h
  obtain ⟨r, hr, hruniform⟩ :=
    kw_exists_uniform_nnreal_finset pairs Q hpair hmono
  refine ⟨r, hr, ?_⟩
  intro v w hvw
  have h := hruniform (v, w) (by simp [pairs, hvw])
  dsimp only [Q] at h
  rw [edist_dist] at h
  exact ENNReal.coe_lt_ofReal.mp h

theorem KWStraightLineEmbedding.exists_uniform_edge_length
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    ∃ r : NNReal, 0 < r ∧ ∀ d : G.Dart,
      (r : ℝ) < ‖embedding.vertex d.snd - embedding.vertex d.fst‖ := by
  classical
  let Q : G.Dart → NNReal → Prop := fun d r ↦
    (r : ℝ) < ‖embedding.vertex d.snd - embedding.vertex d.fst‖
  have hQ : ∀ d ∈ (Finset.univ : Finset G.Dart),
      ∃ r : NNReal, 0 < r ∧ Q d r := by
    intro d _
    let length : ℝ := ‖embedding.vertex d.snd - embedding.vertex d.fst‖
    have hlength : 0 < length := norm_pos_iff.mpr (embedding.dartVector_ne_zero d)
    let r : NNReal := ⟨length / 2, by positivity⟩
    refine ⟨r, ?_, ?_⟩
    · exact_mod_cast half_pos hlength
    · change length / 2 < length
      linarith
  have hmono : ∀ d ∈ (Finset.univ : Finset G.Dart), ∀ {r r' : NNReal},
      r' ≤ r → Q d r → Q d r' := by
    intro d _ r r' hle h
    have hle' : (r' : ℝ) ≤ (r : ℝ) := by exact_mod_cast hle
    exact hle'.trans_lt h
  obtain ⟨r, hr, hall⟩ := kw_exists_uniform_nnreal_finset
    (Finset.univ : Finset G.Dart) Q hQ hmono
  exact ⟨r, hr, fun d ↦ hall d (Finset.mem_univ d)⟩

theorem KWStraightLineEmbedding.exists_uniform_vertex_edge_separation
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    ∃ r : NNReal, 0 < r ∧
      ∀ (v : V) (d : G.Dart), v ≠ d.fst → v ≠ d.snd →
        ∀ y ∈ embedding.dartClosedEdge d,
          (r : ℝ) < dist (embedding.vertex v) y := by
  classical
  let pairs : Finset (V × G.Dart) := Finset.univ.filter
    (fun p ↦ p.1 ≠ p.2.fst ∧ p.1 ≠ p.2.snd)
  let Q : (V × G.Dart) → NNReal → Prop := fun p r ↦
    ∀ y ∈ embedding.dartClosedEdge p.2,
      (r : ENNReal) < edist (embedding.vertex p.1) y
  have hpair : ∀ p ∈ pairs, ∃ r : NNReal, 0 < r ∧ Q p r := by
    intro p hp
    have hnon : p.1 ≠ p.2.fst ∧ p.1 ≠ p.2.snd := by
      simpa only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] using hp
    obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist
      (s := {embedding.vertex p.1}) (t := embedding.dartClosedEdge p.2)
      isCompact_singleton (embedding.dartClosedEdge_isClosed p.2)
      (embedding.singleton_vertex_disjoint_dartClosedEdge
        p.1 p.2 hnon.1 hnon.2)
    exact ⟨r, hr, fun y hy ↦ hsep (embedding.vertex p.1) rfl y hy⟩
  have hmono : ∀ p ∈ pairs, ∀ {r r' : NNReal},
      r' ≤ r → Q p r → Q p r' := by
    intro p _ r r' hle h y hy
    exact (ENNReal.coe_le_coe.mpr hle).trans_lt (h y hy)
  obtain ⟨r, hr, hall⟩ :=
    kw_exists_uniform_nnreal_finset pairs Q hpair hmono
  refine ⟨r, hr, ?_⟩
  intro v d hvfst hvsnd y hy
  have h := hall (v, d) (by simp [pairs, hvfst, hvsnd]) y hy
  rw [edist_dist] at h
  exact ENNReal.coe_lt_ofReal.mp h


end StatMech.FrontierA
