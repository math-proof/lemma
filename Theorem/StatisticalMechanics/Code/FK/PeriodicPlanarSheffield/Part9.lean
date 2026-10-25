/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part9
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicPlaneEmbedding.finiteHorizontalCrossing_isIncreasing
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    IsIncreasing (E.finiteHorizontalCrossing a b c d) := by
  intro eta theta hle
  rintro ⟨x, y, hx, hy, hreach⟩
  refine ⟨x, y, hx, hy, hreach.mono ?_⟩
  intro u v huv
  rw [FK.openSub_adj] at huv ⊢
  refine ⟨huv.1, Bool.eq_true_of_true_le ?_⟩
  simpa [huv.2] using hle s(u, v)

theorem PeriodicPlaneEmbedding.rectRestrict_mono
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    Monotone (E.rectRestrict a b c d) := by
  intro omega eta hle e
  exact hle (Sym2.map Subtype.val e)

theorem PeriodicPlaneEmbedding.horizontalCrossingEvent_isIncreasing
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    IsIncreasing (E.horizontalCrossingEvent a b c d) := by
  intro omega eta hle homega
  exact E.finiteHorizontalCrossing_isIncreasing a b c d
    (E.rectRestrict_mono a b c d hle) homega

theorem PeriodicPlaneEmbedding.horizontalCrossingEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    MeasurableSet (E.horizontalCrossingEvent a b c d) :=
  (IsClopen.preimage ⟨isClosed_discrete _, isOpen_discrete _⟩
    (E.continuous_rectRestrict a b c d)).isOpen.measurableSet


theorem PeriodicPlaneEmbedding.finiteHorizontalCrossing_embeddedPath
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {a b c d : ℝ} {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
    (heta : eta ∈ E.finiteHorizontalCrossing a b c d) :
    ∃ x y : E.RectVertex a b c d,
      E.rectLeftBoundary a b c d x ∧ E.rectRightBoundary a b c d y ∧
      ∃ gamma : Path (E.vertex x.1) (E.vertex y.1),
        Set.range gamma ⊆
          E.planeRect (a - B) (b + B) (c - B) (d + B) := by
  rcases heta with ⟨x, y, hx, hy, hreach⟩
  obtain ⟨p⟩ := hreach
  refine ⟨x, y, hx, hy,
    E.walkArc (p.map (E.openRectHom a b c d eta)), ?_⟩
  exact E.openRectWalkArc_range_subset hB0 hB p


theorem PeriodicPlaneEmbedding.finiteHorizontalCrossing_openWalk_of_wide
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {a b c d : ℝ} (hwide : a + B ≤ b - B)
    {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
    (heta : eta ∈ E.finiteHorizontalCrossing a b c d) :
    ∃ x y : E.RectVertex a b c d,
      E.rectLeftBoundary a b c d x ∧ E.rectRightBoundary a b c d y ∧
      ∃ p : (FK.openSub (E.rectGraph a b c d) eta).Walk x y,
        ¬ (p.map (E.openRectHom a b c d eta)).Nil := by
  rcases heta with ⟨x, y, hx, hy, hreach⟩
  obtain ⟨p⟩ := hreach
  have hxcoord := E.rectLeftBoundary_coord_lt hB hx
  have hycoord := E.rectRightBoundary_coord_gt hB hy
  have hxy : x.1 ≠ y.1 := by
    intro heq
    rw [heq] at hxcoord
    linarith
  exact ⟨x, y, hx, hy, p, SimpleGraph.Walk.not_nil_of_ne hxy⟩


theorem PeriodicPlaneEmbedding.finiteHorizontalCrossing_extendedPath
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {a b c d : ℝ} {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
    (heta : eta ∈ E.finiteHorizontalCrossing a b c d) :
    ∃ xl xr : V, ∃ gamma : Path (E.vertex xl) (E.vertex xr),
      E.vertexCoord xl 0 < a ∧ b < E.vertexCoord xr 0 ∧
      Set.range gamma ⊆
        E.planeRect (a - B) (b + B) (c - B) (d + B) := by
  obtain ⟨x, y, hx, hy, gamma, hgamma⟩ :=
    E.finiteHorizontalCrossing_embeddedPath hB0 hB heta
  obtain ⟨xl, hxl, hxlcoord⟩ := hx
  obtain ⟨xr, hxr, hxrcoord⟩ := hy
  let gamma' := (E.edgeArc hxl).symm.trans (gamma.trans (E.edgeArc hxr))
  refine ⟨xl, xr, gamma', hxlcoord, hxrcoord, ?_⟩
  intro q hq
  simp only [gamma', Path.trans_range, Set.mem_union] at hq
  rcases hq with hq | hq | hq
  · rw [Path.symm_range] at hq
    obtain ⟨t, rfl⟩ := hq
    exact E.edgeArc_mem_expanded_planeRect hB hxl (by exact x.2) t
  · exact hgamma hq
  · obtain ⟨t, rfl⟩ := hq
    exact E.edgeArc_mem_expanded_planeRect hB hxr (by exact y.2) t


end StatMech.FK.PeriodicPlanar
