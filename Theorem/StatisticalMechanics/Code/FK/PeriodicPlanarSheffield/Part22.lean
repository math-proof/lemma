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
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part22
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


namespace PeriodicPlanarDualPair

theorem dualMeasure_isTranslationInvariant
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) :
    Pdual.IsTranslationInvariant (D.dualMeasure mu) := by
  intro z
  refine MeasurePreserving.mk (Pdual.measurable_configTranslate z) ?_
  unfold dualMeasure
  rw [Measure.map_map (Pdual.measurable_configTranslate z)
    (continuous_dualConfigEquiv D.edgeDual).measurable]
  have hcomp : Pdual.configTranslate z ∘ dualConfigEquiv D.edgeDual =
      dualConfigEquiv D.edgeDual ∘ P.configTranslate z := by
    funext omega
    exact (D.dualConfigEquiv_configTranslate z omega).symm
  rw [hcomp, ← Measure.map_map
    (continuous_dualConfigEquiv D.edgeDual).measurable
    (P.measurable_configTranslate z), (hTI z).map_eq]


theorem no_open_primal_dual_edge_crossing
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {x y : V} {a b : W}
    (hxy : P.graph.Adj x y) (hab : Pdual.graph.Adj a b)
    (hopen : omega s(x, y) = true)
    (hdualOpen : dualConfigEquiv D.edgeDual omega s(a, b) = true)
    {t u} (hcross : D.primalEmbedding.edgeArc hxy t =
      D.dualEmbedding.edgeArc hab u) : False := by
  have hedge := D.edgeDual_of_crossing hxy hab t u hcross
  have hinv : D.edgeDual.symm s(a, b) = s(x, y) := by
    rw [← hedge]
    simp
  simp only [dualConfigEquiv_apply, hinv, hopen, Bool.not_true] at hdualOpen
  exact Bool.false_ne_true hdualOpen


theorem no_open_primal_dual_walkArc_crossing
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {x y : V} {a b : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk a b)
    (hp : ¬ p.Nil) (hq : ¬ q.Nil)
    (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges →
      omega s(u, v) = true)
    (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges →
      dualConfigEquiv D.edgeDual omega s(u, v) = true) :
    Disjoint (Set.range (D.primalEmbedding.walkArc p))
      (Set.range (D.dualEmbedding.walkArc q)) := by
  rw [Set.disjoint_left]
  intro z hzp hzd
  obtain ⟨u, v, huv, huvEdge, huvArc⟩ :=
    D.primalEmbedding.mem_walkArc_range_of_not_nil p hp hzp
  obtain ⟨r, s, hrs, hrsEdge, hrsArc⟩ :=
    D.dualEmbedding.mem_walkArc_range_of_not_nil q hq hzd
  obtain ⟨t, ht⟩ := huvArc
  obtain ⟨w, hw⟩ := hrsArc
  exact D.no_open_primal_dual_edge_crossing omega huv hrs
    (hpopen huvEdge) (hqopen hrsEdge) (ht.trans hw.symm)


theorem no_openRectWalkArc_crossing
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {ap bp cp dp ad bd cd dd : ℝ}
    {xp yp : D.primalEmbedding.RectVertex ap bp cp dp}
    {xd yd : D.dualEmbedding.RectVertex ad bd cd dd}
    (p : (FK.openSub (D.primalEmbedding.rectGraph ap bp cp dp)
      (D.primalEmbedding.rectRestrict ap bp cp dp omega)).Walk xp yp)
    (q : (FK.openSub (D.dualEmbedding.rectGraph ad bd cd dd)
      (D.dualEmbedding.rectRestrict ad bd cd dd
        (dualConfigEquiv D.edgeDual omega))).Walk xd yd)
    (hp : ¬ (p.map (D.primalEmbedding.openRectHom ap bp cp dp
      (D.primalEmbedding.rectRestrict ap bp cp dp omega))).Nil)
    (hq : ¬ (q.map (D.dualEmbedding.openRectHom ad bd cd dd
      (D.dualEmbedding.rectRestrict ad bd cd dd
        (dualConfigEquiv D.edgeDual omega)))).Nil) :
    Disjoint
      (Set.range (D.primalEmbedding.walkArc
        (p.map (D.primalEmbedding.openRectHom ap bp cp dp
          (D.primalEmbedding.rectRestrict ap bp cp dp omega)))))
      (Set.range (D.dualEmbedding.walkArc
        (q.map (D.dualEmbedding.openRectHom ad bd cd dd
          (D.dualEmbedding.rectRestrict ad bd cd dd
            (dualConfigEquiv D.edgeDual omega)))))) := by
  apply D.no_open_primal_dual_walkArc_crossing omega _ _ hp hq
  · intro u v huv
    exact D.primalEmbedding.openRectWalk_edge_open p huv
  · intro u v huv
    exact D.dualEmbedding.openRectWalk_edge_open q huv


theorem matchedCrossingEvents_disjoint
    (D : PeriodicPlanarDualPair P Pdual) {B a b c d : ℝ}
    (hBpos : 0 < B)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B) :
    Disjoint
      (D.primalEmbedding.horizontalCrossingEvent
        a b (c + 4 * B) (d - 4 * B))
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a + 4 * B) (b - 4 * B) c d) := by
  rw [Set.disjoint_left]
  intro omega hH hV
  change D.primalEmbedding.rectRestrict a b (c + 4 * B) (d - 4 * B) omega ∈
    D.primalEmbedding.finiteHorizontalCrossing
      a b (c + 4 * B) (d - 4 * B) at hH
  change D.dualEmbedding.rectRestrict (a + 4 * B) (b - 4 * B) c d
      (dualConfigEquiv D.edgeDual omega) ∈
    D.dualEmbedding.finiteVerticalCrossing
      (a + 4 * B) (b - 4 * B) c d at hV
  rcases hH with ⟨xp, yp, hxp, hyp, hpReach⟩
  rcases hV with ⟨xd, yd, hxd, hyd, hdReach⟩
  obtain ⟨p⟩ := hpReach
  obtain ⟨q⟩ := hdReach
  obtain ⟨xl, hxl, hxlcoord⟩ := hxp
  obtain ⟨xr, hxr, hxrcoord⟩ := hyp
  obtain ⟨xb, hxb, hxbcoord⟩ := hxd
  obtain ⟨xt, hxt, hxtcoord⟩ := hyd
  let pfull : P.graph.Walk xp.1 yp.1 := p.map (D.primalEmbedding.openRectHom
    a b (c + 4 * B) (d - 4 * B)
      (D.primalEmbedding.rectRestrict
        a b (c + 4 * B) (d - 4 * B) omega))
  let qfull : Pdual.graph.Walk xd.1 yd.1 := q.map (D.dualEmbedding.openRectHom
    (a + 4 * B) (b - 4 * B) c d
      (D.dualEmbedding.rectRestrict (a + 4 * B) (b - 4 * B) c d
        (dualConfigEquiv D.edgeDual omega)))
  let gamma0 := D.primalEmbedding.walkArc pfull
  let eta0 := D.dualEmbedding.walkArc qfull
  let gamma := (D.primalEmbedding.edgeArc hxl).symm.trans
    (gamma0.trans (D.primalEmbedding.edgeArc hxr))
  let eta := (D.dualEmbedding.edgeArc hxb).symm.trans
    (eta0.trans (D.dualEmbedding.edgeArc hxt))
  have hxpNear := D.primalEmbedding.rectLeftBoundary_coord_lt hBp
    (show D.primalEmbedding.rectLeftBoundary
      a b (c + 4 * B) (d - 4 * B) xp from ⟨xl, hxl, hxlcoord⟩)
  have hypNear := D.primalEmbedding.rectRightBoundary_coord_gt hBp
    (show D.primalEmbedding.rectRightBoundary
      a b (c + 4 * B) (d - 4 * B) yp from ⟨xr, hxr, hxrcoord⟩)
  have hxdNear := D.dualEmbedding.rectBottomBoundary_coord_lt hBd
    (show D.dualEmbedding.rectBottomBoundary
      (a + 4 * B) (b - 4 * B) c d xd from ⟨xb, hxb, hxbcoord⟩)
  have hydNear := D.dualEmbedding.rectTopBoundary_coord_gt hBd
    (show D.dualEmbedding.rectTopBoundary
      (a + 4 * B) (b - 4 * B) c d yd from ⟨xt, hxt, hxtcoord⟩)
  have hpNotNil : ¬ pfull.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    change xp.1 ≠ yp.1
    intro heq
    rw [heq] at hxpNear
    linarith
  have hqNotNil : ¬ qfull.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    change xd.1 ≠ yd.1
    intro heq
    rw [heq] at hxdNear
    linarith
  have hgammaRect : Set.range gamma ⊆
      D.primalEmbedding.planeRect
        (a - B) (b + B) ((c + 4 * B) - B) ((d - 4 * B) + B) := by
    intro z hz
    dsimp only [gamma] at hz
    rw [Path.trans_range] at hz
    rcases hz with hleft | hrest
    rw [Path.symm_range] at hleft
    · obtain ⟨t, rfl⟩ := hleft
      exact D.primalEmbedding.edgeArc_mem_expanded_planeRect hBp hxl xp.2 t
    · simp only [Path.trans_range, Set.mem_union] at hrest
      rcases hrest with hcore | hright
      · exact D.primalEmbedding.openRectWalkArc_range_subset
          hBpos.le hBp p hcore
      · obtain ⟨t, rfl⟩ := hright
        exact D.primalEmbedding.edgeArc_mem_expanded_planeRect hBp hxr yp.2 t
  have hetaRectDual : Set.range eta ⊆
      D.dualEmbedding.planeRect
        ((a + 4 * B) - B) ((b - 4 * B) + B) (c - B) (d + B) := by
    intro z hz
    dsimp only [eta] at hz
    rw [Path.trans_range] at hz
    rcases hz with hbottom | hrest
    rw [Path.symm_range] at hbottom
    · obtain ⟨t, rfl⟩ := hbottom
      exact D.dualEmbedding.edgeArc_mem_expanded_planeRect hBd hxb xd.2 t
    · simp only [Path.trans_range, Set.mem_union] at hrest
      rcases hrest with hcore | htop
      · exact D.dualEmbedding.openRectWalkArc_range_subset
          hBpos.le hBd q hcore
      · obtain ⟨t, rfl⟩ := htop
        exact D.dualEmbedding.edgeArc_mem_expanded_planeRect hBd hxt yd.2 t
  let gammaC := gamma.map D.primalEmbedding.coordinates.continuous
  let etaC := eta.map D.primalEmbedding.coordinates.continuous
  have hgammaY : ∀ t : unitInterval,
      c < gammaC t 1 ∧ gammaC t 1 < d := by
    intro t
    have ht := hgammaRect ⟨t, rfl⟩
    change c < D.primalEmbedding.coordinates (gamma t) 1 ∧
      D.primalEmbedding.coordinates (gamma t) 1 < d
    change a - B ≤ D.primalEmbedding.coordinates (gamma t) 0 ∧
      D.primalEmbedding.coordinates (gamma t) 0 ≤ b + B ∧
      (c + 4 * B) - B ≤ D.primalEmbedding.coordinates (gamma t) 1 ∧
      D.primalEmbedding.coordinates (gamma t) 1 ≤ (d - 4 * B) + B at ht
    constructor <;> linarith
  have hetaX : ∀ t : unitInterval,
      a < etaC t 0 ∧ etaC t 0 < b := by
    intro t
    have ht := hetaRectDual ⟨t, rfl⟩
    rw [D.dual_planeRect_eq] at ht
    change a < D.primalEmbedding.coordinates (eta t) 0 ∧
      D.primalEmbedding.coordinates (eta t) 0 < b
    change (a + 4 * B) - B ≤ D.primalEmbedding.coordinates (eta t) 0 ∧
      D.primalEmbedding.coordinates (eta t) 0 ≤ (b - 4 * B) + B ∧
      c - B ≤ D.primalEmbedding.coordinates (eta t) 1 ∧
      D.primalEmbedding.coordinates (eta t) 1 ≤ d + B at ht
    constructor <;> linarith
  have hgammaLeft : D.primalEmbedding.coordinates
      (D.primalEmbedding.vertex xl) 0 < a := by
    change D.primalEmbedding.vertexCoord xl 0 < a
    exact hxlcoord
  have hgammaRight : b < D.primalEmbedding.coordinates
      (D.primalEmbedding.vertex xr) 0 := by
    change b < D.primalEmbedding.vertexCoord xr 0
    exact hxrcoord
  have hetaBottom : D.primalEmbedding.coordinates
      (D.dualEmbedding.vertex xb) 1 < c := by
    change D.primalEmbedding.coordinates (D.dualEmbedding.vertex xb) 1 < c
    rw [D.coordinates_eq]
    exact hxbcoord
  have hetaTop : d < D.primalEmbedding.coordinates
      (D.dualEmbedding.vertex xt) 1 := by
    change d < D.primalEmbedding.coordinates (D.dualEmbedding.vertex xt) 1
    rw [D.coordinates_eq]
    exact hxtcoord
  have hab0 : a < b := by linarith
  have hcd0 : c < d := by linarith
  obtain ⟨t, s, hcrossC⟩ :=
    ContinuousRectangleCrossing.strip_paths_intersect hab0 hcd0 gammaC etaC
      hgammaLeft hgammaRight hetaBottom hetaTop hgammaY hetaX
  have hcross : gamma t = eta s := by
    apply D.primalEmbedding.coordinates.injective
    simpa [gammaC, etaC] using hcrossC
  have htRect := hgammaRect ⟨t, rfl⟩
  have hsRect := hetaRectDual ⟨s, rfl⟩
  rw [D.dual_planeRect_eq] at hsRect
  change a - B ≤ D.primalEmbedding.coordinates (gamma t) 0 ∧
    D.primalEmbedding.coordinates (gamma t) 0 ≤ b + B ∧
    (c + 4 * B) - B ≤ D.primalEmbedding.coordinates (gamma t) 1 ∧
    D.primalEmbedding.coordinates (gamma t) 1 ≤ (d - 4 * B) + B at htRect
  change (a + 4 * B) - B ≤ D.primalEmbedding.coordinates (eta s) 0 ∧
    D.primalEmbedding.coordinates (eta s) 0 ≤ (b - 4 * B) + B ∧
    c - B ≤ D.primalEmbedding.coordinates (eta s) 1 ∧
    D.primalEmbedding.coordinates (eta s) 1 ≤ d + B at hsRect
  have htCore : gamma t ∈ Set.range gamma0 := by
    have ht : gamma t ∈ Set.range gamma := ⟨t, rfl⟩
    dsimp only [gamma] at ht
    rw [Path.trans_range] at ht
    rcases ht with hleft | hrest
    rw [Path.symm_range] at hleft
    · obtain ⟨r, hr⟩ := hleft
      have hu := D.primalEmbedding.edgeArc_coord_le_vertex_add hBp hxl r 0
      rw [hr] at hu
      rw [hcross] at hu
      linarith
    · simp only [Path.trans_range, Set.mem_union] at hrest
      rcases hrest with hcore | hright
      · exact hcore
      · obtain ⟨r, hr⟩ := hright
        have hu := D.primalEmbedding.vertex_sub_le_edgeArc_coord hBp hxr r 0
        rw [hr] at hu
        rw [hcross] at hu
        linarith
  have hsCore : eta s ∈ Set.range eta0 := by
    have hs : eta s ∈ Set.range eta := ⟨s, rfl⟩
    dsimp only [eta] at hs
    rw [Path.trans_range] at hs
    rcases hs with hbottom | hrest
    rw [Path.symm_range] at hbottom
    · obtain ⟨r, hr⟩ := hbottom
      have hu := D.dualEmbedding.edgeArc_coord_le_vertex_add hBd hxb r 1
      rw [hr] at hu
      rw [← D.coordinates_eq] at hu
      rw [← hcross] at hu
      linarith
    · simp only [Path.trans_range, Set.mem_union] at hrest
      rcases hrest with hcore | htop
      · exact hcore
      · obtain ⟨r, hr⟩ := htop
        have hu := D.dualEmbedding.vertex_sub_le_edgeArc_coord hBd hxt r 1
        rw [hr] at hu
        rw [← D.coordinates_eq] at hu
        rw [← hcross] at hu
        linarith
  have hdisj := D.no_openRectWalkArc_crossing omega p q hpNotNil hqNotNil
  exact Set.disjoint_left.mp hdisj htCore (hcross.symm ▸ hsCore)

theorem matchedCrossing_measureReal_add_le_one
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {B a b c d : ℝ}
    (hBpos : 0 < B)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B) :
    mu.real (D.primalEmbedding.horizontalCrossingEvent
        a b (c + 4 * B) (d - 4 * B)) +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a + 4 * B) (b - 4 * B) c d) ≤ 1 := by
  let H := D.primalEmbedding.horizontalCrossingEvent
    a b (c + 4 * B) (d - 4 * B)
  let Vd := (dualConfigEquiv D.edgeDual) ⁻¹'
    D.dualEmbedding.verticalCrossingEvent (a + 4 * B) (b - 4 * B) c d
  have hdisj : Disjoint H Vd :=
    D.matchedCrossingEvents_disjoint hBpos hBp hBd hab hcd
  have hVd : MeasurableSet Vd :=
    (D.dualEmbedding.verticalCrossingEvent_measurableSet
      (a + 4 * B) (b - 4 * B) c d).preimage
        (continuous_dualConfigEquiv D.edgeDual).measurable
  have hu : mu.real (H ∪ Vd) ≤ 1 := measureReal_le_one
  rw [measureReal_union hdisj hVd] at hu
  exact hu


theorem exists_buffer_matchedCrossing_measureReal_add_le_one
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu] :
    ∃ B : ℝ, 0 < B ∧ ∀ {a b c d : ℝ},
      a + 5 * B < b - 5 * B → c + 5 * B < d - 5 * B →
      mu.real (D.primalEmbedding.horizontalCrossingEvent
          a b (c + 4 * B) (d - 4 * B)) +
        mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a + 4 * B) (b - 4 * B) c d) ≤ 1 := by
  obtain ⟨B, hBpos, hBp, hBd⟩ :=
    D.exists_common_edgeArc_displacement_bound
  refine ⟨B, hBpos, ?_⟩
  intro a b c d hab hcd
  exact D.matchedCrossing_measureReal_add_le_one
    mu hBpos hBp hBd hab hcd


end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar
