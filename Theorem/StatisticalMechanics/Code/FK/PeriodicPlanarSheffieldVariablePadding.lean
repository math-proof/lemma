/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldVariablePadding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRotatedBoundaryBands.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem PeriodicPlaneEmbedding.verticalCrossingEvent_mono_horizontal
    (E : PeriodicPlaneEmbedding P) {a' a b b' c d : Real}
    (ha : a' ≤ a) (hb : b ≤ b') :
    E.verticalCrossingEvent a b c d ⊆
      E.verticalCrossingEvent a' b' c d := by
  intro omega homega
  change E.rectRestrict a b c d omega ∈
    E.finiteVerticalCrossing a b c d at homega
  obtain ⟨x, y, hxBottom, hyTop, hxy⟩ := homega
  have hx' : x.1 ∈ E.rectVertices a' b' c d :=
    ⟨ha.trans x.2.1, x.2.2.1.trans hb, x.2.2.2⟩
  have hy' : y.1 ∈ E.rectVertices a' b' c d :=
    ⟨ha.trans y.2.1, y.2.2.1.trans hb, y.2.2.2⟩
  have hxBottom' : E.rectBottomBoundary a' b' c d ⟨x.1, hx'⟩ := by
    obtain ⟨z, hxz, hz⟩ := hxBottom
    exact ⟨z, hxz, hz⟩
  have hyTop' : E.rectTopBoundary a' b' c d ⟨y.1, hy'⟩ := by
    obtain ⟨z, hyz, hz⟩ := hyTop
    exact ⟨z, hyz, hz⟩
  rw [E.openSub_rectRestrict_eq_induce] at hxy
  obtain ⟨p⟩ := hxy
  let pAmbient : (P.openSubgraph omega).Walk x.1 y.1 :=
    p.map (SimpleGraph.Embedding.induce (E.rectVertices a b c d)).toHom
  have hpAmbient : ∀ v ∈ pAmbient.support,
      v ∈ E.rectVertices a' b' c d := by
    intro v hv
    have hv' : v ∈
        (p.map (SimpleGraph.Embedding.induce
          (E.rectVertices a b c d)).toHom).support := by
      exact hv
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hv'
    obtain ⟨u, _hu, rfl⟩ := hv'
    exact ⟨ha.trans u.2.1, u.2.2.1.trans hb, u.2.2.2⟩
  have hxy' :
      ((P.openSubgraph omega).induce (E.rectVertices a' b' c d)).Reachable
        ⟨x.1, hx'⟩ ⟨y.1, hy'⟩ :=
    ⟨pAmbient.induce (E.rectVertices a' b' c d) hpAmbient⟩
  change E.rectRestrict a' b' c d omega ∈
    E.finiteVerticalCrossing a' b' c d
  refine ⟨⟨x.1, hx'⟩, ⟨y.1, hy'⟩, hxBottom', hyTop', ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hxy'


theorem PeriodicPlaneEmbedding.horizontalCrossingEvent_mono_vertical
    (E : PeriodicPlaneEmbedding P) {a b c' c d d' : Real}
    (hc : c' ≤ c) (hd : d ≤ d') :
    E.horizontalCrossingEvent a b c d ⊆
      E.horizontalCrossingEvent a b c' d' := by
  intro omega homega
  change E.rectRestrict a b c d omega ∈
    E.finiteHorizontalCrossing a b c d at homega
  obtain ⟨x, y, hxLeft, hyRight, hxy⟩ := homega
  have hx' : x.1 ∈ E.rectVertices a b c' d' :=
    ⟨x.2.1, x.2.2.1, hc.trans x.2.2.2.1, x.2.2.2.2.trans hd⟩
  have hy' : y.1 ∈ E.rectVertices a b c' d' :=
    ⟨y.2.1, y.2.2.1, hc.trans y.2.2.2.1, y.2.2.2.2.trans hd⟩
  have hxLeft' : E.rectLeftBoundary a b c' d' ⟨x.1, hx'⟩ := by
    obtain ⟨z, hxz, hz⟩ := hxLeft
    exact ⟨z, hxz, hz⟩
  have hyRight' : E.rectRightBoundary a b c' d' ⟨y.1, hy'⟩ := by
    obtain ⟨z, hyz, hz⟩ := hyRight
    exact ⟨z, hyz, hz⟩
  rw [E.openSub_rectRestrict_eq_induce] at hxy
  obtain ⟨p⟩ := hxy
  let pAmbient : (P.openSubgraph omega).Walk x.1 y.1 :=
    p.map (SimpleGraph.Embedding.induce (E.rectVertices a b c d)).toHom
  have hpAmbient : ∀ v ∈ pAmbient.support,
      v ∈ E.rectVertices a b c' d' := by
    intro v hv
    have hv' : v ∈
        (p.map (SimpleGraph.Embedding.induce
          (E.rectVertices a b c d)).toHom).support := by
      exact hv
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hv'
    obtain ⟨u, _hu, rfl⟩ := hv'
    exact ⟨u.2.1, u.2.2.1, hc.trans u.2.2.2.1, u.2.2.2.2.trans hd⟩
  have hxy' :
      ((P.openSubgraph omega).induce (E.rectVertices a b c' d')).Reachable
        ⟨x.1, hx'⟩ ⟨y.1, hy'⟩ :=
    ⟨pAmbient.induce (E.rectVertices a b c' d') hpAmbient⟩
  change E.rectRestrict a b c' d' omega ∈
    E.finiteHorizontalCrossing a b c' d'
  refine ⟨⟨x.1, hx'⟩, ⟨y.1, hy'⟩, hxLeft', hyRight', ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hxy'


theorem PeriodicPlaneEmbedding.verticalCrossing_tendsto_one_mono_horizontal
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (a b c d a' b' : Nat -> Real)
    (ha : forall n, a' n <= a n) (hb : forall n, b n <= b' n)
    (hlimit : Tendsto (fun n => mu.real
      (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
      atTop (nhds 1)) :
    Tendsto (fun n => mu.real
      (E.verticalCrossingEvent (a' n) (b' n) (c n) (d n)))
      atTop (nhds 1) := by
  exact hlimit.squeeze tendsto_const_nhds
    (fun n => measureReal_mono
      (E.verticalCrossingEvent_mono_horizontal (ha n) (hb n)))
    (fun _ => measureReal_le_one)


theorem PeriodicPlaneEmbedding.horizontalCrossing_tendsto_one_mono_vertical
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (a b c d c' d' : Nat -> Real)
    (hc : forall n, c' n <= c n) (hd : forall n, d n <= d' n)
    (hlimit : Tendsto (fun n => mu.real
      (E.horizontalCrossingEvent (a n) (b n) (c n) (d n)))
      atTop (nhds 1)) :
    Tendsto (fun n => mu.real
      (E.horizontalCrossingEvent (a n) (b n) (c' n) (d' n)))
      atTop (nhds 1) := by
  exact hlimit.squeeze tendsto_const_nhds
    (fun n => measureReal_mono
      (E.horizontalCrossingEvent_mono_vertical (hc n) (hd n)))
    (fun _ => measureReal_le_one)


theorem PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one_of_pads
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {B xPad yPad a b c d : Real}
    (hBpos : 0 < B)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
    (hxPad : 4 * B ≤ xPad) (hyPad : 4 * B ≤ yPad)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B) :
    mu.real (D.primalEmbedding.horizontalCrossingEvent
        a b (c + yPad) (d - yPad)) +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a + xPad) (b - xPad) c d) ≤ 1 := by
  have hH : D.primalEmbedding.horizontalCrossingEvent
      a b (c + yPad) (d - yPad) ⊆
      D.primalEmbedding.horizontalCrossingEvent
        a b (c + 4 * B) (d - 4 * B) :=
    D.primalEmbedding.horizontalCrossingEvent_mono_vertical
      (by linarith) (by linarith)
  have hV : D.dualEmbedding.verticalCrossingEvent
      (a + xPad) (b - xPad) c d ⊆
      D.dualEmbedding.verticalCrossingEvent
        (a + 4 * B) (b - 4 * B) c d :=
    D.dualEmbedding.verticalCrossingEvent_mono_horizontal
      (by linarith) (by linarith)
  have hbase := D.matchedCrossing_measureReal_add_le_one
    mu hBpos hBp hBd hab hcd
  have hHm := measureReal_mono (h₂ := measure_ne_top mu _) hH
  have hVpre :
      (dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a + xPad) (b - xPad) c d ⊆
        (dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a + 4 * B) (b - 4 * B) c d :=
    Set.preimage_mono hV
  have hVm := measureReal_mono (h₂ := measure_ne_top mu _)
    hVpre
  linarith


theorem PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_pads
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {B xPad yPad a b c d : Real}
    (hBpos : 0 < B)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
    (hxPad : 4 * B ≤ xPad) (hyPad : 4 * B ≤ yPad)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B) :
    mu.real (D.primalEmbedding.verticalCrossingEvent
        (a + xPad) (b - xPad) c d) +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          a b (c + yPad) (d - yPad)) ≤ 1 := by
  have hV : D.primalEmbedding.verticalCrossingEvent
      (a + xPad) (b - xPad) c d ⊆
      D.primalEmbedding.verticalCrossingEvent
        (a + 4 * B) (b - 4 * B) c d :=
    D.primalEmbedding.verticalCrossingEvent_mono_horizontal
      (by linarith) (by linarith)
  have hH : D.dualEmbedding.horizontalCrossingEvent
      a b (c + yPad) (d - yPad) ⊆
      D.dualEmbedding.horizontalCrossingEvent
        a b (c + 4 * B) (d - 4 * B) :=
    D.dualEmbedding.horizontalCrossingEvent_mono_vertical
      (by linarith) (by linarith)
  have hbase := D.matchedVerticalHorizontalCrossing_measureReal_add_le_one
    mu hBpos hBp hBd hab hcd
  have hVm := measureReal_mono (h₂ := measure_ne_top mu _) hV
  have hHpre :
      (dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            a b (c + yPad) (d - yPad) ⊆
        (dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            a b (c + 4 * B) (d - 4 * B) :=
    Set.preimage_mono hH
  have hHm := measureReal_mono (h₂ := measure_ne_top mu _)
    hHpre
  linarith


end StatMech.FK.PeriodicPlanar
