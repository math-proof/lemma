/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarDualPair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


structure PeriodicPlaneEmbedding (P : PeriodicGraph V) where
  vertex : V ↪ ℂ
  period : Site 2 →+ ℂ
  period_injective : Function.Injective period
  coordinates : ℂ ≃L[ℝ] (Fin 2 → ℝ)
  coordinates_period : ∀ z i, coordinates (period z) i = z i
  vertex_shift : ∀ z x, vertex (P.shift z x) = vertex x + period z
  proper : ∀ R : ℝ, {x | ‖(vertex x : ℂ)‖ ≤ R}.Finite
  edgeArc : ∀ {x y : V}, P.graph.Adj x y → Path (vertex x) (vertex y)
  edgeArc_injective : ∀ {x y : V} (hxy : P.graph.Adj x y),
    Function.Injective (edgeArc hxy)
  edgeArc_symm : ∀ {x y : V} (hxy : P.graph.Adj x y),
    Set.range (edgeArc hxy.symm) = Set.range (edgeArc hxy)
  edgeArc_shift : ∀ (z : Site 2) {x y : V} (hxy : P.graph.Adj x y),
    Set.range (edgeArc ((P.shift_adj z x y).2 hxy)) =
      (fun p => p + period z) '' Set.range (edgeArc hxy)
  edgeArc_intersection : ∀ {x y z w : V}
      (hxy : P.graph.Adj x y) (hzw : P.graph.Adj z w) (p : ℂ),
      s(x, y) ≠ s(z, w) →
      p ∈ Set.range (edgeArc hxy) → p ∈ Set.range (edgeArc hzw) →
        ∃ v, (v = x ∨ v = y) ∧ (v = z ∨ v = w) ∧ vertex v = p
  edgeArc_disjoint : ∀ {x y z w : V}
      (hxy : P.graph.Adj x y) (hzw : P.graph.Adj z w),
      x ≠ z → x ≠ w → y ≠ z → y ≠ w →
        Disjoint (Set.range (edgeArc hxy)) (Set.range (edgeArc hzw))
  edgeArc_locallyFinite : ∀ (K : Set ℂ), IsCompact K →
    {xy : V × V | ∃ hxy : P.graph.Adj xy.1 xy.2,
      (Set.range (edgeArc hxy) ∩ K).Nonempty}.Finite


structure PeriodicPlanarDualPair
    [Countable V] [Countable W]
    (P : PeriodicGraph V) (Pdual : PeriodicGraph W) where
  primalEmbedding : PeriodicPlaneEmbedding P
  dualEmbedding : PeriodicPlaneEmbedding Pdual
  coordinates_eq : primalEmbedding.coordinates = dualEmbedding.coordinates
  primal_connected : P.graph.Connected
  dual_connected : Pdual.graph.Connected
  edgeDual : Sym2 V ≃ Sym2 W
  edgeDual_mem_edgeSet : ∀ e,
    e ∈ P.graph.edgeSet ↔ edgeDual e ∈ Pdual.graph.edgeSet
  edgeDual_shift : ∀ z e,
    edgeDual (Sym2.map (P.shift z) e) =
      Sym2.map (Pdual.shift z) (edgeDual e)
  edgeDual_crossing : ∀ {x y : V} {a b : W}
      (hxy : P.graph.Adj x y) (hab : Pdual.graph.Adj a b),
      edgeDual s(x, y) = s(a, b) →
        ∃ t u,
          primalEmbedding.edgeArc hxy t = dualEmbedding.edgeArc hab u
  edgeDual_of_crossing : ∀ {x y : V} {a b : W}
      (hxy : P.graph.Adj x y) (hab : Pdual.graph.Adj a b) (t u),
      primalEmbedding.edgeArc hxy t = dualEmbedding.edgeArc hab u →
        edgeDual s(x, y) = s(a, b)
  free_wired_infiniteVolume_dual_law : ∀ {p q : ℝ}
      (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q),
    Pdual.wiredBufferedInfiniteVolume
        (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).1
        (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).2
        (zero_lt_one.trans_le hq) =
      (P.freeBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq)).map
        (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable
  wired_free_infiniteVolume_dual_law : ∀ {p q : ℝ}
      (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q),
    Pdual.freeBufferedInfiniteVolume
        (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).1
        (dualParam_mem_Ioo hp hp1 (zero_lt_one.trans_le hq)).2
        (zero_lt_one.trans_le hq) =
      (P.wiredBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq)).map
        (continuous_dualConfigEquiv edgeDual).measurable.aemeasurable

end StatMech.FK.PeriodicPlanar
