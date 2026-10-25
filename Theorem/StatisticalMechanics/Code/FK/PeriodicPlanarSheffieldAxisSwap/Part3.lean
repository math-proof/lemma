/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrossingFromArms
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap.Part3
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


@[simp] theorem PeriodicPlaneEmbedding.axisSwap_vertexCoord
    (E : PeriodicPlaneEmbedding P) (x : V) (i : Fin 2) :
    E.axisSwap.vertexCoord x i = E.vertexCoord x (Fin.rev i) := by
  simp [PeriodicPlaneEmbedding.vertexCoord, PeriodicPlaneEmbedding.axisSwap]

@[simp] theorem PeriodicPlaneEmbedding.axisSwap_vertexCoord_zero
    (E : PeriodicPlaneEmbedding P) (x : V) :
    E.axisSwap.vertexCoord x 0 = E.vertexCoord x 1 := by
  rfl

@[simp] theorem PeriodicPlaneEmbedding.axisSwap_vertexCoord_one
    (E : PeriodicPlaneEmbedding P) (x : V) :
    E.axisSwap.vertexCoord x 1 = E.vertexCoord x 0 := by
  rfl


theorem PeriodicGraph.axisSwap_isTranslationInvariant
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) :
    P.axisSwap.IsTranslationInvariant mu := by
  intro z
  simpa [PeriodicGraph.axisSwap, PeriodicGraph.configTranslate] using
    hTI (siteAxisSwap z)


theorem PeriodicPlaneEmbedding.axisSwap_verticalCrossingEvent_subset_horizontalCrossingEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) :
    E.axisSwap.verticalCrossingEvent a b c d ⊆
      E.horizontalCrossingEvent c d a b := by
  intro omega homega
  change E.axisSwap.rectRestrict a b c d omega ∈
    E.axisSwap.finiteVerticalCrossing a b c d at homega
  obtain ⟨x, y, hxBottom, hyTop, hxy⟩ := homega
  have hx' : x.1 ∈ E.rectVertices c d a b := by
    exact ⟨by simpa using x.2.2.2.1, by simpa using x.2.2.2.2,
      by simpa using x.2.1, by simpa using x.2.2.1⟩
  have hy' : y.1 ∈ E.rectVertices c d a b := by
    exact ⟨by simpa using y.2.2.2.1, by simpa using y.2.2.2.2,
      by simpa using y.2.1, by simpa using y.2.2.1⟩
  have hxLeft : E.rectLeftBoundary c d a b ⟨x.1, hx'⟩ := by
    obtain ⟨z, hxz, hz⟩ := hxBottom
    refine ⟨z, hxz, ?_⟩
    simpa using hz
  have hyRight : E.rectRightBoundary c d a b ⟨y.1, hy'⟩ := by
    obtain ⟨z, hyz, hz⟩ := hyTop
    refine ⟨z, hyz, ?_⟩
    simpa using hz
  rw [E.axisSwap.openSub_rectRestrict_eq_induce] at hxy
  obtain ⟨p⟩ := hxy
  let pAmbient : (P.openSubgraph omega).Walk x.1 y.1 :=
    p.map (SimpleGraph.Embedding.induce
      (E.axisSwap.rectVertices a b c d)).toHom
  have hpAmbient : ∀ v ∈ pAmbient.support,
      v ∈ E.rectVertices c d a b := by
    intro v hv
    have hv' : v ∈
        (p.map (SimpleGraph.Embedding.induce
          (E.axisSwap.rectVertices a b c d)).toHom).support := hv
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hv'
    obtain ⟨w, _hw, rfl⟩ := hv'
    exact ⟨by simpa using w.2.2.2.1, by simpa using w.2.2.2.2,
      by simpa using w.2.1, by simpa using w.2.2.1⟩
  have hreach :
      ((P.openSubgraph omega).induce (E.rectVertices c d a b)).Reachable
        ⟨x.1, hx'⟩ ⟨y.1, hy'⟩ :=
    ⟨pAmbient.induce (E.rectVertices c d a b) hpAmbient⟩
  change E.rectRestrict c d a b omega ∈ E.finiteHorizontalCrossing c d a b
  refine ⟨⟨x.1, hx'⟩, ⟨y.1, hy'⟩, hxLeft, hyRight, ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hreach


theorem PeriodicPlaneEmbedding.horizontalCrossing_tendsto_one_of_axisSwap_finiteStripJoinedBoundaryArms
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy u - E.vertex x) i| ≤ B)
    (hB0 : 0 ≤ B)
    (r c d : Nat → Real) (height : Nat → Nat)
    (lower upper : Nat → Finset V)
    (hgap : ∀ n, 3 * B < d n - c n)
    (harms : Tendsto (fun n ↦ mu.real
      (E.axisSwap.finiteStripJoinedBoundaryArmEvent
        (r n) (c n) (d n) (height n) (lower n) (upper n)))
      atTop (nhds 1)) :
    Tendsto (fun n ↦ mu.real
      (E.horizontalCrossingEvent
        ((2 * c n + d n) / 3) ((c n + 2 * d n) / 3)
        (r n) (r n + height n))) atTop (nhds 1) := by
  have hBswap : ∀ {x y : V} (hxy : P.axisSwap.graph.Adj x y)
      (u) (i : Fin 2),
      |E.axisSwap.coordinates
        (E.axisSwap.edgeArc hxy u - E.axisSwap.vertex x) i| ≤ B := by
    intro x y hxy u i
    change |axisSwapCoordinates
      (E.coordinates (E.edgeArc hxy u - E.vertex x)) i| ≤ B
    rw [axisSwapCoordinates_apply]
    exact hB hxy u (Fin.rev i)
  have hvertical :=
    E.axisSwap.verticalCrossing_tendsto_one_of_finiteStripJoinedBoundaryArms
      mu B hBswap hB0 r c d height lower upper hgap harms
  exact hvertical.squeeze tendsto_const_nhds
    (fun n ↦ measureReal_mono
      (E.axisSwap_verticalCrossingEvent_subset_horizontalCrossingEvent
        (r n) (r n + height n)
        ((2 * c n + d n) / 3) ((c n + 2 * d n) / 3)))
    (fun _ ↦ measureReal_le_one)


theorem PeriodicPlaneEmbedding.exists_horizontalCrossing_measureReal_gt_of_unique
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r B s : Real) (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy u - E.vertex x) i| ≤ B)
    (t : Int) (ht : 3 * B < t) (m : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ n : Nat, m ≤ n ∧ 1 - epsilon <
      mu.real (E.horizontalCrossingEvent
        ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)
        r (r + n)) := by
  have hBswap : ∀ {x y : V} (hxy : P.axisSwap.graph.Adj x y)
      (u) (i : Fin 2),
      |E.axisSwap.coordinates
        (E.axisSwap.edgeArc hxy u - E.axisSwap.vertex x) i| ≤ B := by
    intro x y hxy u i
    change |axisSwapCoordinates
      (E.coordinates (E.edgeArc hxy u - E.vertex x)) i| ≤ B
    rw [axisSwapCoordinates_apply]
    exact hB hxy u (Fin.rev i)
  obtain ⟨n, hmn, hvertical⟩ :=
    E.axisSwap.exists_verticalCrossing_measureReal_gt_of_unique
      mu hFKG (P.axisSwap_isTranslationInvariant mu hTI) hunique
        r B s hB0 hBswap t ht m hepsilon
  refine ⟨n, hmn, hvertical.trans_le (measureReal_mono ?_)⟩
  exact E.axisSwap_verticalCrossingEvent_subset_horizontalCrossingEvent
    r (r + n) ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)


theorem PeriodicPlaneEmbedding.exists_cofinal_horizontalCrossing_tendsto_one_of_unique
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r B s : Real) (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy u - E.vertex x) i| ≤ B)
    (t : Int) (ht : 3 * B < t) :
    ∃ height : Nat → Nat,
      Tendsto height atTop atTop ∧
      Tendsto (fun k => mu.real
        (E.horizontalCrossingEvent
          ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)
          r (r + height k))) atTop (nhds 1) := by
  have hBswap : ∀ {x y : V} (hxy : P.axisSwap.graph.Adj x y)
      (u) (i : Fin 2),
      |E.axisSwap.coordinates
        (E.axisSwap.edgeArc hxy u - E.axisSwap.vertex x) i| ≤ B := by
    intro x y hxy u i
    change |axisSwapCoordinates
      (E.coordinates (E.edgeArc hxy u - E.vertex x)) i| ≤ B
    rw [axisSwapCoordinates_apply]
    exact hB hxy u (Fin.rev i)
  obtain ⟨height, hheight, hvertical⟩ :=
    E.axisSwap.exists_cofinal_verticalCrossing_tendsto_one_of_unique
      mu hFKG (P.axisSwap_isTranslationInvariant mu hTI) hunique
        r B s hB0 hBswap t ht
  have hle : ∀ k,
      mu.real (E.axisSwap.verticalCrossingEvent r (r + height k)
        ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)) ≤
      mu.real (E.horizontalCrossingEvent
        ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)
        r (r + height k)) := fun k =>
    measureReal_mono
      (E.axisSwap_verticalCrossingEvent_subset_horizontalCrossingEvent
        r (r + height k) ((2 * s + (s + t)) / 3)
          ((s + 2 * (s + t)) / 3))
  refine ⟨height, hheight,
    tendsto_of_tendsto_of_tendsto_of_le_of_le hvertical
      tendsto_const_nhds hle ?_⟩
  intro k
  exact measureReal_le_one


theorem PeriodicPlanarDualPair.exists_cofinal_complementaryDual_horizontalCrossing_tendsto_one
    {W : Type*} [DecidableEq W] [Countable W]
    {Pdual : PeriodicGraph W}
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hdualFKG : IsFKG (D.dualMeasure mu))
    (hTI : P.IsTranslationInvariant mu)
    (hdualUnique : D.dualMeasure mu
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (r B s : Real) (hB0 : 0 ≤ B)
    (hB : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy u - D.dualEmbedding.vertex x) i| ≤ B)
    (t : Int) (ht : 3 * B < t) :
    ∃ height : Nat → Nat,
      Tendsto height atTop atTop ∧
      Tendsto (fun k => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)
          r (r + height k))) atTop (nhds 1) := by
  let muDual := D.dualMeasure mu
  letI : IsProbabilityMeasure muDual := by
    dsimp only [muDual, PeriodicPlanarDualPair.dualMeasure]
    exact inferInstance
  obtain ⟨height, hheight, hlimit⟩ :=
    D.dualEmbedding.exists_cofinal_horizontalCrossing_tendsto_one_of_unique
      muDual hdualFKG (D.dualMeasure_isTranslationInvariant mu hTI)
        hdualUnique r B s hB0 hB t ht
  refine ⟨height, hheight, hlimit.congr' ?_⟩
  filter_upwards with k
  exact D.dualMeasure_measureReal mu
    (D.dualEmbedding.horizontalCrossingEvent_measurableSet
      ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)
        r (r + height k))

end StatMech.FK.PeriodicPlanar
