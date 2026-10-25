/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part12
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem ExpandedEndpointPrimalBoundaryBandLevel.primalAdjacent_limit
    {E : PeriodicPlaneEmbedding P}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {template : Nat -> Finset V} {radius : Nat -> Nat}
    {vLeft vRight vBottom vTop pad : Nat -> Real}
    {step : Nat -> Int}
    (level : ExpandedEndpointPrimalBoundaryBandLevel E mu template radius
      vLeft vRight vBottom vTop pad)
    (hcontinuation : E.UniformTemplateAdjacentBoundaryBandCrossingRadius
      mu template step radius) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (vLeft n - pad n) (vRight n + pad n)
        (vBottom n + pad n) (vTop n - pad n)))
      (mu.real (E.verticalCrossingEvent
        (vLeft n - pad n) (vRight n + pad n)
        (vBottom n + pad n) (vTop n - pad n + step n))))
      atTop (nhds 1) := by
  exact hcontinuation level.width level.height level.margin level.base
    (fun n => vLeft n - pad n) (fun n => vRight n + pad n)
    (fun n => vBottom n + pad n) (fun n => vTop n - pad n)
    level.score level.width_separated level.height_separated
    level.score_le_one level.score_tendsto level.source_subset
    level.connector_subset level.bottom level.top level.left level.right


theorem expandedEndpoint_spans_of_inner_gaps
    (B : Real) (hBpos : 0 < B)
    (vLeft vRight vBottom vTop : Nat -> Real)
    (hLeft hRight hBottom hTop pad : Nat -> Real)
    (hpad : forall n, 4 * B <= pad n)
    (hvWidth : forall n, 10 * B < vRight n - vLeft n)
    (hvHeight : forall n, 10 * B < vTop n - vBottom n)
    (hhWidth : forall n, 10 * B < hRight n - hLeft n)
    (hhHeight : forall n, 10 * B < hTop n - hBottom n) :
    (forall n, vLeft n - pad n + 5 * B <
      vRight n + pad n - 5 * B) /\
    (forall n, vBottom n + 5 * B < vTop n - 5 * B) /\
    (forall n, hLeft n + 5 * B < hRight n - 5 * B) /\
    (forall n, hBottom n - pad n + 5 * B <
      hTop n + pad n - 5 * B) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro n
  · nlinarith [hpad n, hvWidth n]
  · nlinarith [hvHeight n]
  · nlinarith [hhWidth n]
  · nlinarith [hpad n, hhHeight n]


theorem ExpandedEndpointPrimalBoundaryBandLevel.false_of_alignedEndpoints
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {template : Nat -> Finset V} {radius : Nat -> Nat}
    {vLeft vRight vBottom vTop pad : Nat -> Real}
    {hLeft hRight hBottom hTop : Nat -> Real}
    {step : Nat -> Int}
    (level : ExpandedEndpointPrimalBoundaryBandLevel D.primalEmbedding mu
      template radius vLeft vRight vBottom vTop pad)
    (hcontinuation :
      D.primalEmbedding.UniformTemplateAdjacentBoundaryBandCrossingRadius
        mu template step radius)
    (halignLeft : forall n, hLeft n + pad n = vLeft n - pad n)
    (halignRight : forall n, hRight n - pad n = vRight n + pad n)
    (halignBottom : forall n, hBottom n - pad n = vBottom n + pad n)
    (halignTop : forall n,
      hTop n + pad n = vTop n - pad n + step n)
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (hpad : forall n, 4 * B <= pad n)
    (hvWidth : forall n, 10 * B < vRight n - vLeft n)
    (hvHeight : forall n, 10 * B < vTop n - vBottom n)
    (hhWidth : forall n, 10 * B < hRight n - hLeft n)
    (hhHeight : forall n, 10 * B < hTop n - hBottom n)
    (hdualVertical : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (vLeft n) (vRight n) (vBottom n) (vTop n)))
      atTop (nhds 1))
    (hdualHorizontal : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (hLeft n) (hRight n) (hBottom n) (hTop n)))
      atTop (nhds 1)) : False := by
  have hprimal0 := level.primalAdjacent_limit hcontinuation
  have hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (vLeft n - pad n) (vRight n + pad n)
        (vBottom n + pad n) (vTop n - pad n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (hLeft n + pad n) (hRight n - pad n)
        (hBottom n - pad n) (hTop n + pad n))))
      atTop (nhds 1) := by
    apply hprimal0.congr'
    filter_upwards [] with n
    simp only [halignLeft n, halignRight n,
      halignBottom n, halignTop n]
  obtain ⟨hspanVX, hspanVY, hspanHX, hspanHY⟩ :=
    expandedEndpoint_spans_of_inner_gaps B hBpos
      vLeft vRight vBottom vTop hLeft hRight hBottom hTop pad hpad
      hvWidth hvHeight hhWidth hhHeight
  exact D.variablePadComplementaryEndpoints_false mu B hBpos hBp hBd
    vLeft vRight vBottom vTop hLeft hRight hBottom hTop pad hpad
    hspanVX hspanVY hspanHX hspanHY hprimal hdualVertical hdualHorizontal


theorem PeriodicPlaneEmbedding.uniformTemplateAdjacentBoundaryBandCrossingRadius_of_deepGrid
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (template : Nat -> Finset V) (step : Nat -> Int)
    (radius : Nat -> Nat)
    (hcross : E.UniformTemplateDeepGridAdjacentHeightCrossingRadius
      mu template step radius) :
    E.UniformTemplateAdjacentBoundaryBandCrossingRadius
      mu template step radius := by
  intro width height margin base a b c d p hwidthSep hheightSep hp hplim
    hsource hconnector hbottom htop hleft hright
  let epsilon : Nat -> Real := fun n => 1 - p n
  let bottom : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Real := fun n v =>
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  let top : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Real := fun n v =>
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))
  let left : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Real := fun n v =>
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  let right : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Real := fun n v =>
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))
  let vertical : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Bool := fun n v =>
    boundaryBandPreferenceColor (margin n) (height n) v.2.val
      (epsilon n) (bottom n v) (top n v)
  let horizontal : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Bool := fun n v =>
    boundaryBandPreferenceColor (margin n) (width n) v.1.val
      (epsilon n) (left n v) (right n v)
  have hepsilon : Tendsto epsilon atTop (nhds 0) := by
    simpa [epsilon] using
      (tendsto_const_nhds (x := (1 : Real))).sub hplim
  apply hcross width height margin
    (fun n => (Nat.zero_le (2 * margin n)).trans_lt (hwidthSep n))
    base vertical horizontal a b c d epsilon bottom top left right hepsilon
  · exact fun n => sub_nonneg.mpr (hp n)
  · exact hsource
  · exact hconnector
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v
    rfl
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_true_of_lower hv
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_false_of_upper (hheightSep n) hv
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_true_of_lower hv
  · intro n v hv
    exact boundaryBandPreferenceColor_eq_false_of_upper (hwidthSep n) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_true_imp
      (sub_nonneg.mpr (hp n)) (hheightSep n) measureReal_le_one
      (fun h => hbottom n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_false_imp
      (sub_nonneg.mpr (hp n)) (hheightSep n) measureReal_le_one
      (fun h => htop n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_true_imp
      (sub_nonneg.mpr (hp n)) (hwidthSep n) measureReal_le_one
      (fun h => hleft n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_false_imp
      (sub_nonneg.mpr (hp n)) (hwidthSep n) measureReal_le_one
      (fun h => hright n v h) (le_refl _) hv


theorem PeriodicPlaneEmbedding.uniformTemplateAdjacentBoundaryBandCrossingRadius_of_pairMerge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (template : Nat -> Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (step : Nat -> Int) (hstep : forall n, 0 <= step n)
    (radius : Nat -> Nat)
    (hmerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
        ((template n).image (P.shift
          (preferenceKingOffset (q n).2 +
            if (q n).1.val = 0 then 0 else verticalShift (step n))))
        (radius n))) atTop (nhds 0)) :
    E.UniformTemplateAdjacentBoundaryBandCrossingRadius
      mu template step radius := by
  apply E.uniformTemplateAdjacentBoundaryBandCrossingRadius_of_deepGrid
  exact E.uniformTemplateDeepGridAdjacentHeightCrossingRadius_of_pairMerge
    mu hFKG hTI template htemplateHit step hstep radius hmerge


theorem PeriodicPlaneEmbedding.exists_uniformTemplateAdjacentBoundaryBandCrossingRadius
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat -> Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (step : Nat -> Int) (hstep : forall n, 0 <= step n) :
    exists radius, E.UniformTemplateAdjacentBoundaryBandCrossingRadius
      mu template step radius := by
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_deepGrid_adjacentHeight_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit step hstep
  exact ⟨radius,
    E.uniformTemplateAdjacentBoundaryBandCrossingRadius_of_deepGrid
      mu template step radius hcross⟩


theorem PeriodicPlaneEmbedding.exists_uniformTemplateAdjacentBoundaryBandCrossingRadius_with_pairMerge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat -> Finset V)
    (htemplateHit : Tendsto (fun n =>
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
    (step : Nat -> Int) (hstep : forall n, 0 <= step n) :
    exists radius : Nat -> Nat,
      (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3),
        Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
          ((template n).image (P.shift
            (preferenceKingOffset (q n).2 +
              if (q n).1.val = 0 then 0 else verticalShift (step n))))
          (radius n))) atTop (nhds 0)) /\
      E.UniformTemplateAdjacentBoundaryBandCrossingRadius
        mu template step radius := by
  let neighbor : Nat -> (Fin 2 × (Fin 3 × Fin 3)) -> Finset V :=
    fun n q => (template n).image (P.shift
      (preferenceKingOffset q.2 +
        if q.1.val = 0 then 0 else verticalShift (step n)))
  obtain ⟨radius, hradius⟩ :=
    P.exists_uniform_pairMergeRadius mu hunique template neighbor
  have hepsilon : Tendsto (fun n : Nat => (1 : Real) / (n + 1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hmerge (q : Nat -> Fin 2 × (Fin 3 × Fin 3)) :
      Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n)
        ((template n).image (P.shift
          (preferenceKingOffset (q n).2 +
            if (q n).1.val = 0 then 0 else verticalShift (step n))))
        (radius n))) atTop (nhds 0) := by
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => le_of_lt ((hradius n).2 (q n))) hepsilon
  exact ⟨radius, hmerge,
    E.uniformTemplateAdjacentBoundaryBandCrossingRadius_of_pairMerge
      mu hFKG hTI template htemplateHit step hstep radius hmerge⟩


end StatMech.FK.PeriodicPlanar
