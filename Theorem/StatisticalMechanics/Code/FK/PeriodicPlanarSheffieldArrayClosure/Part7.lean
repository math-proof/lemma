/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure.Part5
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicPlaneEmbedding.exists_uniformTemplateBoundaryBandCrossingRadius
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (template : Nat → Finset V)
    (htemplateHit : Tendsto (fun n ↦
      mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1)) :
    ∃ radius, E.UniformTemplateBoundaryBandCrossingRadius
      mu template radius := by
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_deepGridPreference_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit
  refine ⟨radius, ?_⟩
  intro width height margin base a b c d p hwidthSep hheightSep hp hplim
    hsource hconnector hbottom htop hleft hright
  let epsilon : Nat → Real := fun n ↦ 1 - p n
  let bottom : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v ↦
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  let top : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v ↦
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))
  let left : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v ↦
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  let right : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Real := fun n v ↦
    mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V)
      (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))
  let vertical : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Bool := fun n v ↦
    boundaryBandPreferenceColor (margin n) (height n) v.2.val
      (epsilon n) (bottom n v) (top n v)
  let horizontal : (n : Nat) →
      PreferenceGridVertex (width n) (height n) → Bool := fun n v ↦
    boundaryBandPreferenceColor (margin n) (width n) v.1.val
      (epsilon n) (left n v) (right n v)
  have hepsilon : Tendsto epsilon atTop (nhds 0) := by
    simpa [epsilon] using
      (tendsto_const_nhds (x := (1 : Real))).sub hplim
  apply hcross width height margin
    (fun n ↦ (Nat.zero_le (2 * margin n)).trans_lt (hwidthSep n))
    base vertical horizontal
    a b c d epsilon bottom top left right hepsilon
  · exact fun n ↦ sub_nonneg.mpr (hp n)
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
      (fun h ↦ hbottom n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_false_imp
      (sub_nonneg.mpr (hp n)) (hheightSep n) measureReal_le_one
      (fun h ↦ htop n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_true_imp
      (sub_nonneg.mpr (hp n)) (hwidthSep n) measureReal_le_one
      (fun h ↦ hleft n v h) (le_refl _) hv
  · intro n v hv
    apply boundaryBandPreferenceColor_false_imp
      (sub_nonneg.mpr (hp n)) (hwidthSep n) measureReal_le_one
      (fun h ↦ hright n v h) (le_refl _) hv


theorem PeriodicPlaneEmbedding.exists_uniformBoundaryBandRadius_with_cofinalConnectorSchedule
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
    ∃ (radius : Nat → Nat) (p : Nat → Real)
      (family : ∀ m,
        E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)),
      E.UniformBoundaryBandCrossingRadius mu radius ∧
      Tendsto p atTop (nhds 1) ∧
      ∀ m, (family m).AlignedMarginSchedule E
        (fun _ ↦ E.connectorMarginRequirement (radius m))
        (fun _ ↦ E.connectorMarginRequirement (radius m)) := by
  obtain ⟨radius, hradius⟩ :=
    E.exists_uniformRadius_boundaryBandScores_crossing_max_tendsto_one
      mu hFKG hTI hunique
  obtain ⟨p, family, hp, hschedule⟩ :=
    E.exists_cofinalNormalBoundaryBandFamilies_with_connectorSchedule
      mu hFKG hTI hunique radius
  exact ⟨radius, p, family, hradius, hp, hschedule⟩


theorem PeriodicPlaneEmbedding.exists_alignedActiveSide_choice
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (S : Nat → Finset V) (p : Nat → Real)
    (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (hp : Tendsto p atTop (nhds 1))
    (verticalRequirement horizontalRequirement : Nat → Nat → Nat)
    (cutoff : Nat) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ m, cutoff ≤ m ∧ 1 - epsilon < p m ∧
      (family m).AlignedMarginSchedule E
        (verticalRequirement m) (horizontalRequirement m) := by
  have hev : ∀ᶠ m in atTop, 1 - epsilon < p m :=
    (tendsto_order.1 hp).1 (1 - epsilon) (by linarith)
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 hev
  let m := max cutoff threshold
  refine ⟨m, Nat.le_max_left _ _, hthreshold m (Nat.le_max_right _ _), ?_⟩
  exact (family m).alignedMarginSchedule E
    (verticalRequirement m) (horizontalRequirement m)


theorem PeriodicPlaneEmbedding.exists_uniformRadius_alignedActiveSide_choice
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (S : Nat → Finset V) (p : Nat → Real)
    (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (hp : Tendsto p atTop (nhds 1)) (radius : Nat → Nat)
    (cutoff : Nat) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ m, cutoff ≤ m ∧ 1 - epsilon < p m ∧
      (family m).AlignedMarginSchedule E
        (fun _ ↦ E.connectorMarginRequirement (radius m))
        (fun _ ↦ E.connectorMarginRequirement (radius m)) := by
  exact E.exists_alignedActiveSide_choice mu S p family hp
    (fun m _ ↦ E.connectorMarginRequirement (radius m))
    (fun m _ ↦ E.connectorMarginRequirement (radius m))
    cutoff hepsilon


theorem PeriodicGraph.exists_commonBoundaryPairMergeRadius
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (bottom top left right : Finset V) (cutoff : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ radius, cutoff ≤ radius ∧
      mu.real (P.pairMergeErrorUnion bottom top radius) < epsilon ∧
      mu.real (P.pairMergeErrorUnion left right radius) < epsilon := by
  have hvertical : ∀ᶠ radius in atTop,
      mu.real (P.pairMergeErrorUnion bottom top radius) < epsilon :=
    (tendsto_order.1
      (P.pairMergeErrorUnion_real_tendsto_zero
        mu hunique bottom top)).2 epsilon hepsilon
  have hhorizontal : ∀ᶠ radius in atTop,
      mu.real (P.pairMergeErrorUnion left right radius) < epsilon :=
    (tendsto_order.1
      (P.pairMergeErrorUnion_real_tendsto_zero
        mu hunique left right)).2 epsilon hepsilon
  obtain ⟨verticalCutoff, hverticalCutoff⟩ := eventually_atTop.1 hvertical
  obtain ⟨horizontalCutoff, hhorizontalCutoff⟩ :=
    eventually_atTop.1 hhorizontal
  let radius := max cutoff (max verticalCutoff horizontalCutoff)
  refine ⟨radius, Nat.le_max_left _ _, ?_, ?_⟩
  · exact hverticalCutoff radius
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  · exact hhorizontalCutoff radius
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))


theorem PeriodicPlaneEmbedding.exists_alignedSharedLevel_choice
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (S : Nat → Finset V) (p : Nat → Real)
    (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (hp : Tendsto p atTop (nhds 1))
    (verticalRequirement horizontalRequirement : Nat → Nat → Nat)
    (scaleCutoff : Nat) (connectorRadius : Nat → Nat) {epsilon : Real}
    (hepsilon : 0 < epsilon) :
    ∃ m extent : Nat, ∃ bottom top left right : Finset V,
      scaleCutoff ≤ m ∧
      1 - epsilon < p m ∧
      (family m).AlignedMarginSchedule E
        (verticalRequirement m) (horizontalRequirement m) ∧
      (P.orbitBox (P.bufferedRadius (connectorRadius m)) : Set V) ⊆
        E.rectVertices (-(extent : Real)) extent
          (-(extent : Real)) extent ∧
      (bottom : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (bottom : Set V) (E.rectBottomBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      (top : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (top : Set V) (E.rectTopBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      (left : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (left : Set V) (E.rectLeftBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      (right : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (right : Set V) (E.rectRightBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      let template := P.fourBoundaryComponentTemplate bottom top left right
      (template : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (template : Set V) (E.rectBottomBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (template : Set V) (E.rectTopBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (template : Set V) (E.rectLeftBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (template : Set V) (E.rectRightBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) := by
  obtain ⟨m, hm, hpm, hschedule⟩ := E.exists_alignedActiveSide_choice
    mu S p family hp verticalRequirement horizontalRequirement
      scaleCutoff hepsilon
  have hschedule' := hschedule
  obtain ⟨horizontal, vertical, _hh, _hv, _hvr, _hhr,
      _hLB, _hRB, _hLT, _hRT, _hBL, _hTL, _hBR, _hTR⟩ := hschedule
  let horizontalMargin := horizontal 0
  let verticalMargin := vertical 0
  obtain ⟨coordinateCutoff, hcoordinateCutoff⟩ := exists_nat_ge
    (max
      (E.orbitBoxCoordinateBound (P.bufferedRadius (connectorRadius m)) 0)
      (E.orbitBoxCoordinateBound (P.bufferedRadius (connectorRadius m)) 1))
  let extent := coordinateCutoff +
    2 * (family m).radiusBottom verticalMargin +
    2 * (family m).radiusTop verticalMargin +
    2 * (family m).radiusLeft horizontalMargin +
    2 * (family m).radiusRight horizontalMargin + 1
  have hcoordinateCutoffExtent : coordinateCutoff ≤ extent := by
    dsimp only [extent]
    omega
  have hcoordinateZero :
      E.orbitBoxCoordinateBound (P.bufferedRadius (connectorRadius m)) 0 ≤
        (extent : Real) :=
    (le_max_left _ _).trans <| hcoordinateCutoff.trans <| by
      exact_mod_cast hcoordinateCutoffExtent
  have hcoordinateOne :
      E.orbitBoxCoordinateBound (P.bufferedRadius (connectorRadius m)) 1 ≤
        (extent : Real) :=
    (le_max_right _ _).trans <| hcoordinateCutoff.trans <| by
      exact_mod_cast hcoordinateCutoffExtent
  have hconnector :
      (P.orbitBox (P.bufferedRadius (connectorRadius m)) : Set V) ⊆
        E.rectVertices (-(extent : Real)) extent
          (-(extent : Real)) extent := by
    intro v hv
    have hv0 := E.abs_vertexCoord_le_orbitBoxCoordinateBound hv (0 : Fin 2)
    have hv1 := E.abs_vertexCoord_le_orbitBoxCoordinateBound hv (1 : Fin 2)
    rw [abs_le] at hv0 hv1
    exact ⟨by linarith [hv0.1, hcoordinateZero],
      hv0.2.trans hcoordinateZero,
      by linarith [hv1.1, hcoordinateOne],
      hv1.2.trans hcoordinateOne⟩
  have hbottomWidth :
      2 * ((family m).radiusBottom verticalMargin : Int) ≤
        (extent : Int) - -(extent : Int) := by
    dsimp only [extent]
    push_cast
    omega
  have htopWidth :
      2 * ((family m).radiusTop verticalMargin : Int) ≤
        (extent : Int) - -(extent : Int) := by
    dsimp only [extent]
    push_cast
    omega
  have hbottomHeight :
      ((family m).radiusBottom verticalMargin : Int) ≤
        (extent : Int) - -(extent : Int) := by
    dsimp only [extent]
    push_cast
    omega
  have htopHeight :
      ((family m).radiusTop verticalMargin : Int) ≤
        (extent : Int) - -(extent : Int) := by
    dsimp only [extent]
    push_cast
    omega
  have hleftWidth :
      ((family m).radiusLeft horizontalMargin : Int) ≤
        (extent : Int) - -(extent : Int) := by
    dsimp only [extent]
    push_cast
    omega
  have hrightWidth :
      ((family m).radiusRight horizontalMargin : Int) ≤
        (extent : Int) - -(extent : Int) := by
    dsimp only [extent]
    push_cast
    omega
  have hleftHeight :
      2 * ((family m).radiusLeft horizontalMargin : Int) ≤
        (extent : Int) - -(extent : Int) := by
    dsimp only [extent]
    push_cast
    omega
  have hrightHeight :
      2 * ((family m).radiusRight horizontalMargin : Int) ≤
        (extent : Int) - -(extent : Int) := by
    dsimp only [extent]
    push_cast
    omega
  obtain ⟨bottom, top, left, right,
      hbottomSource, hbottomScore, htopSource, htopScore,
      hleftSource, hleftScore, hrightSource, hrightScore, hshared⟩ :=
    (family m).exists_sharedEndpointComponents E mu hTI
      verticalMargin horizontalMargin (-(extent : Int)) extent
        (-(extent : Int)) extent
      hbottomWidth htopWidth hbottomHeight htopHeight
      hleftWidth hrightWidth hleftHeight hrightHeight
  refine ⟨m, extent, bottom, top, left, right,
    hm, hpm, hschedule', hconnector, ?_⟩
  simpa only [Int.cast_neg, Int.cast_natCast] using
    And.intro hbottomSource <| And.intro hbottomScore <|
    And.intro htopSource <| And.intro htopScore <|
    And.intro hleftSource <| And.intro hleftScore <|
    And.intro hrightSource <| And.intro hrightScore hshared


theorem PeriodicPlaneEmbedding.exists_alignedSharedLevel_with_nextConnector
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (S : Nat → Finset V) (p : Nat → Real)
    (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (hp : Tendsto p atTop (nhds 1))
    (verticalRequirement horizontalRequirement : Nat → Nat → Nat)
    (scaleCutoff connectorRadius : Nat)
    {scoreEpsilon mergeEpsilon : Real}
    (hscoreEpsilon : 0 < scoreEpsilon)
    (hmergeEpsilon : 0 < mergeEpsilon) :
    ∃ m extent : Nat, ∃ bottom top left right : Finset V,
      ∃ nextConnector : Nat,
      scaleCutoff ≤ m ∧ connectorRadius ≤ nextConnector ∧
      1 - scoreEpsilon < p m ∧
      (family m).AlignedMarginSchedule E
        (verticalRequirement m) (horizontalRequirement m) ∧
      (P.orbitBox (P.bufferedRadius connectorRadius) : Set V) ⊆
        E.rectVertices (-(extent : Real)) extent
          (-(extent : Real)) extent ∧
      (bottom : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (bottom : Set V) (E.rectBottomBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      (top : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (top : Set V) (E.rectTopBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      (left : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (left : Set V) (E.rectLeftBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      (right : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (right : Set V) (E.rectRightBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      (let template :=
        P.fourBoundaryComponentTemplate bottom top left right
      (template : Set V) ⊆ E.rectVertices (-(extent : Real)) extent
        (-(extent : Real)) extent ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (template : Set V) (E.rectBottomBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (template : Set V) (E.rectTopBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (template : Set V) (E.rectLeftBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent)) ∧
      p m < mu.real (E.rectSideConnectionEvent
        (-(extent : Real)) extent (-(extent : Real)) extent
        (template : Set V) (E.rectRightBoundaryVertices
          (-(extent : Real)) extent (-(extent : Real)) extent))) ∧
      mu.real (P.pairMergeErrorUnion bottom top nextConnector) <
        mergeEpsilon ∧
      mu.real (P.pairMergeErrorUnion left right nextConnector) <
        mergeEpsilon := by
  obtain ⟨m, extent, bottom, top, left, right,
      hm, hpm, hschedule, hconnector,
      hbottomSource, hbottomComponent, htopSource, htopComponent,
      hleftSource, hleftComponent, hrightSource, hrightComponent,
      htemplate, hbottom, htop, hleftScore, hrightScore⟩ :=
    E.exists_alignedSharedLevel_choice mu hTI S p family hp
      verticalRequirement horizontalRequirement scaleCutoff
      (fun _ ↦ connectorRadius)
      hscoreEpsilon
  obtain ⟨nextConnector, hnextConnector, hverticalMerge,
      hhorizontalMerge⟩ :=
    P.exists_commonBoundaryPairMergeRadius mu hunique
      bottom top left right connectorRadius hmergeEpsilon
  exact ⟨m, extent, bottom, top, left, right, nextConnector,
    hm, hnextConnector, hpm, hschedule, hconnector,
    hbottomSource, hbottomComponent, htopSource, htopComponent,
    hleftSource, hleftComponent, hrightSource, hrightComponent,
    (by
      dsimp only
      exact ⟨htemplate, hbottom, htop, hleftScore, hrightScore⟩),
    hverticalMerge, hhorizontalMerge⟩


end StatMech.FK.PeriodicPlanar
