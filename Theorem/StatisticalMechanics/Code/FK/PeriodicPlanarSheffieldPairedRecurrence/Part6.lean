/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part4
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem nonempty_alignedNormalTwoRotatedEndpointPairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k : Nat) :
    Nonempty (AlignedNormalTwoRotatedEndpointPairedMixedBoundaryScores
      E Edual mu muDual S Sdual p pDual family familyDual schedule k) := by
  obtain ⟨normalThresholdX, normalThresholdY, hnormal⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E Edual mu muDual hTI hTIDual family familyDual schedule k
  obtain ⟨rotatedThresholdX, rotatedThresholdY, hrotated⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E.axisSwap Edual.axisSwap mu muDual
      (P.axisSwap_isTranslationInvariant mu hTI)
      (Pdual.axisSwap_isTranslationInvariant muDual hTIDual)
      family.axisSwap familyDual.axisSwap schedule.axisSwap k
  let normalX := max normalThresholdX rotatedThresholdY
  let rotatedHorizontalX := max rotatedThresholdX normalThresholdY
  let normalProbe := Classical.choice
    (hnormal (Nat.le_max_left _ _) le_rfl :
      Nonempty (AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
        S Sdual p pDual family familyDual schedule k normalX
        normalThresholdY))
  let rotatedProbe := Classical.choice
    (hrotated (Nat.le_max_left _ _) le_rfl :
      Nonempty (AlignedExactExtentPairedMixedBoundaryScores
        E.axisSwap Edual.axisSwap mu muDual S Sdual p pDual
        family.axisSwap familyDual.axisSwap schedule.axisSwap k
        rotatedHorizontalX rotatedThresholdY))
  let normalSpan := normalProbe.raw.wideRightInt -
    normalProbe.raw.wideLeftInt
  let rotatedHorizontalSpan := rotatedProbe.raw.wideRightInt -
    rotatedProbe.raw.wideLeftInt
  have hnormalSpan : 0 <= normalSpan := by
    exact (show (0 : Int) <= (normalX : Int) by omega).trans
      normalProbe.raw.extentX_le_wideSpan
  have hrotatedHorizontalSpan : 0 <= rotatedHorizontalSpan := by
    exact (show (0 : Int) <= (rotatedHorizontalX : Int) by omega).trans
      rotatedProbe.raw.extentX_le_wideSpan
  let normalY := rotatedHorizontalSpan.toNat
  let rotatedHorizontalY := normalSpan.toNat
  have hnormalThresholdY : normalThresholdY <= normalY := by
    have hX : normalThresholdY <= rotatedHorizontalX :=
      Nat.le_max_right _ _
    have hspan : (rotatedHorizontalX : Int) <=
        rotatedHorizontalSpan := by
      simpa only [rotatedHorizontalSpan] using
        rotatedProbe.raw.extentX_le_wideSpan
    have hXInt : (normalThresholdY : Int) <= rotatedHorizontalX := by
      exact_mod_cast hX
    rw [Int.le_toNat hrotatedHorizontalSpan]
    exact_mod_cast hXInt.trans hspan
  have hrotatedThresholdY : rotatedThresholdY <= rotatedHorizontalY := by
    have hX : rotatedThresholdY <= normalX := Nat.le_max_right _ _
    have hspan : (normalX : Int) <= normalSpan := by
      simpa only [normalSpan] using normalProbe.raw.extentX_le_wideSpan
    have hXInt : (rotatedThresholdY : Int) <= normalX := by
      exact_mod_cast hX
    rw [Int.le_toNat hnormalSpan]
    exact_mod_cast hXInt.trans hspan
  have hrotatedThresholdX : rotatedThresholdX <= normalY := by
    have hX : rotatedThresholdX <= rotatedHorizontalX :=
      Nat.le_max_left _ _
    have hspan : (rotatedHorizontalX : Int) <=
        rotatedHorizontalSpan := by
      simpa only [rotatedHorizontalSpan] using
        rotatedProbe.raw.extentX_le_wideSpan
    have hXInt : (rotatedThresholdX : Int) <= rotatedHorizontalX := by
      exact_mod_cast hX
    rw [Int.le_toNat hrotatedHorizontalSpan]
    exact_mod_cast hXInt.trans hspan
  let normal := Classical.choice
    (hnormal (extentX := normalX) (extentY := normalY)
      (Nat.le_max_left _ _) hnormalThresholdY)
  let rotatedVertical := Classical.choice
    (hrotated (extentX := normalY) (extentY := normalX)
      hrotatedThresholdX (Nat.le_max_right _ _))
  let rotatedHorizontal := Classical.choice
    (hrotated (extentX := rotatedHorizontalX)
      (extentY := rotatedHorizontalY)
      (Nat.le_max_left _ _) hrotatedThresholdY)
  refine ⟨{
    normalX := normalX
    normalY := normalY
    rotatedHorizontalX := rotatedHorizontalX
    rotatedHorizontalY := rotatedHorizontalY
    normal := normal
    rotatedVertical := rotatedVertical
    rotatedHorizontal := rotatedHorizontal
    normalSpan_eq := ?_
    rotatedHorizontalSpan_eq := ?_ }⟩
  · calc
      normal.raw.wideRightInt - normal.raw.wideLeftInt =
          pairedWideSpanAtExtentX E Edual family familyDual schedule k
            normalX := normal.wideSpan_formula
      _ = normalSpan := by
        symm
        simpa only [normalSpan] using normalProbe.wideSpan_formula
      _ = (rotatedHorizontalY : Int) := by
        rw [Int.toNat_of_nonneg hnormalSpan]
  · calc
      rotatedHorizontal.raw.wideRightInt -
          rotatedHorizontal.raw.wideLeftInt =
          pairedWideSpanAtExtentX E.axisSwap Edual.axisSwap
            family.axisSwap familyDual.axisSwap schedule.axisSwap k
            rotatedHorizontalX := rotatedHorizontal.wideSpan_formula
      _ = rotatedHorizontalSpan := by
        symm
        simpa only [rotatedHorizontalSpan] using
          rotatedProbe.wideSpan_formula
      _ = (normalY : Int) := by
        rw [Int.toNat_of_nonneg hrotatedHorizontalSpan]


theorem PeriodicPlaneEmbedding.horizontalCrossing_translate_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    (a b c d : Real) :
    mu.real (E.horizontalCrossingEvent a b c d) <=
      mu.real (E.horizontalCrossingEvent
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real))) := by
  let A := E.horizontalCrossingEvent a b c d
  let translated := E.horizontalCrossingEvent
    (a + (z 0 : Real)) (b + (z 0 : Real))
    (c + (z 1 : Real)) (d + (z 1 : Real))
  have hsub : A <= P.translateEvent z translated := by
    intro omega homega
    change E.rectRestrict a b c d omega ∈
      E.finiteHorizontalCrossing a b c d at homega
    obtain ⟨x, y, hxLeft, hyRight, hxy⟩ := homega
    have hx' : P.shift z x.1 ∈ E.rectVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) :=
      (E.shift_mem_rectVertices z a b c d x.1).2 x.2
    have hy' : P.shift z y.1 ∈ E.rectVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) :=
      (E.shift_mem_rectVertices z a b c d y.1).2 y.2
    have hxBoundary := (E.shift_mem_rectLeftBoundaryVertices
      z a b c d x.1).2 ⟨x.2, hxLeft⟩
    have hyBoundary := (E.shift_mem_rectRightBoundaryVertices
      z a b c d y.1).2 ⟨y.2, hyRight⟩
    rw [E.openSub_rectRestrict_eq_induce] at hxy
    obtain ⟨path⟩ := hxy
    let ambientPath : (P.openSubgraph omega).Walk x.1 y.1 :=
      path.map (SimpleGraph.Embedding.induce
        (E.rectVertices a b c d)).toHom
    let translatedPath :=
      ambientPath.map (P.openSubgraphTranslateHom z omega)
    have htranslatedPath : ∀ v ∈ translatedPath.support,
        v ∈ E.rectVertices
          (a + (z 0 : Real)) (b + (z 0 : Real))
          (c + (z 1 : Real)) (d + (z 1 : Real)) := by
      intro v hv
      simp only [translatedPath, SimpleGraph.Walk.support_map,
        List.mem_map] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      change w ∈ (path.map (SimpleGraph.Embedding.induce
        (E.rectVertices a b c d)).toHom).support at hw
      rw [SimpleGraph.Walk.support_map] at hw
      obtain ⟨u, _hu, huw⟩ := List.mem_map.mp hw
      rw [← huw]
      exact (E.shift_mem_rectVertices z a b c d u.1).2 u.2
    change E.rectRestrict
      (a + (z 0 : Real)) (b + (z 0 : Real))
      (c + (z 1 : Real)) (d + (z 1 : Real))
      (P.configTranslate z omega) ∈ E.finiteHorizontalCrossing
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real))
    refine ⟨⟨P.shift z x.1, hx'⟩, ⟨P.shift z y.1, hy'⟩,
      hxBoundary.2, hyBoundary.2, ?_⟩
    rw [E.openSub_rectRestrict_eq_induce]
    exact ⟨translatedPath.induce _ htranslatedPath⟩
  have hmeasure : mu.real A <=
      mu.real (P.translateEvent z translated) := measureReal_mono hsub
  change mu.real A <= mu.real translated
  calc
    mu.real A <= mu.real (P.translateEvent z translated) := hmeasure
    _ = mu.real translated := by
      unfold Measure.real
      rw [P.translateEvent_measure_eq mu hTI z
        (E.horizontalCrossingEvent_measurableSet _ _ _ _)]


theorem PeriodicPlaneEmbedding.verticalCrossing_translate_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    (a b c d : Real) :
    mu.real (E.verticalCrossingEvent a b c d) <=
      mu.real (E.verticalCrossingEvent
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real))) := by
  let A := E.verticalCrossingEvent a b c d
  let translated := E.verticalCrossingEvent
    (a + (z 0 : Real)) (b + (z 0 : Real))
    (c + (z 1 : Real)) (d + (z 1 : Real))
  have hsub : A <= P.translateEvent z translated := by
    intro omega homega
    change E.rectRestrict a b c d omega ∈
      E.finiteVerticalCrossing a b c d at homega
    obtain ⟨x, y, hxBottom, hyTop, hxy⟩ := homega
    have hx' : P.shift z x.1 ∈ E.rectVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) :=
      (E.shift_mem_rectVertices z a b c d x.1).2 x.2
    have hy' : P.shift z y.1 ∈ E.rectVertices
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real)) :=
      (E.shift_mem_rectVertices z a b c d y.1).2 y.2
    have hxBoundary := (E.shift_mem_rectBottomBoundaryVertices
      z a b c d x.1).2 ⟨x.2, hxBottom⟩
    have hyBoundary := (E.shift_mem_rectTopBoundaryVertices
      z a b c d y.1).2 ⟨y.2, hyTop⟩
    rw [E.openSub_rectRestrict_eq_induce] at hxy
    obtain ⟨path⟩ := hxy
    let ambientPath : (P.openSubgraph omega).Walk x.1 y.1 :=
      path.map (SimpleGraph.Embedding.induce
        (E.rectVertices a b c d)).toHom
    let translatedPath :=
      ambientPath.map (P.openSubgraphTranslateHom z omega)
    have htranslatedPath : ∀ v ∈ translatedPath.support,
        v ∈ E.rectVertices
          (a + (z 0 : Real)) (b + (z 0 : Real))
          (c + (z 1 : Real)) (d + (z 1 : Real)) := by
      intro v hv
      simp only [translatedPath, SimpleGraph.Walk.support_map,
        List.mem_map] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      change w ∈ (path.map (SimpleGraph.Embedding.induce
        (E.rectVertices a b c d)).toHom).support at hw
      rw [SimpleGraph.Walk.support_map] at hw
      obtain ⟨u, _hu, huw⟩ := List.mem_map.mp hw
      rw [← huw]
      exact (E.shift_mem_rectVertices z a b c d u.1).2 u.2
    change E.rectRestrict
      (a + (z 0 : Real)) (b + (z 0 : Real))
      (c + (z 1 : Real)) (d + (z 1 : Real))
      (P.configTranslate z omega) ∈ E.finiteVerticalCrossing
        (a + (z 0 : Real)) (b + (z 0 : Real))
        (c + (z 1 : Real)) (d + (z 1 : Real))
    refine ⟨⟨P.shift z x.1, hx'⟩, ⟨P.shift z y.1, hy'⟩,
      hxBoundary.2, hyBoundary.2, ?_⟩
    rw [E.openSub_rectRestrict_eq_induce]
    exact ⟨translatedPath.induce _ htranslatedPath⟩
  have hmeasure : mu.real A <=
      mu.real (P.translateEvent z translated) := measureReal_mono hsub
  change mu.real A <= mu.real translated
  calc
    mu.real A <= mu.real (P.translateEvent z translated) := hmeasure
    _ = mu.real translated := by
      unfold Measure.real
      rw [P.translateEvent_measure_eq mu hTI z
        (E.verticalCrossingEvent_measurableSet _ _ _ _)]


theorem PeriodicPlaneEmbedding.horizontalCrossing_translate_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Nat -> Site 2) (a b c d : Nat -> Real)
    (hlimit : Tendsto (fun n => mu.real
      (E.horizontalCrossingEvent (a n) (b n) (c n) (d n)))
      atTop (nhds 1)) :
    Tendsto (fun n => mu.real (E.horizontalCrossingEvent
      (a n + (z n 0 : Real)) (b n + (z n 0 : Real))
      (c n + (z n 1 : Real)) (d n + (z n 1 : Real))))
      atTop (nhds 1) := by
  exact hlimit.squeeze tendsto_const_nhds
    (fun n => E.horizontalCrossing_translate_measureReal_le
      mu hTI (z n) (a n) (b n) (c n) (d n))
    (fun _ => measureReal_le_one)


theorem PeriodicPlaneEmbedding.verticalCrossing_translate_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Nat -> Site 2) (a b c d : Nat -> Real)
    (hlimit : Tendsto (fun n => mu.real
      (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
      atTop (nhds 1)) :
    Tendsto (fun n => mu.real (E.verticalCrossingEvent
      (a n + (z n 0 : Real)) (b n + (z n 0 : Real))
      (c n + (z n 1 : Real)) (d n + (z n 1 : Real))))
      atTop (nhds 1) := by
  exact hlimit.squeeze tendsto_const_nhds
    (fun n => E.verticalCrossing_translate_measureReal_le
      mu hTI (z n) (a n) (b n) (c n) (d n))
    (fun _ => measureReal_le_one)


theorem PeriodicPlaneEmbedding.crossingMax_independent_translate_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (zH zV : Nat -> Site 2)
    (aH bH cH dH aV bV cV dV : Nat -> Real)
    (hlimit : Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (aH n) (bH n) (cH n) (dH n)))
      (mu.real (E.verticalCrossingEvent
        (aV n) (bV n) (cV n) (dV n)))) atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (aH n + (zH n 0 : Real)) (bH n + (zH n 0 : Real))
        (cH n + (zH n 1 : Real)) (dH n + (zH n 1 : Real))))
      (mu.real (E.verticalCrossingEvent
        (aV n + (zV n 0 : Real)) (bV n + (zV n 0 : Real))
        (cV n + (zV n 1 : Real)) (dV n + (zV n 1 : Real)))))
      atTop (nhds 1) := by
  exact hlimit.squeeze tendsto_const_nhds
    (fun n => max_le_max
      (E.horizontalCrossing_translate_measureReal_le
        mu hTI (zH n) (aH n) (bH n) (cH n) (dH n))
      (E.verticalCrossing_translate_measureReal_le
        mu hTI (zV n) (aV n) (bV n) (cV n) (dV n)))
    (fun _ => max_le measureReal_le_one measureReal_le_one)


theorem exists_matched_commonSquareNormalBoundaryBandData_ge
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W))) [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {margin : Nat}
    {p pDual : Real}
    (primal : E.NormalBoundaryBandSeed mu S margin p)
    (dual : Edual.NormalBoundaryBandSeed muDual Sdual margin pDual)
    (lower : Nat) :
    exists M : Nat, lower <= M /\
      Nonempty (E.CommonSquareNormalBoundaryBandData
        mu S margin M p) /\
      Nonempty (Edual.CommonSquareNormalBoundaryBandData
        muDual Sdual margin M pDual) := by
  let M0 := commonPrimalDualBandHalfWidth
    primal.radiusLeft primal.radiusRight
    primal.radiusBottom primal.radiusTop
    dual.radiusLeft dual.radiusRight
    dual.radiusBottom dual.radiusTop
  let M := max M0 lower
  have hM0 : M0 <= M := Nat.le_max_left _ _
  have h := le_commonPrimalDualBandHalfWidth
    primal.radiusLeft primal.radiusRight
    primal.radiusBottom primal.radiusTop
    dual.radiusLeft dual.radiusRight
    dual.radiusBottom dual.radiusTop
  dsimp only at h
  refine ⟨M, Nat.le_max_right _ _, ?_, ?_⟩
  · exact Nonempty.intro <| primal.toCommonSquare E mu hTI M
      (h.1.trans hM0) (h.2.1.trans hM0)
      (h.2.2.1.trans hM0) (h.2.2.2.1.trans hM0)
  · exact Nonempty.intro <| dual.toCommonSquare Edual muDual hTIDual M
      (h.2.2.2.2.1.trans hM0) (h.2.2.2.2.2.1.trans hM0)
      (h.2.2.2.2.2.2.1.trans hM0) (h.2.2.2.2.2.2.2.trans hM0)


theorem PeriodicPlaneEmbedding.exists_commonSquareNormalBoundaryBands_outward
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (score : Nat -> Real) (margin M : Nat -> Nat)
    (data : forall n, E.CommonSquareNormalBoundaryBandData
      mu (P.orbitBox n) (margin n) (M n) (score n))
    (hscore : Tendsto score atTop (nhds 1))
    (_hscore_le : forall n, score n <= 1)
    (pad : Nat -> Int) (hpad : forall n, 0 <= pad n) :
    exists radius : Nat -> Nat, forall
      (width height : Nat -> Nat)
      (hwidth : forall n, 0 < width n)
      (hheight : forall n, 0 < height n),
      (forall n, E.orbitBoxCoordinateBound
        (P.bufferedRadius (radius n)) (0 : Fin 2) <= M n) ->
      (forall n, E.orbitBoxCoordinateBound
        (P.bufferedRadius (radius n)) (1 : Fin 2) <= M n) ->
      Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent
          (-(M n : Real)) (M n + width n : Real)
          (-(M n : Real) - pad n) (M n + height n + pad n : Real)))
        (mu.real (E.horizontalCrossingEvent
          (-(M n : Real) - pad n) (M n + width n + pad n : Real)
          (-(M n : Real)) (M n + height n : Real))))
        atTop (nhds 1) := by
  let zLeft : Nat -> Site 2 := fun n => (data n).zLeft
  let zRight : Nat -> Site 2 := fun n => (data n).zRight
  let zBottom : Nat -> Site 2 := fun n => (data n).zBottom
  let zTop : Nat -> Site 2 := fun n => (data n).zTop
  have hleftSubset (n : Nat) :
      ((P.orbitBox n).image (P.shift (zLeft n)) : Set V) <=
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real) := by
    simpa [zLeft] using ((data n).left (0 : Fin (margin n + 1))).1
  have hrightSubset (n : Nat) :
      ((P.orbitBox n).image (P.shift (zRight n)) : Set V) <=
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real) := by
    simpa [zRight] using ((data n).right (0 : Fin (margin n + 1))).1
  have hbottomSubset (n : Nat) :
      ((P.orbitBox n).image (P.shift (zBottom n)) : Set V) <=
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real) := by
    simpa [zBottom] using ((data n).bottom (0 : Fin (margin n + 1))).1
  have htopSubset (n : Nat) :
      ((P.orbitBox n).image (P.shift (zTop n)) : Set V) <=
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real) := by
    simpa [zTop] using ((data n).top (0 : Fin (margin n + 1))).1
  have hleftLower (n : Nat) : score n < mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zLeft n)) : Set V)
        (E.rectLeftBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))) := by
    simpa [zLeft] using ((data n).left (0 : Fin (margin n + 1))).2
  have hrightLower (n : Nat) : score n < mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zRight n)) : Set V)
        (E.rectRightBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))) := by
    simpa [zRight] using ((data n).right (0 : Fin (margin n + 1))).2
  have hbottomLower (n : Nat) : score n < mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zBottom n)) : Set V)
        (E.rectBottomBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))) := by
    simpa [zBottom] using ((data n).bottom (0 : Fin (margin n + 1))).2
  have htopLower (n : Nat) : score n < mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zTop n)) : Set V)
        (E.rectTopBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))) := by
    simpa [zTop] using ((data n).top (0 : Fin (margin n + 1))).2
  have hleftLimit := hscore.squeeze tendsto_const_nhds
    (fun n => le_of_lt (hleftLower n)) (fun _ => measureReal_le_one)
  have hrightLimit := hscore.squeeze tendsto_const_nhds
    (fun n => le_of_lt (hrightLower n)) (fun _ => measureReal_le_one)
  have hbottomLimit := hscore.squeeze tendsto_const_nhds
    (fun n => le_of_lt (hbottomLower n)) (fun _ => measureReal_le_one)
  have htopLimit := hscore.squeeze tendsto_const_nhds
    (fun n => le_of_lt (htopLower n)) (fun _ => measureReal_le_one)
  exact E.exists_fourShiftTemplate_outward_crossing_max_tendsto_one_of_coordinateBounds
    mu hFKG hTI hunique M zLeft zRight zBottom zTop
    hleftSubset hrightSubset hbottomSubset htopSubset
    hleftLimit hrightLimit hbottomLimit htopLimit pad hpad


theorem PeriodicPlaneEmbedding.exists_pointwise_commonSquareNormalBoundaryBands_outward
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (score : Nat -> Nat -> Real)
    (margin M : Nat -> Nat -> Nat)
    (data : forall k n, E.CommonSquareNormalBoundaryBandData
      mu (P.orbitBox n) (margin k n) (M k n) (score k n))
    (hscore : forall k, Tendsto (score k) atTop (nhds 1))
    (hscore_le : forall k n, score k n <= 1)
    (pad : Nat -> Nat -> Int) (hpad : forall k n, 0 <= pad k n)
    (width height : Nat -> Nat -> Nat)
    (hwidth : forall k n, 0 < width k n)
    (hheight : forall k n, 0 < height k n) :
    exists radius : Nat -> Nat -> Nat,
      (forall k n, E.orbitBoxCoordinateBound
        (P.bufferedRadius (radius k n)) (0 : Fin 2) <= M k n) ->
      (forall k n, E.orbitBoxCoordinateBound
        (P.bufferedRadius (radius k n)) (1 : Fin 2) <= M k n) ->
      forall k, Tendsto (fun n => max
        (mu.real (E.verticalCrossingEvent
          (-(M k n : Real)) (M k n + width k n : Real)
          (-(M k n : Real) - pad k n)
          (M k n + height k n + pad k n : Real)))
        (mu.real (E.horizontalCrossingEvent
          (-(M k n : Real) - pad k n)
          (M k n + width k n + pad k n : Real)
          (-(M k n : Real)) (M k n + height k n : Real))))
        atTop (nhds 1) := by
  have hexists (k : Nat) :=
    E.exists_commonSquareNormalBoundaryBands_outward mu hFKG hTI hunique
      (score k) (margin k) (M k) (data k) (hscore k) (hscore_le k)
      (pad k) (hpad k)
  let radius : Nat -> Nat -> Nat := fun k => Classical.choose (hexists k)
  have hcross (k : Nat) := Classical.choose_spec (hexists k)
  refine ⟨radius, ?_⟩
  intro hx hy k
  exact hcross k (width k) (height k) (hwidth k) (hheight k)
    (hx k) (hy k)


end StatMech.FK.PeriodicPlanar
