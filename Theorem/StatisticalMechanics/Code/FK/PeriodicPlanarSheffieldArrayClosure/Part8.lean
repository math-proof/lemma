/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicPlaneEmbedding.nonempty_alignedSharedLevelStep
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (S : Nat → Finset V) (p : Nat → Real)
    (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (hp : Tendsto p atTop (nhds 1))
    (verticalRequirement horizontalRequirement : Nat → Nat → Nat)
    (previousScale previousConnector : Nat)
    {scoreEpsilon mergeEpsilon : Real}
    (hscoreEpsilon : 0 < scoreEpsilon)
    (hmergeEpsilon : 0 < mergeEpsilon) :
    Nonempty (E.AlignedSharedLevelStep mu S p family
      verticalRequirement horizontalRequirement previousScale
      previousConnector scoreEpsilon mergeEpsilon) := by
  obtain ⟨scale, extent, bottom, top, left, right, nextConnector,
      hscale, hconnectorMono, hthreshold, hschedule, hconnector,
      hbottomSource, hbottomComponent, htopSource, htopComponent,
      hleftSource, hleftComponent, hrightSource, hrightComponent,
      htemplateData,
      hvertical, hhorizontal⟩ :=
    E.exists_alignedSharedLevel_with_nextConnector mu hTI hunique
      S p family hp verticalRequirement horizontalRequirement
      previousScale previousConnector hscoreEpsilon hmergeEpsilon
  dsimp only at htemplateData
  rcases htemplateData with
    ⟨htemplate, hbottom, htop, hleftScore, hrightScore⟩
  exact ⟨{
    scale := scale
    extent := extent
    bottom := bottom
    top := top
    left := left
    right := right
    nextConnector := nextConnector
    scale_ge := hscale
    connector_mono := hconnectorMono
    threshold_gt := hthreshold
    schedule := hschedule
    connector_subset := hconnector
    bottom_subset := hbottomSource
    bottomComponentScore := hbottomComponent
    top_subset := htopSource
    topComponentScore := htopComponent
    left_subset := hleftSource
    leftComponentScore := hleftComponent
    right_subset := hrightSource
    rightComponentScore := hrightComponent
    template_subset := htemplate
    bottomScore := hbottom
    topScore := htop
    leftScore := hleftScore
    rightScore := hrightScore
    verticalMerge := hvertical
    horizontalMerge := hhorizontal }⟩


theorem PeriodicPlaneEmbedding.exists_recursiveAlignedSharedLevelSteps
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (S : Nat → Finset V) (p : Nat → Real)
    (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (hp : Tendsto p atTop (nhds 1))
    (verticalRequirement horizontalRequirement : Nat → Nat → Nat)
    (scoreEpsilon mergeEpsilon : Nat → Real)
    (hscoreEpsilon : ∀ n, 0 < scoreEpsilon n)
    (hmergeEpsilon : ∀ n, 0 < mergeEpsilon n) :
    ∃ state : Nat → Nat × Nat,
      ∃ steps : ∀ n, E.AlignedSharedLevelStep mu S p family
        verticalRequirement horizontalRequirement
        (state n).1 (state n).2 (scoreEpsilon n) (mergeEpsilon n),
      state 0 = (0, 0) ∧
      ∀ n, state (n + 1) = ((steps n).scale + 1,
        (steps n).nextConnector) := by
  let chooseStep (n : Nat) (state : Nat × Nat) :
      E.AlignedSharedLevelStep mu S p family
        verticalRequirement horizontalRequirement
        state.1 state.2 (scoreEpsilon n) (mergeEpsilon n) :=
    Classical.choice (E.nonempty_alignedSharedLevelStep
      mu hTI hunique S p family hp verticalRequirement horizontalRequirement
      state.1 state.2 (hscoreEpsilon n) (hmergeEpsilon n))
  let state : Nat → Nat × Nat := fun n ↦
    Nat.rec (0, 0) (fun n previous ↦
      let step := chooseStep n previous
      (step.scale + 1, step.nextConnector)) n
  let steps : ∀ n, E.AlignedSharedLevelStep mu S p family
      verticalRequirement horizontalRequirement
      (state n).1 (state n).2 (scoreEpsilon n) (mergeEpsilon n) :=
    fun n ↦ chooseStep n (state n)
  refine ⟨state, steps, rfl, ?_⟩
  intro n
  simp only [state, steps, Nat.rec_add_one]


theorem uniform_cofinal_diagonal_below_growing_cutoff
    (f : Nat → Nat → Real)
    (hf : ∀ k, Tendsto (f k) atTop (nhds 1))
    (hle : ∀ k n, f k n ≤ 1) (cutoff : Nat → Nat) :
    ∃ index : Nat → Nat,
      (∀ n, max n (cutoff n) ≤ index n) ∧
      ∀ k : Nat → Nat, (∀ n, k n < n + 1) →
        Tendsto (fun n ↦ f (k n) (index n)) atTop (nhds 1) := by
  let defect : Nat → Nat → Real := fun k n ↦ 1 - f k n
  have hdefect (k : Nat) : Tendsto (defect k) atTop (nhds 0) := by
    simpa [defect] using
      (tendsto_const_nhds (x := (1 : Real))).sub (hf k)
  have hrow (n : Nat) : Tendsto
      (fun m ↦ ∑ k ∈ Finset.range (n + 1), defect k m)
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum (Finset.range (n + 1))
      (fun k _hk ↦ hdefect k)
  have hepsilon (n : Nat) : 0 < (1 : Real) / (n + 1) := by positivity
  choose threshold hthreshold using fun n ↦
    (Metric.tendsto_atTop.1 (hrow n))
      ((1 : Real) / (n + 1)) (hepsilon n)
  let index : Nat → Nat := fun n ↦
    max (max n (cutoff n)) (threshold n)
  have hindex (n : Nat) : max n (cutoff n) ≤ index n :=
    Nat.le_max_left _ _
  have hdist (n : Nat) :
      dist (∑ k ∈ Finset.range (n + 1), defect k (index n)) 0 <
        (1 : Real) / (n + 1) :=
    hthreshold n (index n) (Nat.le_max_right _ _)
  have hsum : Tendsto
      (fun n ↦ ∑ k ∈ Finset.range (n + 1), defect k (index n))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero (fun _ ↦ abs_nonneg _) _
      tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    simpa only [Real.dist_eq, sub_zero] using le_of_lt (hdist n)
  refine ⟨index, hindex, ?_⟩
  intro k hk
  have hnonneg (n : Nat) : 0 ≤ defect (k n) (index n) :=
    sub_nonneg.mpr (hle (k n) (index n))
  have hupper (n : Nat) : defect (k n) (index n) ≤
      ∑ j ∈ Finset.range (n + 1), defect j (index n) := by
    exact Finset.single_le_sum
      (s := Finset.range (n + 1))
      (f := fun j ↦ defect j (index n))
      (fun j _hj ↦ sub_nonneg.mpr (hle j (index n)))
      (Finset.mem_range.mpr (hk n))
  have hzero : Tendsto (fun n ↦ defect (k n) (index n))
      atTop (nhds 0) := squeeze_zero hnonneg hupper hsum
  have hone := (tendsto_const_nhds (x := (1 : Real))).sub hzero
  simpa [defect] using hone


theorem exists_cofinalIndex_uniform_tendsto_one_below_diagonal
    (f : Nat → Nat → Real)
    (hf : ∀ k, Tendsto (f k) atTop (nhds 1))
    (hle : ∀ k n, f k n ≤ 1) :
    ∃ index : Nat → Nat, (∀ n, n ≤ index n) ∧
      ∀ k : Nat → Nat, (∀ n, k n < n + 1) →
        Tendsto (fun n ↦ f (k n) (index n)) atTop (nhds 1) := by
  let defect : Nat → Nat → Real := fun k n ↦ 1 - f k n
  have hdefect (k : Nat) : Tendsto (defect k) atTop (nhds 0) := by
    simpa [defect] using
      (tendsto_const_nhds (x := (1 : Real))).sub (hf k)
  obtain ⟨index, hindex, hsum⟩ :=
    exists_cofinalIndex_finsetSum_tendsto_zero defect hdefect
  refine ⟨index, hindex, ?_⟩
  intro k hk
  have hnonneg (n : Nat) : 0 ≤ defect (k n) (index n) := by
    exact sub_nonneg.mpr (hle (k n) (index n))
  have hupper (n : Nat) : defect (k n) (index n) ≤
      ∑ j ∈ Finset.range (n + 1), defect j (index n) := by
    exact Finset.single_le_sum
      (s := Finset.range (n + 1))
      (f := fun j ↦ defect j (index n))
      (fun j _hj ↦ sub_nonneg.mpr (hle j (index n)))
      (Finset.mem_range.mpr (hk n))
  have hzero : Tendsto (fun n ↦ defect (k n) (index n))
      atTop (nhds 0) := squeeze_zero hnonneg hupper hsum
  have hone := (tendsto_const_nhds (x := (1 : Real))).sub hzero
  simpa [defect] using hone


theorem PeriodicPlaneEmbedding.verticalCrossing_tendsto_one_of_boundaryScores
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (a b c d : Nat → Real) (bottomSource topSource : Nat → Finset V)
    (hbottom : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        (bottomSource n : Set V)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1))
    (htop : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        (topSource n : Set V)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1))
    (hmerge : Tendsto (fun n ↦ mu.real
      (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
        (bottomSource n) (topSource n))) atTop (nhds 0)) :
    Tendsto (fun n ↦ mu.real
      (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
      atTop (nhds 1) := by
  let A : Nat → Real := fun n ↦ mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      (bottomSource n : Set V)
      (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  let H : Nat → Real := fun n ↦ mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      (topSource n : Set V)
      (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))
  let M : Nat → Real := fun n ↦ mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
      (bottomSource n) (topSource n))
  let C : Nat → Real := fun n ↦ mu.real
    (E.verticalCrossingEvent (a n) (b n) (c n) (d n))
  have hlower (n : Nat) : A n * H n - M n ≤ C n := by
    simpa only [A, H, M, C] using
      E.verticalCrossing_measureReal_ge_side_mul_sub_mergeError
        mu hFKG (a n) (b n) (c n) (d n)
          (bottomSource n) (topSource n)
  have hbound : Tendsto (fun n ↦ A n * H n - M n)
      atTop (nhds 1) := by
    convert hbottom.mul htop |>.sub hmerge using 1 <;> norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hbound tendsto_const_nhds hlower (fun _ ↦ measureReal_le_one)


theorem PeriodicPlaneEmbedding.horizontalCrossing_tendsto_one_of_boundaryScores
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (a b c d : Nat → Real) (leftSource rightSource : Nat → Finset V)
    (hleft : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        (leftSource n : Set V)
        (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1))
    (hright : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        (rightSource n : Set V)
        (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n))))
      atTop (nhds 1))
    (hmerge : Tendsto (fun n ↦ mu.real
      (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
        (leftSource n) (rightSource n))) atTop (nhds 0)) :
    Tendsto (fun n ↦ mu.real
      (E.horizontalCrossingEvent (a n) (b n) (c n) (d n)))
      atTop (nhds 1) := by
  let A : Nat → Real := fun n ↦ mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      (leftSource n : Set V)
      (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  let H : Nat → Real := fun n ↦ mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      (rightSource n : Set V)
      (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))
  let M : Nat → Real := fun n ↦ mu.real
    (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n)
      (leftSource n) (rightSource n))
  let C : Nat → Real := fun n ↦ mu.real
    (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))
  have hlower (n : Nat) : A n * H n - M n ≤ C n := by
    simpa only [A, H, M, C] using
      E.horizontalCrossing_measureReal_ge_side_mul_sub_mergeError
        mu hFKG (a n) (b n) (c n) (d n)
          (leftSource n) (rightSource n)
  have hbound : Tendsto (fun n ↦ A n * H n - M n)
      atTop (nhds 1) := by
    convert hleft.mul hright |>.sub hmerge using 1 <;> norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hbound tendsto_const_nhds hlower (fun _ ↦ measureReal_le_one)


theorem PeriodicPlaneEmbedding.preferenceGrid_orbitBox_subset_translated_rect
    (E : PeriodicPlaneEmbedding P) (R M width height : Nat) (z : Site 2)
    (hx : E.orbitBoxCoordinateBound R (0 : Fin 2) ≤ M)
    (hy : E.orbitBoxCoordinateBound R (1 : Fin 2) ≤ M) :
    ∀ v : PreferenceGridVertex width height,
      P.shift (preferenceGridSite v + z) '' (P.orbitBox R : Set V) ⊆
        E.rectVertices (-(M : Real) + z 0) (M + width + z 0 : Real)
          (-(M : Real) + z 1) (M + height + z 1 : Real) := by
  intro v _ hmem
  obtain ⟨u, hu, rfl⟩ := hmem
  rw [P.shift_add]
  apply (E.shift_mem_rectVertices z (-(M : Real)) (M + width : Real)
    (-(M : Real)) (M + height : Real) _).2
  exact E.preferenceGrid_orbitBox_subset_rect_of_coordinateBound
    R M width height hx hy v ⟨u, hu, rfl⟩

set_option linter.unusedVariables false in


theorem PeriodicPlaneEmbedding.exists_fourShiftTemplate_outward_crossing_max_tendsto_one_of_connector
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (M : Nat → Nat) (zLeft zRight zBottom zTop : Nat → Site 2)
    (hleft : ∀ n,
      ((P.orbitBox n).image (P.shift (zLeft n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))
    (hright : ∀ n,
      ((P.orbitBox n).image (P.shift (zRight n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))
    (hbottom : ∀ n,
      ((P.orbitBox n).image (P.shift (zBottom n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))
    (htop : ∀ n,
      ((P.orbitBox n).image (P.shift (zTop n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))
    (hleftLimit : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zLeft n)) : Set V)
        (E.rectLeftBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (hrightLimit : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zRight n)) : Set V)
        (E.rectRightBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (hbottomLimit : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zBottom n)) : Set V)
        (E.rectBottomBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (htopLimit : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zTop n)) : Set V)
        (E.rectTopBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (pad : Nat → Int) (hpad : ∀ n, 0 ≤ pad n) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n),
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (preferenceGridSite v + verticalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (-(M n : Real)) (M n + width n : Real)
              (-(M n : Real) - pad n) (M n + height n - pad n : Real)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (preferenceGridSite v + verticalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (-(M n : Real)) (M n + width n : Real)
              (-(M n : Real) - pad n) (M n + height n + pad n : Real)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (preferenceGridSite v + horizontalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (-(M n : Real) - pad n)
              (M n + width n - pad n : Real)
              (-(M n : Real)) (M n + height n : Real)) →
      (∀ n (v : PreferenceGridVertex (width n) (height n)),
        (P.shift (preferenceGridSite v + horizontalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
            E.rectVertices (-(M n : Real) - pad n)
              (M n + width n + pad n : Real)
              (-(M n : Real)) (M n + height n : Real)) →
      Tendsto (fun n ↦ max
        (mu.real (E.verticalCrossingEvent
          (-(M n : Real)) (M n + width n : Real)
          (-(M n : Real) - pad n) (M n + height n + pad n : Real)))
        (mu.real (E.horizontalCrossingEvent
          (-(M n : Real) - pad n) (M n + width n + pad n : Real)
          (-(M n : Real)) (M n + height n : Real))))
        atTop (nhds 1) := by
  let template : Nat → Finset V := fun n ↦
    P.fourShiftTemplate (P.orbitBox n) (zLeft n) (zRight n)
      (zBottom n) (zTop n)
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun _ h ↦ h.1
  have htemplateHit : Tendsto (fun n ↦
      mu.real (P.setHitsInfinite (template n : Set V)))
      atTop (nhds 1) := by
    simpa only [template] using
      P.fourShiftTemplate_hitsInfinite_tendsto_one mu hTI hexists
        zLeft zRight zBottom zTop
  obtain ⟨radius, hcross⟩ :=
    E.exists_uniformTemplate_outwardBoundaryScores_crossing_max_tendsto_one
      mu hFKG hTI hunique template htemplateHit pad hpad
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight
    hconnectorV0 hconnectorV1 hconnectorH0 hconnectorH1
  let bottom : Nat → Real := fun n ↦ mu.real
    (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
      (-(M n : Real)) (M n : Real)
      ((P.orbitBox n).image (P.shift (zBottom n)) : Set V)
      (E.rectBottomBoundaryVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)))
  let top : Nat → Real := fun n ↦ mu.real
    (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
      (-(M n : Real)) (M n : Real)
      ((P.orbitBox n).image (P.shift (zTop n)) : Set V)
      (E.rectTopBoundaryVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)))
  let left : Nat → Real := fun n ↦ mu.real
    (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
      (-(M n : Real)) (M n : Real)
      ((P.orbitBox n).image (P.shift (zLeft n)) : Set V)
      (E.rectLeftBoundaryVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)))
  let right : Nat → Real := fun n ↦ mu.real
    (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
      (-(M n : Real)) (M n : Real)
      ((P.orbitBox n).image (P.shift (zRight n)) : Set V)
      (E.rectRightBoundaryVertices (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)))
  let p : Nat → Real := fun n ↦
    min (min (bottom n) (top n)) (min (left n) (right n))
  have hp : Tendsto p atTop (nhds 1) := by
    simpa only [p, bottom, top, left, right, min_self] using
      (hbottomLimit.min htopLimit).min (hleftLimit.min hrightLimit)
  apply hcross width height hwidth hheight (fun _ ↦ 0)
    (fun n ↦ -(M n : Real)) (fun n ↦ M n + width n)
    (fun n ↦ -(M n : Real)) (fun n ↦ M n + height n) p hp
  · intro n
    exact (min_le_left _ _).trans
      ((min_le_left _ _).trans measureReal_le_one)
  · intro n v
    simpa only [template, zero_add] using
      E.fourShiftTemplate_preferenceGrid_subset_rect
        (M n) (width n) (height n) (P.orbitBox n)
        (zLeft n) (zRight n) (zBottom n) (zTop n)
        (hleft n) (hright n) (hbottom n) (htop n) v
  · simpa only [zero_add] using hconnectorV0
  · simpa only [zero_add] using hconnectorV1
  · simpa only [zero_add] using hconnectorH0
  · simpa only [zero_add] using hconnectorH1
  · intro n i
    have hside := E.rectBottomConnection_fourShiftTemplate_le mu hTI
      (M n) (width n) (height n) (P.orbitBox n)
      (zLeft n) (zRight n) (zBottom n) (zTop n) i
    exact ((min_le_left _ _).trans (min_le_left _ _)).trans
      (by simpa only [bottom, template, zero_add] using hside)
  · intro n i
    have hside := E.rectTopConnection_fourShiftTemplate_le mu hTI
      (M n) (width n) (height n) (P.orbitBox n)
      (zLeft n) (zRight n) (zBottom n) (zTop n) i
    exact ((min_le_left _ _).trans (min_le_right _ _)).trans
      (by simpa only [top, template, zero_add] using hside)
  · intro n j
    have hside := E.rectLeftConnection_fourShiftTemplate_le mu hTI
      (M n) (width n) (height n) (P.orbitBox n)
      (zLeft n) (zRight n) (zBottom n) (zTop n) j
    exact ((min_le_right _ _).trans (min_le_left _ _)).trans
      (by simpa only [left, template, zero_add] using hside)
  · intro n j
    have hside := E.rectRightConnection_fourShiftTemplate_le mu hTI
      (M n) (width n) (height n) (P.orbitBox n)
      (zLeft n) (zRight n) (zBottom n) (zTop n) j
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans
      (by simpa only [right, template, zero_add] using hside)


theorem PeriodicPlaneEmbedding.exists_fourShiftTemplate_outward_crossing_max_tendsto_one_of_coordinateBounds
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (M : Nat → Nat) (zLeft zRight zBottom zTop : Nat → Site 2)
    (hleft : ∀ n,
      ((P.orbitBox n).image (P.shift (zLeft n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))
    (hright : ∀ n,
      ((P.orbitBox n).image (P.shift (zRight n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))
    (hbottom : ∀ n,
      ((P.orbitBox n).image (P.shift (zBottom n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))
    (htop : ∀ n,
      ((P.orbitBox n).image (P.shift (zTop n)) : Set V) ⊆
        E.rectVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real))
    (hleftLimit : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zLeft n)) : Set V)
        (E.rectLeftBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (hrightLimit : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zRight n)) : Set V)
        (E.rectRightBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (hbottomLimit : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zBottom n)) : Set V)
        (E.rectBottomBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (htopLimit : Tendsto (fun n ↦ mu.real
      (E.rectSideConnectionEvent (-(M n : Real)) (M n : Real)
        (-(M n : Real)) (M n : Real)
        ((P.orbitBox n).image (P.shift (zTop n)) : Set V)
        (E.rectTopBoundaryVertices (-(M n : Real)) (M n : Real)
          (-(M n : Real)) (M n : Real)))) atTop (nhds 1))
    (pad : Nat → Int) (hpad : ∀ n, 0 ≤ pad n) :
    ∃ radius : Nat → Nat, ∀
      (width height : Nat → Nat)
      (hwidth : ∀ n, 0 < width n) (hheight : ∀ n, 0 < height n),
      (∀ n, E.orbitBoxCoordinateBound
        (P.bufferedRadius (radius n)) (0 : Fin 2) ≤ M n) →
      (∀ n, E.orbitBoxCoordinateBound
        (P.bufferedRadius (radius n)) (1 : Fin 2) ≤ M n) →
      Tendsto (fun n ↦ max
        (mu.real (E.verticalCrossingEvent
          (-(M n : Real)) (M n + width n : Real)
          (-(M n : Real) - pad n) (M n + height n + pad n : Real)))
        (mu.real (E.horizontalCrossingEvent
          (-(M n : Real) - pad n) (M n + width n + pad n : Real)
          (-(M n : Real)) (M n + height n : Real))))
        atTop (nhds 1) := by
  obtain ⟨radius, hcross⟩ :=
    E.exists_fourShiftTemplate_outward_crossing_max_tendsto_one_of_connector
      mu hFKG hTI hunique M zLeft zRight zBottom zTop
      hleft hright hbottom htop hleftLimit hrightLimit
      hbottomLimit htopLimit pad hpad
  refine ⟨radius, ?_⟩
  intro width height hwidth hheight hx hy
  apply hcross width height hwidth hheight
  · intro n v
    simpa only [verticalShift_zero_apply, verticalShift_one_apply,
      Int.cast_zero, add_zero, Int.cast_neg, sub_eq_add_neg] using
      E.preferenceGrid_orbitBox_subset_translated_rect
        (P.bufferedRadius (radius n)) (M n) (width n) (height n)
        (verticalShift (-(pad n))) (hx n) (hy n) v
  · intro n v
    have hbase := E.preferenceGrid_orbitBox_subset_translated_rect
      (P.bufferedRadius (radius n)) (M n) (width n) (height n)
      (verticalShift (-(pad n))) (hx n) (hy n) v
    have hbase' :
        P.shift (preferenceGridSite v + verticalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
            E.rectVertices (-(M n : Real)) (M n + width n : Real)
              (-(M n : Real) - pad n) (M n + height n - pad n : Real) := by
      simpa only [verticalShift_zero_apply, verticalShift_one_apply,
        Int.cast_zero, add_zero, Int.cast_neg, sub_eq_add_neg] using hbase
    apply hbase'.trans
    apply E.rectVertices_mono le_rfl le_rfl le_rfl
    have hp : (0 : Real) ≤ pad n := by exact_mod_cast hpad n
    linarith
  · intro n v
    simpa only [horizontalShift_zero_apply, horizontalShift_one_apply,
      Int.cast_zero, add_zero, Int.cast_neg, sub_eq_add_neg] using
      E.preferenceGrid_orbitBox_subset_translated_rect
        (P.bufferedRadius (radius n)) (M n) (width n) (height n)
        (horizontalShift (-(pad n))) (hx n) (hy n) v
  · intro n v
    have hbase := E.preferenceGrid_orbitBox_subset_translated_rect
      (P.bufferedRadius (radius n)) (M n) (width n) (height n)
      (horizontalShift (-(pad n))) (hx n) (hy n) v
    have hbase' :
        P.shift (preferenceGridSite v + horizontalShift (-(pad n))) ''
          (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆
            E.rectVertices (-(M n : Real) - pad n)
              (M n + width n - pad n : Real)
              (-(M n : Real)) (M n + height n : Real) := by
      simpa only [horizontalShift_zero_apply, horizontalShift_one_apply,
        Int.cast_zero, add_zero, Int.cast_neg, sub_eq_add_neg] using hbase
    apply hbase'.trans
    apply E.rectVertices_mono le_rfl
    · have hp : (0 : Real) ≤ pad n := by exact_mod_cast hpad n
      linarith
    · exact le_rfl
    · exact le_rfl

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}


theorem adjacent_height_array_contradiction_of_primal_dual_bounded_limits
    (horizontal vertical dualVertical dualHorizontal : Nat → Nat → Real)
    (K : Nat → Nat)
    (hhorizontal_nonneg : ∀ n k, 0 ≤ horizontal n k)
    (hvertical_nonneg : ∀ n k, 0 ≤ vertical n k)
    (hhorizontal_le_one : ∀ n k, horizontal n k ≤ 1)
    (hvertical_le_one : ∀ n k, vertical n k ≤ 1)
    (hvertical_start : Tendsto (fun n ↦ vertical n 0) atTop (nhds 1))
    (hhorizontal_end : Tendsto
      (fun n ↦ horizontal n (K n + 1)) atTop (nhds 1))
    (hmatchHorizontal : ∀ n k,
      horizontal n k + dualVertical n k ≤ 1)
    (hmatchVertical : ∀ n k,
      vertical n k + dualHorizontal n k ≤ 1)
    (hprimalLimits : ∀ k : Nat → Nat,
      (∀ n, k n < K n + 1) → Tendsto (fun n ↦ max
        (horizontal n (k n)) (vertical n (k n + 1)))
        atTop (nhds 1))
    (hdualLimits : ∀ k : Nat → Nat,
      (∀ n, k n ≤ K n + 1) → Tendsto (fun n ↦ max
        (dualVertical n (k n)) (dualHorizontal n (k n)))
        atTop (nhds 1)) : False := by
  apply adjacent_height_array_contradiction_of_endpoint_and_uniform_limits
    horizontal vertical K hhorizontal_nonneg hvertical_nonneg
    hhorizontal_le_one hvertical_le_one hvertical_start hhorizontal_end
  intro k hk
  have hkBound : ∀ n, k n ≤ K n + 1 := fun n ↦ (hk n).le
  have hkNextBound : ∀ n, k n + 1 ≤ K n + 1 := by
    intro n
    exact Nat.succ_le_of_lt (hk n)
  refine ⟨hprimalLimits k hk, ?_, ?_⟩
  · simpa only [min_comm] using min_tendsto_zero_of_matched_exclusion
      (fun n ↦ horizontal n (k n))
      (fun n ↦ vertical n (k n))
      (fun n ↦ dualVertical n (k n))
      (fun n ↦ dualHorizontal n (k n))
      (fun n ↦ hhorizontal_nonneg n (k n))
      (fun n ↦ hvertical_nonneg n (k n))
      (fun n ↦ hmatchHorizontal n (k n))
      (fun n ↦ hmatchVertical n (k n))
      (hdualLimits k hkBound)
  · simpa only [min_comm] using min_tendsto_zero_of_matched_exclusion
      (fun n ↦ horizontal n (k n + 1))
      (fun n ↦ vertical n (k n + 1))
      (fun n ↦ dualVertical n (k n + 1))
      (fun n ↦ dualHorizontal n (k n + 1))
      (fun n ↦ hhorizontal_nonneg n (k n + 1))
      (fun n ↦ hvertical_nonneg n (k n + 1))
      (fun n ↦ hmatchHorizontal n (k n + 1))
      (fun n ↦ hmatchVertical n (k n + 1))
      (hdualLimits (fun n ↦ k n + 1) hkNextBound)


theorem PeriodicPlanarDualPair.adjacent_rectangles_contradiction_of_bounded_max_limits
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {B : Real} (hBpos : 0 < B)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
    (a b c d : Nat → Nat → Real) (K : Nat → Nat)
    (hspanX : ∀ n k, a n k + 5 * B < b n k - 5 * B)
    (hspanY : ∀ n k, c n k + 5 * B < d n k - 5 * B)
    (hverticalStart : Tendsto (fun n ↦ mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (a n 0 + 4 * B) (b n 0 - 4 * B) (c n 0) (d n 0)))
      atTop (nhds 1))
    (hhorizontalEnd : Tendsto (fun n ↦ mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (a n (K n + 1)) (b n (K n + 1))
        (c n (K n + 1) + 4 * B) (d n (K n + 1) - 4 * B)))
      atTop (nhds 1))
    (hprimal : ∀ k : Nat → Nat, (∀ n, k n < K n + 1) →
      Tendsto (fun n ↦ max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          (a n (k n)) (b n (k n))
          (c n (k n) + 4 * B) (d n (k n) - 4 * B)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          (a n (k n + 1) + 4 * B) (b n (k n + 1) - 4 * B)
          (c n (k n + 1)) (d n (k n + 1))))) atTop (nhds 1))
    (hdual : ∀ k : Nat → Nat, (∀ n, k n ≤ K n + 1) →
      Tendsto (fun n ↦ max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a n (k n) + 4 * B) (b n (k n) - 4 * B)
            (c n (k n)) (d n (k n))))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            (a n (k n)) (b n (k n))
            (c n (k n) + 4 * B) (d n (k n) - 4 * B))))
        atTop (nhds 1)) : False := by
  let horizontal : Nat → Nat → Real := fun n k ↦ mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a n k) (b n k) (c n k + 4 * B) (d n k - 4 * B))
  let vertical : Nat → Nat → Real := fun n k ↦ mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a n k + 4 * B) (b n k - 4 * B) (c n k) (d n k))
  let dualVertical : Nat → Nat → Real := fun n k ↦ mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a n k + 4 * B) (b n k - 4 * B) (c n k) (d n k))
  let dualHorizontal : Nat → Nat → Real := fun n k ↦ mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a n k) (b n k) (c n k + 4 * B) (d n k - 4 * B))
  apply adjacent_height_array_contradiction_of_primal_dual_bounded_limits
    horizontal vertical dualVertical dualHorizontal K
    (fun _ _ ↦ measureReal_nonneg) (fun _ _ ↦ measureReal_nonneg)
    (fun _ _ ↦ measureReal_le_one) (fun _ _ ↦ measureReal_le_one)
    (by simpa [vertical] using hverticalStart)
    (by simpa [horizontal] using hhorizontalEnd)
  · intro n k
    exact D.matchedCrossing_measureReal_add_le_one mu hBpos hBp hBd
      (hspanX n k) (hspanY n k)
  · intro n k
    exact D.matchedVerticalHorizontalCrossing_measureReal_add_le_one
      mu hBpos hBp hBd (hspanX n k) (hspanY n k)
  · intro k hk
    simpa [horizontal, vertical] using hprimal k hk
  · intro k hk
    simpa [dualVertical, dualHorizontal] using hdual k hk


end StatMech.FK.PeriodicPlanar
