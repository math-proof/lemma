/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap.Part3
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

omit [Countable V] in theorem PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_mono_sources
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    {L R L' R' : Finset V} (hL : L ⊆ L') (hR : R ⊆ R') :
    E.rectanglePairMergeErrorUnion a b c d L R ⊆
      E.rectanglePairMergeErrorUnion a b c d L' R' := by
  intro omega homega
  obtain ⟨x, hxL, y, hyR, hxy⟩ := by
    simpa only [PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion,
      Set.mem_iUnion] using homega
  apply Set.mem_iUnion.2
  exact ⟨x, Set.mem_iUnion.2 ⟨hL hxL, Set.mem_iUnion.2 ⟨y,
    Set.mem_iUnion.2 ⟨hR hyR, hxy⟩⟩⟩⟩

omit [Countable V] in theorem PeriodicGraph.connectedWithinOrbit_subset_connectedWithinSet
    (P : PeriodicGraph V) {A : Set V} {x y : V} {N : Nat}
    (hbox : (P.orbitBox (P.bufferedRadius N) : Set V) ⊆ A) :
    P.connectedWithinOrbit x y N ⊆ P.connectedWithinSet A x y := by
  rintro omega ⟨l, hchain, hlast, hsupport⟩
  exact ⟨l, hchain, hlast, fun v hv => hbox (hsupport v hv)⟩


theorem PeriodicPlaneEmbedding.finiteRectangleJoinedHorizontalEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (L R : Finset V) :
    MeasurableSet (E.finiteRectangleJoinedHorizontalEvent a b c d L R) :=
  ((P.infiniteSetConnectionWithin_measurableSet
      (E.rectVertices a b c d) (L : Set V)
      (E.rectLeftBoundaryVertices a b c d)).inter
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rectVertices a b c d) (R : Set V)
      (E.rectRightBoundaryVertices a b c d))).diff
    (E.rectanglePairMergeErrorUnion_measurableSet a b c d L R)


theorem PeriodicPlaneEmbedding.finiteRectangleJoinedHorizontalEvent_subset_horizontalCrossing
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (L R : Finset V) :
    E.finiteRectangleJoinedHorizontalEvent a b c d L R ⊆
      E.horizontalCrossingEvent a b c d := by
  intro omega homega
  obtain ⟨x, hxL, hxinf, xl, hxlLeft, hxxl⟩ := homega.1.1
  obtain ⟨y, hyR, hyinf, yr, hyrRight, hyyr⟩ := homega.1.2
  have hxy : omega ∈
      P.connectedWithinSet (E.rectVertices a b c d) x y := by
    by_contra hnot
    apply homega.2
    apply Set.mem_iUnion.2
    refine ⟨x, Set.mem_iUnion.2 ⟨hxL, Set.mem_iUnion.2 ⟨y,
      Set.mem_iUnion.2 ⟨hyR, ?_⟩⟩⟩⟩
    exact ⟨⟨hxinf, hyinf⟩, hnot⟩
  obtain ⟨qxl, hqxl⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxxl
  obtain ⟨qxy, hqxy⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxy
  obtain ⟨qyr, hqyr⟩ := P.connectedWithinSet_exists_openSubgraphWalk hyyr
  let q : (P.openSubgraph omega).Walk xl yr :=
    qxl.reverse.append (qxy.append qyr)
  have hqRect : ∀ v ∈ q.support, v ∈ E.rectVertices a b c d := by
    intro v hv
    dsimp only [q] at hv
    rw [SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_reverse] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hqxl v (by simpa using hv)
    · rw [SimpleGraph.Walk.support_append] at hv
      rcases List.mem_append.mp (List.mem_of_mem_tail hv) with hv | hv
      · exact hqxy v hv
      · exact hqyr v (List.mem_of_mem_tail hv)
  have hxlRect := hqRect xl q.start_mem_support
  have hyrRect := hqRect yr q.end_mem_support
  have hleft : E.rectLeftBoundary a b c d ⟨xl, hxlRect⟩ := hxlLeft.2
  have hright : E.rectRightBoundary a b c d ⟨yr, hyrRect⟩ := hyrRight.2
  have hreach :
      ((P.openSubgraph omega).induce (E.rectVertices a b c d)).Reachable
        ⟨xl, hxlRect⟩ ⟨yr, hyrRect⟩ :=
    ⟨q.induce (E.rectVertices a b c d) hqRect⟩
  change E.rectRestrict a b c d omega ∈ E.finiteHorizontalCrossing a b c d
  refine ⟨⟨xl, hxlRect⟩, ⟨yr, hyrRect⟩, hleft, hright, ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hreach


theorem PeriodicPlaneEmbedding.verticalCrossing_measureReal_ge_side_mul_sub_mergeError
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (L R : Finset V) :
    mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
        (E.rectBottomBoundaryVertices a b c d)) *
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectTopBoundaryVertices a b c d)) -
      mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤
        mu.real (E.verticalCrossingEvent a b c d) := by
  let A := E.rectSideConnectionEvent a b c d (L : Set V)
    (E.rectBottomBoundaryVertices a b c d)
  let B := E.rectSideConnectionEvent a b c d (R : Set V)
    (E.rectTopBoundaryVertices a b c d)
  let M := E.rectanglePairMergeErrorUnion a b c d L R
  have hinter : mu.real A * mu.real B ≤ mu.real (A ∩ B) :=
    hFKG A B
      (E.rectSideConnectionEvent_measurableSet a b c d (L : Set V)
        (E.rectBottomBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d (R : Set V)
        (E.rectTopBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d (L : Set V)
        (E.rectBottomBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d (R : Set V)
        (E.rectTopBoundaryVertices a b c d))
  have hdiff : mu.real (A ∩ B) - mu.real M ≤
      mu.real ((A ∩ B) \ M) := le_measureReal_diff
  have hjoined : mu.real ((A ∩ B) \ M) ≤
      mu.real (E.verticalCrossingEvent a b c d) :=
    measureReal_mono
      (E.finiteRectangleJoinedVerticalEvent_subset_verticalCrossing
        a b c d L R)
  dsimp only [A, B, M] at hinter hdiff hjoined ⊢
  linarith


theorem PeriodicPlaneEmbedding.horizontalCrossing_measureReal_ge_side_mul_sub_mergeError
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (L R : Finset V) :
    mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
        (E.rectLeftBoundaryVertices a b c d)) *
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectRightBoundaryVertices a b c d)) -
      mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤
        mu.real (E.horizontalCrossingEvent a b c d) := by
  let A := E.rectSideConnectionEvent a b c d (L : Set V)
    (E.rectLeftBoundaryVertices a b c d)
  let B := E.rectSideConnectionEvent a b c d (R : Set V)
    (E.rectRightBoundaryVertices a b c d)
  let M := E.rectanglePairMergeErrorUnion a b c d L R
  have hinter : mu.real A * mu.real B ≤ mu.real (A ∩ B) :=
    hFKG A B
      (E.rectSideConnectionEvent_measurableSet a b c d (L : Set V)
        (E.rectLeftBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d (R : Set V)
        (E.rectRightBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d (L : Set V)
        (E.rectLeftBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d (R : Set V)
        (E.rectRightBoundaryVertices a b c d))
  have hdiff : mu.real (A ∩ B) - mu.real M ≤
      mu.real ((A ∩ B) \ M) := le_measureReal_diff
  have hjoined : mu.real ((A ∩ B) \ M) ≤
      mu.real (E.horizontalCrossingEvent a b c d) :=
    measureReal_mono
      (E.finiteRectangleJoinedHorizontalEvent_subset_horizontalCrossing
        a b c d L R)
  dsimp only [A, B, M] at hinter hdiff hjoined ⊢
  linarith


theorem PeriodicPlaneEmbedding.setHitsInfinite_inter_rectSide_diff_mergeError_subset_rectSide
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (L R : Finset V) (side : Set V) :
    (P.setHitsInfinite (R : Set V) ∩
      E.rectSideConnectionEvent a b c d (L : Set V) side) \
        E.rectanglePairMergeErrorUnion a b c d L R ⊆
      E.rectSideConnectionEvent a b c d (R : Set V) side := by
  intro omega homega
  obtain ⟨y, hyR, hyinf⟩ := homega.1.1
  obtain ⟨x, hxL, hxinf, v, hvside, hxv⟩ := homega.1.2
  have hxy : omega ∈
      P.connectedWithinSet (E.rectVertices a b c d) x y := by
    by_contra hnot
    apply homega.2
    apply Set.mem_iUnion.2
    refine ⟨x, Set.mem_iUnion.2 ⟨hxL, Set.mem_iUnion.2 ⟨y,
      Set.mem_iUnion.2 ⟨hyR, ⟨⟨hxinf, hyinf⟩, hnot⟩⟩⟩⟩⟩
  obtain ⟨qxy, hqxy⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxy
  obtain ⟨qxv, hqxv⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxv
  let q : (P.openSubgraph omega).Walk y v := qxy.reverse.append qxv
  have hqRect : ∀ w ∈ q.support, w ∈ E.rectVertices a b c d := by
    intro w hw
    dsimp only [q] at hw
    rw [SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_reverse] at hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hqxy w (by simpa using hw)
    · exact hqxv w (List.mem_of_mem_tail hw)
  exact ⟨y, hyR, hyinf, v, hvside,
    P.mem_connectedWithinSet_of_walk q hqRect⟩


theorem PeriodicPlaneEmbedding.rectSide_measureReal_ge_hits_mul_side_sub_mergeError
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real)
    (L R : Finset V) (side : Set V) :
    mu.real (P.setHitsInfinite (R : Set V)) *
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V) side) -
      mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤
        mu.real (E.rectSideConnectionEvent a b c d (R : Set V) side) := by
  let H := P.setHitsInfinite (R : Set V)
  let A := E.rectSideConnectionEvent a b c d (L : Set V) side
  let M := E.rectanglePairMergeErrorUnion a b c d L R
  have hinter : mu.real H * mu.real A ≤ mu.real (H ∩ A) :=
    hFKG H A (P.setHitsInfinite_measurableSet (R : Set V))
      (E.rectSideConnectionEvent_measurableSet a b c d (L : Set V) side)
      (P.setHitsInfinite_isIncreasing (R : Set V))
      (E.rectSideConnectionEvent_isIncreasing a b c d (L : Set V) side)
  have hdiff : mu.real (H ∩ A) - mu.real M ≤
      mu.real ((H ∩ A) \ M) := le_measureReal_diff
  have htransfer : mu.real ((H ∩ A) \ M) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V) side) :=
    measureReal_mono
      (E.setHitsInfinite_inter_rectSide_diff_mergeError_subset_rectSide
        a b c d L R side)
  dsimp only [H, A, M] at hinter hdiff htransfer ⊢
  linarith


theorem PeriodicPlaneEmbedding.verticalCrossing_ge_preferredSide_transfer
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (L R : Finset V)
    (hOpposite :
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectBottomBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectTopBoundaryVertices a b c d))) :
    let A := mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
      (E.rectBottomBoundaryVertices a b c d))
    let H := mu.real (P.setHitsInfinite (R : Set V))
    let M := mu.real (E.rectanglePairMergeErrorUnion a b c d L R)
    A * (H * A - M) - M ≤
      mu.real (E.verticalCrossingEvent a b c d) := by
  dsimp only
  have htransfer := E.rectSide_measureReal_ge_hits_mul_side_sub_mergeError
    mu hFKG a b c d L R (E.rectBottomBoundaryVertices a b c d)
  have htop :
      mu.real (P.setHitsInfinite (R : Set V)) *
        mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
          (E.rectBottomBoundaryVertices a b c d)) -
        mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectTopBoundaryVertices a b c d)) := htransfer.trans hOpposite
  have hAnonneg : 0 ≤
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
        (E.rectBottomBoundaryVertices a b c d)) := measureReal_nonneg
  have hmul := mul_le_mul_of_nonneg_left htop hAnonneg
  have hcross := E.verticalCrossing_measureReal_ge_side_mul_sub_mergeError
    mu hFKG a b c d L R
  nlinarith


theorem PeriodicPlaneEmbedding.horizontalCrossing_ge_preferredSide_transfer
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (L R : Finset V)
    (hOpposite :
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectLeftBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectRightBoundaryVertices a b c d))) :
    let A := mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
      (E.rectLeftBoundaryVertices a b c d))
    let H := mu.real (P.setHitsInfinite (R : Set V))
    let M := mu.real (E.rectanglePairMergeErrorUnion a b c d L R)
    A * (H * A - M) - M ≤
      mu.real (E.horizontalCrossingEvent a b c d) := by
  dsimp only
  have htransfer := E.rectSide_measureReal_ge_hits_mul_side_sub_mergeError
    mu hFKG a b c d L R (E.rectLeftBoundaryVertices a b c d)
  have hright :
      mu.real (P.setHitsInfinite (R : Set V)) *
        mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
          (E.rectLeftBoundaryVertices a b c d)) -
        mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤
      mu.real (E.rectSideConnectionEvent a b c d (R : Set V)
        (E.rectRightBoundaryVertices a b c d)) := htransfer.trans hOpposite
  have hAnonneg : 0 ≤
      mu.real (E.rectSideConnectionEvent a b c d (L : Set V)
        (E.rectLeftBoundaryVertices a b c d)) := measureReal_nonneg
  have hmul := mul_le_mul_of_nonneg_left hright hAnonneg
  have hcross := E.horizontalCrossing_measureReal_ge_side_mul_sub_mergeError
    mu hFKG a b c d L R
  nlinarith


theorem dominant_of_four_event_sqrt_trick
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) {A B C D : Set (ConfigSpace (Sym2 V))}
    (hA : IsIncreasing A) (hB : IsIncreasing B)
    (hC : IsIncreasing C) (hD : IsIncreasing D)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hCm : MeasurableSet C) (hDm : MeasurableSet D)
    (hBA : mu.real B ≤ mu.real A)
    (hCA : mu.real C ≤ mu.real A)
    (hDA : mu.real D ≤ mu.real A) :
    1 - Real.sqrt (Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D))))) ≤
      mu.real A := by
  have h := four_event_sqrt_trick mu hFKG hA hB hC hD hAm hBm hCm hDm
  have hCD : max (mu.real C) (mu.real D) ≤ mu.real A :=
    max_le hCA hDA
  rw [max_eq_left hBA, max_eq_left hCD] at h
  exact h


theorem PeriodicPlaneEmbedding.dominant_bottomSide_measureReal_ge_fourthRoot
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (S : Set V)
    (hS : S ⊆ E.rectVertices a b c d)
    (hTop : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectTopBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d)))
    (hLeft : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d)))
    (hRight : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectRightBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d))) :
    1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d)) := by
  let A := E.rectSideConnectionEvent a b c d S
    (E.rectBottomBoundaryVertices a b c d)
  let B := E.rectSideConnectionEvent a b c d S
    (E.rectTopBoundaryVertices a b c d)
  let C := E.rectSideConnectionEvent a b c d S
    (E.rectLeftBoundaryVertices a b c d)
  let D := E.rectSideConnectionEvent a b c d S
    (E.rectRightBoundaryVertices a b c d)
  have hdom :
      1 - Real.sqrt (Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D))))) ≤
        mu.real A := by
    exact dominant_of_four_event_sqrt_trick mu hFKG
      (E.rectSideConnectionEvent_isIncreasing a b c d S
        (E.rectBottomBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d S
        (E.rectTopBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d S
        (E.rectLeftBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d S
        (E.rectRightBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d S
        (E.rectBottomBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d S
        (E.rectTopBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d S
        (E.rectLeftBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d S
        (E.rectRightBoundaryVertices a b c d)) hTop hLeft hRight
  have hmass : mu.real (P.setHitsInfinite S) ≤
      mu.real (A ∪ (B ∪ (C ∪ D))) :=
    measureReal_mono
      (E.setHitsInfinite_subset_rectSideConnection_union a b c d S hS)
  have hsqrt :
      Real.sqrt (Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D))))) ≤
        Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) := by
    gcongr
  dsimp only [A, B, C, D] at hdom hsqrt ⊢
  linarith


theorem PeriodicPlaneEmbedding.dominant_leftSide_measureReal_ge_fourthRoot
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (S : Set V)
    (hS : S ⊆ E.rectVertices a b c d)
    (hRight : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectRightBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d)))
    (hBottom : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d)))
    (hTop : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectTopBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d))) :
    1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d)) := by
  let A := E.rectSideConnectionEvent a b c d S
    (E.rectLeftBoundaryVertices a b c d)
  let B := E.rectSideConnectionEvent a b c d S
    (E.rectRightBoundaryVertices a b c d)
  let C := E.rectSideConnectionEvent a b c d S
    (E.rectBottomBoundaryVertices a b c d)
  let D := E.rectSideConnectionEvent a b c d S
    (E.rectTopBoundaryVertices a b c d)
  have hdom :
      1 - Real.sqrt (Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D))))) ≤
        mu.real A := by
    exact dominant_of_four_event_sqrt_trick mu hFKG
      (E.rectSideConnectionEvent_isIncreasing a b c d S
        (E.rectLeftBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d S
        (E.rectRightBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d S
        (E.rectBottomBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_isIncreasing a b c d S
        (E.rectTopBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d S
        (E.rectLeftBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d S
        (E.rectRightBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d S
        (E.rectBottomBoundaryVertices a b c d))
      (E.rectSideConnectionEvent_measurableSet a b c d S
        (E.rectTopBoundaryVertices a b c d)) hRight hBottom hTop
  have hmass0 : mu.real (P.setHitsInfinite S) ≤
      mu.real
        (E.rectSideConnectionEvent a b c d S
            (E.rectBottomBoundaryVertices a b c d) ∪
          (E.rectSideConnectionEvent a b c d S
              (E.rectTopBoundaryVertices a b c d) ∪
            (E.rectSideConnectionEvent a b c d S
                (E.rectLeftBoundaryVertices a b c d) ∪
              E.rectSideConnectionEvent a b c d S
                (E.rectRightBoundaryVertices a b c d)))) :=
    measureReal_mono
      (E.setHitsInfinite_subset_rectSideConnection_union a b c d S hS)
  have hmass : mu.real (P.setHitsInfinite S) ≤
      mu.real (A ∪ (B ∪ (C ∪ D))) := by
    dsimp only [A, B, C, D]
    simpa only [Set.union_assoc, Set.union_left_comm, Set.union_comm] using hmass0
  have hsqrt :
      Real.sqrt (Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D))))) ≤
        Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) := by
    gcongr
  dsimp only [A, B, C, D] at hdom hsqrt ⊢
  linarith


theorem PeriodicPlaneEmbedding.preference_max_bottom_left_ge_fourthRoot
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (a b c d : Real) (S : Set V)
    (hS : S ⊆ E.rectVertices a b c d)
    (hBottomTop : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectTopBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d)))
    (hLeftRight : mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectRightBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d))) :
    1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite S))) ≤
      max
        (mu.real (E.rectSideConnectionEvent a b c d S
          (E.rectBottomBoundaryVertices a b c d)))
        (mu.real (E.rectSideConnectionEvent a b c d S
          (E.rectLeftBoundaryVertices a b c d))) := by
  by_cases hLeftBottom :
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectLeftBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d S
        (E.rectBottomBoundaryVertices a b c d))
  · apply le_trans (E.dominant_bottomSide_measureReal_ge_fourthRoot
      mu hFKG a b c d S hS hBottomTop hLeftBottom
      (hLeftRight.trans hLeftBottom))
    exact le_max_left _ _
  · have hBottomLeft :
        mu.real (E.rectSideConnectionEvent a b c d S
          (E.rectBottomBoundaryVertices a b c d)) ≤
        mu.real (E.rectSideConnectionEvent a b c d S
          (E.rectLeftBoundaryVertices a b c d)) := le_of_not_ge hLeftBottom
    apply le_trans (E.dominant_leftSide_measureReal_ge_fourthRoot
      mu hFKG a b c d S hS hLeftRight hBottomLeft
      (hBottomTop.trans hBottomLeft))
    exact le_max_right _ _


theorem PeriodicPlaneEmbedding.dominant_translatedOrbitBox_bottomSide_ge_fourthRoot
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (z : Site 2) (N : Nat) (a b c d : Real)
    (hbox : (P.shift z '' (P.orbitBox N : Set V)) ⊆
      E.rectVertices a b c d)
    (hTop : mu.real (E.rectSideConnectionEvent a b c d
        (P.shift z '' (P.orbitBox N : Set V))
        (E.rectTopBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d
        (P.shift z '' (P.orbitBox N : Set V))
        (E.rectBottomBoundaryVertices a b c d)))
    (hLeft : mu.real (E.rectSideConnectionEvent a b c d
        (P.shift z '' (P.orbitBox N : Set V))
        (E.rectLeftBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d
        (P.shift z '' (P.orbitBox N : Set V))
        (E.rectBottomBoundaryVertices a b c d)))
    (hRight : mu.real (E.rectSideConnectionEvent a b c d
        (P.shift z '' (P.orbitBox N : Set V))
        (E.rectRightBoundaryVertices a b c d)) ≤
      mu.real (E.rectSideConnectionEvent a b c d
        (P.shift z '' (P.orbitBox N : Set V))
        (E.rectBottomBoundaryVertices a b c d))) :
    1 - Real.sqrt (Real.sqrt
        (1 - mu.real (P.orbitBoxHitsInfinite N))) ≤
      mu.real (E.rectSideConnectionEvent a b c d
        (P.shift z '' (P.orbitBox N : Set V))
        (E.rectBottomBoundaryVertices a b c d)) := by
  have h := E.dominant_bottomSide_measureReal_ge_fourthRoot mu hFKG
    a b c d (P.shift z '' (P.orbitBox N : Set V)) hbox hTop hLeft hRight
  rw [P.setHitsInfinite_translate_measureReal_eq mu hTI z,
    P.setHitsInfinite_orbitBox] at h
  exact h


theorem PeriodicPlaneEmbedding.dominant_translatedOrbitBox_bottomSide_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hexists : mu {omega | P.HasInfiniteCluster omega} = 1)
    (z : Nat → Site 2) (a b c d : Nat → Real)
    (hbox : ∀ N, (P.shift (z N) '' (P.orbitBox N : Set V)) ⊆
      E.rectVertices (a N) (b N) (c N) (d N))
    (hTop : ∀ N, mu.real (E.rectSideConnectionEvent
        (a N) (b N) (c N) (d N)
        (P.shift (z N) '' (P.orbitBox N : Set V))
        (E.rectTopBoundaryVertices (a N) (b N) (c N) (d N))) ≤
      mu.real (E.rectSideConnectionEvent (a N) (b N) (c N) (d N)
        (P.shift (z N) '' (P.orbitBox N : Set V))
        (E.rectBottomBoundaryVertices (a N) (b N) (c N) (d N))))
    (hLeft : ∀ N, mu.real (E.rectSideConnectionEvent
        (a N) (b N) (c N) (d N)
        (P.shift (z N) '' (P.orbitBox N : Set V))
        (E.rectLeftBoundaryVertices (a N) (b N) (c N) (d N))) ≤
      mu.real (E.rectSideConnectionEvent (a N) (b N) (c N) (d N)
        (P.shift (z N) '' (P.orbitBox N : Set V))
        (E.rectBottomBoundaryVertices (a N) (b N) (c N) (d N))))
    (hRight : ∀ N, mu.real (E.rectSideConnectionEvent
        (a N) (b N) (c N) (d N)
        (P.shift (z N) '' (P.orbitBox N : Set V))
        (E.rectRightBoundaryVertices (a N) (b N) (c N) (d N))) ≤
      mu.real (E.rectSideConnectionEvent (a N) (b N) (c N) (d N)
        (P.shift (z N) '' (P.orbitBox N : Set V))
        (E.rectBottomBoundaryVertices (a N) (b N) (c N) (d N)))) :
    Tendsto (fun N => mu.real (E.rectSideConnectionEvent
      (a N) (b N) (c N) (d N)
      (P.shift (z N) '' (P.orbitBox N : Set V))
      (E.rectBottomBoundaryVertices (a N) (b N) (c N) (d N))))
      atTop (nhds 1) := by
  have hhit := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hmiss : Tendsto (fun N =>
      1 - mu.real (P.orbitBoxHitsInfinite N)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hhit
  have hlower : Tendsto (fun N => 1 - Real.sqrt (Real.sqrt
      (1 - mu.real (P.orbitBoxHitsInfinite N)))) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hmiss.sqrt.sqrt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
  · intro N
    exact E.dominant_translatedOrbitBox_bottomSide_ge_fourthRoot
      mu hFKG hTI (z N) N (a N) (b N) (c N) (d N)
      (hbox N) (hTop N) (hLeft N) (hRight N)
  · intro N
    exact measureReal_le_one


theorem crossing_tendsto_one_of_preferredSide_transfer
    (A H M crossing : Nat → Real)
    (hA : Tendsto A atTop (nhds 1))
    (hH : Tendsto H atTop (nhds 1))
    (hM : Tendsto M atTop (nhds 0))
    (hlower : ∀ N, A N * (H N * A N - M N) - M N ≤ crossing N)
    (hupper : ∀ N, crossing N ≤ 1) :
    Tendsto crossing atTop (nhds 1) := by
  have htransfer : Tendsto
      (fun N => A N * (H N * A N - M N) - M N)
      atTop (nhds 1) := by
    convert hA.mul ((hH.mul hA).sub hM) |>.sub hM using 1 <;> norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    htransfer tendsto_const_nhds hlower hupper


theorem crossing_max_tendsto_one_of_preferredSide_branches
    (A Hv Hh Mv Mh Cv Ch : Nat → Real)
    (hA : Tendsto A atTop (nhds 1))
    (hHv : Tendsto Hv atTop (nhds 1))
    (hHh : Tendsto Hh atTop (nhds 1))
    (hMv : Tendsto Mv atTop (nhds 0))
    (hMh : Tendsto Mh atTop (nhds 0))
    (hbranch : ∀ N,
      A N * (Hv N * A N - Mv N) - Mv N ≤ Cv N ∨
      A N * (Hh N * A N - Mh N) - Mh N ≤ Ch N)
    (hCv : ∀ N, Cv N ≤ 1) (hCh : ∀ N, Ch N ≤ 1) :
    Tendsto (fun N => max (Cv N) (Ch N)) atTop (nhds 1) := by
  let Lv := fun N => A N * (Hv N * A N - Mv N) - Mv N
  let Lh := fun N => A N * (Hh N * A N - Mh N) - Mh N
  have hLv : Tendsto Lv atTop (nhds 1) := by
    dsimp only [Lv]
    convert hA.mul ((hHv.mul hA).sub hMv) |>.sub hMv using 1 <;> norm_num
  have hLh : Tendsto Lh atTop (nhds 1) := by
    dsimp only [Lh]
    convert hA.mul ((hHh.mul hA).sub hMh) |>.sub hMh using 1 <;> norm_num
  have hmin : Tendsto (fun N => min (Lv N) (Lh N)) atTop (nhds 1) := by
    simpa using hLv.min hLh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hmin tendsto_const_nhds
  · intro N
    rcases hbranch N with hV | hH
    · exact (min_le_left _ _).trans (hV.trans (le_max_left _ _))
    · exact (min_le_right _ _).trans (hH.trans (le_max_right _ _))
  · intro N
    exact max_le (hCv N) (hCh N)

end StatMech.FK.PeriodicPlanar
