/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem opposedEndpointVerticalScore_mono_width
    {width width' height : Nat} (hwidth : width <= width') :
    opposedEndpointVerticalScore width height <=
      opposedEndpointVerticalScore width' height := by
  unfold opposedEndpointVerticalScore
  split_ifs <;> norm_num <;> omega

theorem opposedEndpointVerticalScore_anti_height
    {width height height' : Nat} (hheight : height <= height') :
    opposedEndpointVerticalScore width height' <=
      opposedEndpointVerticalScore width height := by
  unfold opposedEndpointVerticalScore
  split_ifs <;> norm_num <;> omega

theorem opposedEndpointHorizontalScore_anti_width
    {width width' height : Nat} (hwidth : width <= width') :
    opposedEndpointHorizontalScore width' height <=
      opposedEndpointHorizontalScore width height := by
  unfold opposedEndpointHorizontalScore
  split_ifs <;> norm_num <;> omega

theorem opposedEndpointHorizontalScore_mono_height
    {width height height' : Nat} (hheight : height <= height') :
    opposedEndpointHorizontalScore width height <=
      opposedEndpointHorizontalScore width height' := by
  unfold opposedEndpointHorizontalScore
  split_ifs <;> norm_num <;> omega


theorem exists_opposedEndpointVerticalSelector
    (height minimumWidth : Nat -> Nat) :
    exists width : Nat -> Nat,
      (forall n, minimumWidth n <= width n) /\
      Tendsto (fun n => opposedEndpointVerticalScore (width n) (height n))
        atTop (nhds 1) := by
  let width : Nat -> Nat := fun n => max (minimumWidth n) (height n + 1)
  refine ⟨width, fun n => Nat.le_max_left _ _, ?_⟩
  have heq : (fun n => opposedEndpointVerticalScore (width n) (height n)) =
      fun _ : Nat => (1 : Real) := by
    funext n
    have hlt : height n < width n :=
      (Nat.lt_succ_self _).trans_le (Nat.le_max_right _ _)
    simp only [opposedEndpointVerticalScore, hlt, if_pos]
  rw [heq]
  exact tendsto_const_nhds


theorem exists_opposedEndpointHorizontalSelector
    (width minimumHeight : Nat -> Nat) :
    exists height : Nat -> Nat,
      (forall n, minimumHeight n <= height n) /\
      Tendsto (fun n => opposedEndpointHorizontalScore (width n) (height n))
        atTop (nhds 1) := by
  let height : Nat -> Nat := fun n => max (minimumHeight n) (width n + 1)
  refine ⟨height, fun n => Nat.le_max_left _ _, ?_⟩
  have heq : (fun n => opposedEndpointHorizontalScore (width n) (height n)) =
      fun _ : Nat => (1 : Real) := by
    funext n
    have hlt : width n < height n :=
      (Nat.lt_succ_self _).trans_le (Nat.le_max_right _ _)
    simp only [opposedEndpointHorizontalScore, hlt, if_pos]
  rw [heq]
  exact tendsto_const_nhds


theorem opposedEndpointScores_not_simultaneously_tendsto_one
    (width height : Nat -> Nat) :
    ¬ (Tendsto
      (fun n => opposedEndpointVerticalScore (width n) (height n))
        atTop (nhds 1) /\
      Tendsto
        (fun n => opposedEndpointHorizontalScore (width n) (height n))
          atTop (nhds 1)) := by
  rintro ⟨hvertical, hhorizontal⟩
  have hverticalEventually : ∀ᶠ n in atTop,
      (1 / 2 : Real) < opposedEndpointVerticalScore (width n) (height n) :=
    hvertical.eventually (Ioi_mem_nhds (by norm_num))
  have hhorizontalEventually : ∀ᶠ n in atTop,
      (1 / 2 : Real) < opposedEndpointHorizontalScore (width n) (height n) :=
    hhorizontal.eventually (Ioi_mem_nhds (by norm_num))
  obtain ⟨n, hv, hh⟩ :=
    (hverticalEventually.and hhorizontalEventually).exists
  by_cases hlt : height n < width n
  · have hnot : ¬ (width n < height n) := by omega
    simp only [opposedEndpointHorizontalScore, hnot] at hh
    norm_num at hh
  · simp only [opposedEndpointVerticalScore, hlt] at hv
    norm_num at hv


theorem exists_alignedCrossNestedPairedChain_ge
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
    (k padding length lowerX lowerY : Nat) :
    exists data : AlignedCrossNestedPairedChain E Edual mu muDual
        S Sdual p pDual family familyDual schedule k padding length,
      (forall j, lowerX <= data.extentX j) /\
      (forall j, lowerY <= data.extentY j) := by
  obtain ⟨thresholdX0, thresholdY0, hthreshold0⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E Edual mu muDual hTI hTIDual family familyDual schedule k
  let thresholdX := max thresholdX0 lowerX
  let thresholdY := max thresholdY0 lowerY
  have hthreshold {extentX extentY : Nat}
      (hx : thresholdX <= extentX) (hy : thresholdY <= extentY) :
      Nonempty (AlignedExactExtentPairedMixedBoundaryScores
        E Edual mu muDual S Sdual p pDual family familyDual schedule k
          extentX extentY) :=
    hthreshold0 ((Nat.le_max_left _ _).trans hx)
      ((Nat.le_max_left _ _).trans hy)
  let extentY : Nat -> Nat := fun j =>
    thresholdY + 2 * padding * (length - j)
  let State (j : Nat) :=
    Sigma fun x : {x : Nat // thresholdX <= x} =>
      AlignedExactExtentPairedMixedBoundaryScores
        E Edual mu muDual S Sdual p pDual family familyDual schedule k x.1
          (extentY j)
  have hy (j : Nat) : thresholdY <= extentY j := by
    dsimp only [extentY]
    omega
  let initial : State 0 :=
    ⟨⟨thresholdX, le_rfl⟩, Classical.choice
      (hthreshold (extentX := thresholdX) (extentY := extentY 0)
        (le_refl _) (hy 0))⟩
  let nextState (j : Nat) (previous : State j) : State (j + 1) := by
    let span := previous.2.raw.wideRightInt -
      previous.2.raw.wideLeftInt
    have hspan : 0 <= span :=
      (show (0 : Int) <= previous.1.1 by omega).trans
        previous.2.raw.extentX_le_wideSpan
    let nextX := span.toNat + 2 * padding
    have hpreviousX : thresholdX <= previous.1.1 := previous.1.2
    have hnextX : thresholdX <= nextX := by
      have htoNat : previous.1.1 <= span.toNat := by
        rw [Int.le_toNat hspan]
        exact previous.2.raw.extentX_le_wideSpan
      exact hpreviousX.trans (htoNat.trans (Nat.le_add_right _ _))
    exact ⟨⟨nextX, hnextX⟩, Classical.choice
      (hthreshold (extentX := nextX) (extentY := extentY (j + 1))
        hnextX (hy (j + 1)))⟩
  let state : forall j, State j := fun j =>
    Nat.rec (motive := State) initial nextState j
  let extentX : Nat -> Nat := fun j => (state j).1.1
  let level : forall j, AlignedExactExtentPairedMixedBoundaryScores
      E Edual mu muDual S Sdual p pDual family familyDual schedule k
        (extentX j) (extentY j) := fun j => (state j).2
  refine ⟨{
    extentX := extentX
    extentY := extentY
    level := level
    nextX_eq := ?_
    nextY_eq := ?_ }, ?_, ?_⟩
  · intro j hj
    let span := (state j).2.raw.wideRightInt -
      (state j).2.raw.wideLeftInt
    have hspan : 0 <= span :=
      (show (0 : Int) <= (state j).1.1 by omega).trans
        (state j).2.raw.extentX_le_wideSpan
    change ((state (j + 1)).1.1 : Int) = span + 2 * (padding : Int)
    simp only [state, Nat.rec_add_one, nextState]
    change ((span.toNat + 2 * padding : Nat) : Int) =
      span + 2 * (padding : Int)
    push_cast
    rw [Int.toNat_of_nonneg hspan]
  · intro j hj
    dsimp only [extentY]
    have hsub : length - j = length - (j + 1) + 1 := by omega
    rw [hsub]
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  · intro j
    exact (Nat.le_max_right _ _).trans (state j).1.2
  · intro j
    exact (Nat.le_max_right _ _).trans (hy j)


theorem nonempty_alignedCrossNestedPairedChain
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
    (k padding length : Nat) :
    Nonempty (AlignedCrossNestedPairedChain E Edual mu muDual
      S Sdual p pDual family familyDual schedule k padding length) := by
  obtain ⟨data, _, _⟩ := exists_alignedCrossNestedPairedChain_ge
    E Edual mu muDual hTI hTIDual family familyDual schedule
      k padding length 0 0
  exact ⟨data⟩


end StatMech.FK.PeriodicPlanar
