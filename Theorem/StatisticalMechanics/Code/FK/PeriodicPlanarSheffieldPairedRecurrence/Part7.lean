/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part5
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem nonempty_alignedCrossNestedThreePairedMixedBoundaryScores
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
    (k padding : Nat) :
    Nonempty (AlignedCrossNestedThreePairedMixedBoundaryScores
      E Edual mu muDual S Sdual p pDual family familyDual schedule k
      padding) := by
  obtain ⟨thresholdX, thresholdY, hthreshold⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E Edual mu muDual hTI hTIDual family familyDual schedule k
  let nextY := thresholdY
  let currentY := nextY + 2 * padding
  let previousY := currentY + 2 * padding
  let previousX := thresholdX
  let previous := Classical.choice
    (hthreshold (extentX := previousX) (extentY := previousY)
      (by simp [previousX]) (by dsimp [previousY, currentY, nextY]; omega))
  let previousSpan :=
    previous.raw.wideRightInt - previous.raw.wideLeftInt
  have hpreviousSpan : 0 <= previousSpan :=
    (show (0 : Int) <= previousX by omega).trans
      previous.raw.extentX_le_wideSpan
  let currentX := previousSpan.toNat + 2 * padding
  have hcurrentX : thresholdX <= currentX := by
    have hspan : previousX <= previousSpan.toNat := by
      rw [Int.le_toNat hpreviousSpan]
      exact previous.raw.extentX_le_wideSpan
    exact (show thresholdX = previousX by rfl) |>.trans_le
      (hspan.trans (Nat.le_add_right _ _))
  let current := Classical.choice
    (hthreshold (extentX := currentX) (extentY := currentY)
      hcurrentX (by simp [currentY, nextY]))
  let currentSpan := current.raw.wideRightInt - current.raw.wideLeftInt
  have hcurrentSpan : 0 <= currentSpan :=
    (show (0 : Int) <= currentX by omega).trans
      current.raw.extentX_le_wideSpan
  let nextX := currentSpan.toNat + 2 * padding
  have hnextX : thresholdX <= nextX := by
    have hspan : currentX <= currentSpan.toNat := by
      rw [Int.le_toNat hcurrentSpan]
      exact current.raw.extentX_le_wideSpan
    exact hcurrentX.trans (hspan.trans (Nat.le_add_right _ _))
  let next := Classical.choice
    (hthreshold (extentX := nextX) (extentY := nextY)
      hnextX (by simp [nextY]))
  refine ⟨{
    previousX := previousX
    previousY := previousY
    currentX := currentX
    currentY := currentY
    nextX := nextX
    nextY := nextY
    previous := previous
    current := current
    next := next
    currentX_eq := ?_
    nextX_eq := ?_
    previousY_eq := rfl
    currentY_eq := rfl }⟩
  · change ((previousSpan.toNat + 2 * padding : Nat) : Int) =
      previousSpan + 2 * (padding : Int)
    push_cast
    rw [Int.toNat_of_nonneg hpreviousSpan]
  · change ((currentSpan.toNat + 2 * padding : Nat) : Int) =
      currentSpan + 2 * (padding : Int)
    push_cast
    rw [Int.toNat_of_nonneg hcurrentSpan]


theorem exists_alignedCrossNestedThreePairedMixedBoundaryScores_ge
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
    (k padding lowerX lowerY : Nat) :
    exists data : AlignedCrossNestedThreePairedMixedBoundaryScores
        E Edual mu muDual S Sdual p pDual family familyDual schedule k padding,
      lowerX <= data.currentX /\ lowerY <= data.currentY /\
      (lowerX : Int) <= data.current.raw.wideRightInt -
        data.current.raw.wideLeftInt := by
  obtain ⟨thresholdX, thresholdY, hthreshold⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E Edual mu muDual hTI hTIDual family familyDual schedule k
  let nextY := max thresholdY lowerY
  let currentY := nextY + 2 * padding
  let previousY := currentY + 2 * padding
  let previousX := max thresholdX lowerX
  let previous := Classical.choice
    (hthreshold (extentX := previousX) (extentY := previousY)
      (Nat.le_max_left _ _)
      (by dsimp [previousY, currentY, nextY]; omega))
  let previousSpan :=
    previous.raw.wideRightInt - previous.raw.wideLeftInt
  have hpreviousSpan : 0 <= previousSpan :=
    (show (0 : Int) <= previousX by omega).trans
      previous.raw.extentX_le_wideSpan
  let currentX := previousSpan.toNat + 2 * padding
  have hpreviousXSpan : previousX <= previousSpan.toNat := by
    rw [Int.le_toNat hpreviousSpan]
    exact previous.raw.extentX_le_wideSpan
  have hcurrentX : thresholdX <= currentX :=
    (Nat.le_max_left _ _).trans
      (hpreviousXSpan.trans (Nat.le_add_right _ _))
  let current := Classical.choice
    (hthreshold (extentX := currentX) (extentY := currentY)
      hcurrentX
      ((Nat.le_max_left _ _).trans (Nat.le_add_right _ _)))
  let currentSpan := current.raw.wideRightInt - current.raw.wideLeftInt
  have hcurrentSpan : 0 <= currentSpan :=
    (show (0 : Int) <= currentX by omega).trans
      current.raw.extentX_le_wideSpan
  let nextX := currentSpan.toNat + 2 * padding
  have hnextX : thresholdX <= nextX := by
    have hspan : currentX <= currentSpan.toNat := by
      rw [Int.le_toNat hcurrentSpan]
      exact current.raw.extentX_le_wideSpan
    exact hcurrentX.trans (hspan.trans (Nat.le_add_right _ _))
  let next := Classical.choice
    (hthreshold (extentX := nextX) (extentY := nextY)
      hnextX (Nat.le_max_left _ _))
  let data : AlignedCrossNestedThreePairedMixedBoundaryScores
      E Edual mu muDual S Sdual p pDual family familyDual schedule k
      padding := {
    previousX := previousX
    previousY := previousY
    currentX := currentX
    currentY := currentY
    nextX := nextX
    nextY := nextY
    previous := previous
    current := current
    next := next
    currentX_eq := by
      change ((previousSpan.toNat + 2 * padding : Nat) : Int) =
        previousSpan + 2 * (padding : Int)
      push_cast
      rw [Int.toNat_of_nonneg hpreviousSpan]
    nextX_eq := by
      change ((currentSpan.toNat + 2 * padding : Nat) : Int) =
        currentSpan + 2 * (padding : Int)
      push_cast
      rw [Int.toNat_of_nonneg hcurrentSpan]
    previousY_eq := rfl
    currentY_eq := rfl }
  refine ⟨data, ?_, ?_, ?_⟩
  · exact (Nat.le_max_right _ _).trans
      (hpreviousXSpan.trans (Nat.le_add_right _ _))
  · exact (Nat.le_max_right _ _).trans (Nat.le_add_right _ _)
  · have hlowerNat : lowerX <= currentX :=
      (Nat.le_max_right _ _).trans
        (hpreviousXSpan.trans (Nat.le_add_right _ _))
    have hlowerInt : (lowerX : Int) <= (currentX : Int) := by
      exact_mod_cast hlowerNat
    exact hlowerInt.trans current.raw.extentX_le_wideSpan


theorem nonempty_alignedRotatedCrossNestedThreePairedMixedBoundaryScores
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
    (k padding : Nat) :
    Nonempty (AlignedCrossNestedThreePairedMixedBoundaryScores
      E.axisSwap Edual.axisSwap mu muDual S Sdual p pDual
      family.axisSwap familyDual.axisSwap schedule.axisSwap k padding) := by
  exact nonempty_alignedCrossNestedThreePairedMixedBoundaryScores
    E.axisSwap Edual.axisSwap mu muDual
    (P.axisSwap_isTranslationInvariant mu hTI)
    (Pdual.axisSwap_isTranslationInvariant muDual hTIDual)
    family.axisSwap familyDual.axisSwap schedule.axisSwap k padding


end StatMech.FK.PeriodicPlanar
