/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part7
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem nonempty_crossNestedThreePairedMixedBoundaryScores
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
    Nonempty (CrossNestedThreePairedMixedBoundaryScores E Edual mu muDual
      S Sdual p pDual padding) := by
  obtain ⟨thresholdX, thresholdY, hthreshold⟩ :=
    exists_exactExtentPairedMixedBoundaryScores_thresholds
      E Edual mu muDual hTI hTIDual family familyDual schedule k
  let nextY := thresholdY
  let currentY := nextY + 2 * padding
  let previousY := currentY + 2 * padding
  let previousX := thresholdX
  let previous := Classical.choice
    (hthreshold (extentX := previousX) (extentY := previousY)
      (by simp [previousX]) (by dsimp [previousY, currentY, nextY]; omega))
  let previousSpan := previous.wideRightInt - previous.wideLeftInt
  have hpreviousSpan : 0 <= previousSpan :=
    (show (0 : Int) <= previousX by omega).trans
      previous.extentX_le_wideSpan
  let currentX := previousSpan.toNat + 2 * padding
  have hcurrentX : thresholdX <= currentX := by
    have hspan : previousX <= previousSpan.toNat := by
      rw [Int.le_toNat hpreviousSpan]
      exact previous.extentX_le_wideSpan
    exact (show thresholdX = previousX by rfl) |>.trans_le
      (hspan.trans (Nat.le_add_right _ _))
  let current := Classical.choice
    (hthreshold (extentX := currentX) (extentY := currentY)
      hcurrentX (by simp [currentY, nextY]))
  let currentSpan := current.wideRightInt - current.wideLeftInt
  have hcurrentSpan : 0 <= currentSpan :=
    (show (0 : Int) <= currentX by omega).trans
      current.extentX_le_wideSpan
  let nextX := currentSpan.toNat + 2 * padding
  have hnextX : thresholdX <= nextX := by
    have hspan : currentX <= currentSpan.toNat := by
      rw [Int.le_toNat hcurrentSpan]
      exact current.extentX_le_wideSpan
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


theorem exists_exactExtentPairedMixedBoundaryScores_ge
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
    (k minimumX minimumY : Nat) :
    exists extentX extentY,
      minimumX <= extentX /\ minimumY <= extentY /\
      Nonempty (ExactExtentPairedMixedBoundaryScores E Edual mu muDual
        S Sdual p pDual extentX extentY) := by
  let h := schedule.horizontal k
  let v := schedule.vertical k
  let radiusX := max
    (max (family.radiusLeft h) (family.radiusRight h))
    (max (familyDual.radiusLeft h) (familyDual.radiusRight h))
  let radiusY := max
    (max (family.radiusBottom v) (family.radiusTop v))
    (max (familyDual.radiusBottom v) (familyDual.radiusTop v))
  obtain ⟨extentX, extentY, width, height, widthDual, heightDual,
      hminX, hminY, hwidth, hheight, hwidthDual, hheightDual,
      hb, hbDual, hd, hdDual⟩ :=
    exists_pairedMixedGridDimensions E Edual family familyDual h v
      (max minimumX radiusX) (max minimumY radiusY)
  have hminimumX : minimumX <= extentX :=
    (Nat.le_max_left _ _).trans hminX
  have hminimumY : minimumY <= extentY :=
    (Nat.le_max_left _ _).trans hminY
  have hleftP : family.radiusLeft h <= extentX :=
    (Nat.le_max_left _ _).trans (Nat.le_max_left _ _) |>.trans
      ((Nat.le_max_right _ _).trans hminX)
  have hrightP : family.radiusRight h <= extentX :=
    (Nat.le_max_right _ _).trans (Nat.le_max_left _ _) |>.trans
      ((Nat.le_max_right _ _).trans hminX)
  have hleftD : familyDual.radiusLeft h <= extentX :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _) |>.trans
      ((Nat.le_max_right _ _).trans hminX)
  have hrightD : familyDual.radiusRight h <= extentX :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _) |>.trans
      ((Nat.le_max_right _ _).trans hminX)
  have hbottomP : family.radiusBottom v <= extentY :=
    (Nat.le_max_left _ _).trans (Nat.le_max_left _ _) |>.trans
      ((Nat.le_max_right _ _).trans hminY)
  have htopP : family.radiusTop v <= extentY :=
    (Nat.le_max_right _ _).trans (Nat.le_max_left _ _) |>.trans
      ((Nat.le_max_right _ _).trans hminY)
  have hbottomD : familyDual.radiusBottom v <= extentY :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _) |>.trans
      ((Nat.le_max_right _ _).trans hminY)
  have htopD : familyDual.radiusTop v <= extentY :=
    (Nat.le_max_right _ _).trans (Nat.le_max_right _ _) |>.trans
      ((Nat.le_max_right _ _).trans hminY)
  have hposX : 0 < family.baseRight 0 - h + extentX -
      (family.baseLeft 0 + h) := by omega
  have hposXDual : 0 < familyDual.baseRight 0 - h + extentX -
      (familyDual.baseLeft 0 + h) := by omega
  have hposY : 0 < family.baseTop 1 - v + extentY -
      (family.baseBottom 1 + v) := by omega
  have hposYDual : 0 < familyDual.baseTop 1 - v + extentY -
      (familyDual.baseBottom 1 + v) := by omega
  refine ⟨extentX, extentY, hminimumX, hminimumY, ?_⟩
  exact exists_pairedMixedBoundaryScores_atExtents E Edual mu muDual
    hTI hTIDual family familyDual schedule k extentX extentY
    hposX hposXDual hposY hposYDual hleftP hrightP hbottomP htopP
    hleftD hrightD hbottomD htopD


theorem exists_pairedCommonBoundaryPairMergeRadius
    (P : PeriodicGraph V) (Pdual : PeriodicGraph W)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
    [IsProbabilityMeasure muDual]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (huniqueDual :
      muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (bottom top left right : Finset V)
    (bottomDual topDual leftDual rightDual : Finset W)
    (cutoff : Nat) {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists radius, cutoff <= radius /\
      mu.real (P.pairMergeErrorUnion bottom top radius) < epsilon /\
      mu.real (P.pairMergeErrorUnion left right radius) < epsilon /\
      muDual.real
        (Pdual.pairMergeErrorUnion bottomDual topDual radius) < epsilon /\
      muDual.real
        (Pdual.pairMergeErrorUnion leftDual rightDual radius) < epsilon := by
  have hPV : ∀ᶠ radius in atTop,
      mu.real (P.pairMergeErrorUnion bottom top radius) < epsilon :=
    (tendsto_order.1
      (P.pairMergeErrorUnion_real_tendsto_zero
        mu hunique bottom top)).2 epsilon hepsilon
  have hPH : ∀ᶠ radius in atTop,
      mu.real (P.pairMergeErrorUnion left right radius) < epsilon :=
    (tendsto_order.1
      (P.pairMergeErrorUnion_real_tendsto_zero
        mu hunique left right)).2 epsilon hepsilon
  have hDV : ∀ᶠ radius in atTop,
      muDual.real
        (Pdual.pairMergeErrorUnion bottomDual topDual radius) < epsilon :=
    (tendsto_order.1
      (Pdual.pairMergeErrorUnion_real_tendsto_zero
        muDual huniqueDual bottomDual topDual)).2 epsilon hepsilon
  have hDH : ∀ᶠ radius in atTop,
      muDual.real
        (Pdual.pairMergeErrorUnion leftDual rightDual radius) < epsilon :=
    (tendsto_order.1
      (Pdual.pairMergeErrorUnion_real_tendsto_zero
        muDual huniqueDual leftDual rightDual)).2 epsilon hepsilon
  have hall := hPV.and (hPH.and (hDV.and hDH))
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 hall
  let radius := max cutoff threshold
  have hr := hthreshold radius (Nat.le_max_right _ _)
  exact ⟨radius, Nat.le_max_left _ _, hr.1, hr.2.1, hr.2.2.1,
    hr.2.2.2⟩


end StatMech.FK.PeriodicPlanar
