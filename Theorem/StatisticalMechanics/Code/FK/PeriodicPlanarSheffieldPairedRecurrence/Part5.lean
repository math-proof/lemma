/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem nonempty_alignedNormalRotatedInsetPairedMixedBoundaryScores
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
    Nonempty (AlignedNormalRotatedInsetPairedMixedBoundaryScores
      E Edual mu muDual S Sdual p pDual family familyDual schedule k
      padding) := by
  obtain ⟨normalThresholdX, normalThresholdY, hnormal⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E Edual mu muDual hTI hTIDual family familyDual schedule k
  obtain ⟨rotatedThresholdX, rotatedThresholdY, hrotated⟩ :=
    exists_alignedExactExtentPairedMixedBoundaryScores_thresholds
      E.axisSwap Edual.axisSwap mu muDual
      (P.axisSwap_isTranslationInvariant mu hTI)
      (Pdual.axisSwap_isTranslationInvariant muDual hTIDual)
      family.axisSwap familyDual.axisSwap schedule.axisSwap k
  let normalX := max normalThresholdX (rotatedThresholdY + 2 * padding)
  let rotatedX := max rotatedThresholdX normalThresholdY
  let normalProbe := Classical.choice
    (hnormal (Nat.le_max_left _ _) le_rfl :
      Nonempty (AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
        S Sdual p pDual family familyDual schedule k normalX
        normalThresholdY))
  let rotatedProbe := Classical.choice
    (hrotated (Nat.le_max_left _ _) le_rfl :
      Nonempty (AlignedExactExtentPairedMixedBoundaryScores
        E.axisSwap Edual.axisSwap mu muDual S Sdual p pDual
        family.axisSwap familyDual.axisSwap schedule.axisSwap k rotatedX
        rotatedThresholdY))
  let normalSpan := pairedWideSpanAtExtentX E Edual family familyDual
    schedule k normalX
  let rotatedSpan := pairedWideSpanAtExtentX E.axisSwap Edual.axisSwap
    family.axisSwap familyDual.axisSwap schedule.axisSwap k rotatedX
  have hnormalXSpan : (normalX : Int) <= normalSpan := by
    calc
      (normalX : Int) <= normalProbe.raw.wideRightInt -
          normalProbe.raw.wideLeftInt :=
        normalProbe.raw.extentX_le_wideSpan
      _ = normalSpan := by
        simpa only [normalSpan] using normalProbe.wideSpan_formula
  have hrotatedXSpan : (rotatedX : Int) <= rotatedSpan := by
    calc
      (rotatedX : Int) <= rotatedProbe.raw.wideRightInt -
          rotatedProbe.raw.wideLeftInt :=
        rotatedProbe.raw.extentX_le_wideSpan
      _ = rotatedSpan := by
        simpa only [rotatedSpan] using rotatedProbe.wideSpan_formula
  have hnormalSpanPadding : (2 * padding : Int) <= normalSpan := by
    have hX : rotatedThresholdY + 2 * padding <= normalX :=
      Nat.le_max_right _ _
    have hcast : (2 * padding : Int) <= (normalX : Int) := by
      exact_mod_cast (show 2 * padding <= normalX by omega)
    exact hcast.trans hnormalXSpan
  let rotatedY := (normalSpan - 2 * (padding : Int)).toNat
  let normalY := rotatedSpan.toNat
  have hrotatedThresholdY : rotatedThresholdY <= rotatedY := by
    have hX : rotatedThresholdY + 2 * padding <= normalX :=
      Nat.le_max_right _ _
    have hcastX : (rotatedThresholdY + 2 * padding : Int) <=
        (normalX : Int) := by
      exact_mod_cast hX
    have hcast : (rotatedThresholdY + 2 * padding : Int) <= normalSpan :=
      hcastX.trans hnormalXSpan
    have hnonneg : 0 <= normalSpan - 2 * (padding : Int) := by omega
    have hcastY : (rotatedThresholdY : Int) <= (rotatedY : Int) := by
      change (rotatedThresholdY : Int) <=
        ((normalSpan - 2 * (padding : Int)).toNat : Int)
      rw [Int.toNat_of_nonneg hnonneg]
      omega
    exact_mod_cast hcastY
  have hnormalThresholdY : normalThresholdY <= normalY := by
    have hX : normalThresholdY <= rotatedX := Nat.le_max_right _ _
    have hcastX : (normalThresholdY : Int) <= (rotatedX : Int) := by
      exact_mod_cast hX
    have hcast : (normalThresholdY : Int) <= rotatedSpan :=
      hcastX.trans hrotatedXSpan
    have hnonneg : 0 <= rotatedSpan := by
      exact (show (0 : Int) <= (rotatedX : Int) by omega).trans
        hrotatedXSpan
    have hcastY : (normalThresholdY : Int) <= (normalY : Int) := by
      change (normalThresholdY : Int) <= (rotatedSpan.toNat : Int)
      rw [Int.toNat_of_nonneg hnonneg]
      exact hcast
    exact_mod_cast hcastY
  let normal := Classical.choice
    (hnormal (Nat.le_max_left _ _) hnormalThresholdY :
      Nonempty (AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
        S Sdual p pDual family familyDual schedule k normalX normalY))
  let rotated := Classical.choice
    (hrotated (Nat.le_max_left _ _) hrotatedThresholdY :
      Nonempty (AlignedExactExtentPairedMixedBoundaryScores
        E.axisSwap Edual.axisSwap mu muDual S Sdual p pDual
        family.axisSwap familyDual.axisSwap schedule.axisSwap k rotatedX
        rotatedY))
  refine ⟨{
    normalX := normalX
    rotatedX := rotatedX
    normalY := normalY
    rotatedY := rotatedY
    normal := normal
    rotated := rotated
    normalSpan_eq := ?_
    rotatedSpan_eq := ?_ }⟩
  · rw [normal.wideSpan_formula]
    change normalSpan = (rotatedY : Int) + 2 * (padding : Int)
    have hnonneg : 0 <= normalSpan - 2 * (padding : Int) := by
      exact sub_nonneg.mpr hnormalSpanPadding
    change normalSpan =
      ((normalSpan - 2 * (padding : Int)).toNat : Int) +
        2 * (padding : Int)
    rw [Int.toNat_of_nonneg hnonneg]
    omega
  · rw [rotated.wideSpan_formula]
    change rotatedSpan = (normalY : Int)
    have hnonneg : 0 <= rotatedSpan := by
      exact (show (0 : Int) <= (rotatedX : Int) by omega).trans
        hrotatedXSpan
    change rotatedSpan = (rotatedSpan.toNat : Int)
    rw [Int.toNat_of_nonneg hnonneg]


end StatMech.FK.PeriodicPlanar
