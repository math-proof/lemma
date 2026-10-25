/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualBoundaryBands.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRecursiveLimits
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldNormalBoundaryBandAssembly
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonSquareEnlarge
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDualBoundaryBands
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem int_le_nat_of_toNat_le_paired {x : Int} {n : Nat}
    (h : x.toNat ≤ n) : x ≤ n := by
  by_cases hx : 0 ≤ x
  · have h' : (x.toNat : Int) ≤ (n : Int) := by exact_mod_cast h
    rwa [Int.toNat_of_nonneg hx] at h'
  · omega


theorem exists_pairedAlignedMarginSchedule
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    (verticalRequirement horizontalRequirement : Nat → Nat) :
    Nonempty (PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement) := by
  let verticalStep : Nat → Nat := fun h ↦ max
    (max (family.fullVerticalRequirement E h)
      (familyDual.fullVerticalRequirement Edual h))
    (verticalRequirement h)
  let horizontalStep : Nat → Nat := fun v ↦ max
    (max (family.fullHorizontalRequirement E v)
      (familyDual.fullHorizontalRequirement Edual v))
    (horizontalRequirement v)
  obtain ⟨horizontal, vertical, hh, hv, hhv, hvh⟩ :=
    exists_alternating_dominating_sequences verticalStep horizontalStep
  have hPV (n : Nat) : family.fullVerticalRequirement E (horizontal n) ≤
      vertical n :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_left _ _).trans (hhv n))
  have hDV (n : Nat) :
      familyDual.fullVerticalRequirement Edual (horizontal n) ≤ vertical n :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_left _ _).trans (hhv n))
  have hPH (n : Nat) : family.fullHorizontalRequirement E (vertical n) ≤
      horizontal (n + 1) :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_left _ _).trans (hvh n))
  have hDH (n : Nat) :
      familyDual.fullHorizontalRequirement Edual (vertical n) ≤
        horizontal (n + 1) :=
    (Nat.le_max_right _ _).trans ((Nat.le_max_left _ _).trans (hvh n))
  have verticalReq (n : Nat) :
      verticalRequirement (horizontal n) ≤ vertical n :=
    (Nat.le_max_right _ _).trans (hhv n)
  have horizontalReq (n : Nat) :
      horizontalRequirement (vertical n) ≤ horizontal (n + 1) :=
    (Nat.le_max_right _ _).trans (hvh n)
  refine ⟨{
    horizontal := horizontal
    vertical := vertical
    horizontal_tendsto := hh
    vertical_tendsto := hv
    vertical_requirement := verticalReq
    horizontal_requirement := horizontalReq
    primal_left_bottom := ?_
    primal_right_bottom := ?_
    primal_left_top := ?_
    primal_right_top := ?_
    primal_bottom_left := ?_
    primal_top_left := ?_
    primal_bottom_right := ?_
    primal_top_right := ?_
    dual_left_bottom := ?_
    dual_right_bottom := ?_
    dual_left_top := ?_
    dual_right_top := ?_
    dual_bottom_left := ?_
    dual_top_left := ?_
    dual_bottom_right := ?_
    dual_top_right := ?_ }⟩
  all_goals intro n
  · have h := (Nat.le_max_left
      (max (((family.radiusLeft (horizontal n) : Int) +
        family.baseLeft 1 - family.baseBottom 1).toNat)
        (((family.radiusRight (horizontal n) : Int) +
          family.baseRight 1 - family.baseBottom 1).toNat)) _).trans (hPV n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_left _ _).trans h)
    omega
  · have h := (Nat.le_max_left
      (max (((family.radiusLeft (horizontal n) : Int) +
        family.baseLeft 1 - family.baseBottom 1).toNat)
        (((family.radiusRight (horizontal n) : Int) +
          family.baseRight 1 - family.baseBottom 1).toNat)) _).trans (hPV n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_right _ _).trans h)
    omega
  · have h := (Nat.le_max_right _ _).trans (hPV n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_left _ _).trans h)
    omega
  · have h := (Nat.le_max_right _ _).trans (hPV n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_right _ _).trans h)
    omega
  · have h := (Nat.le_max_left _ _).trans (hPH n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_left _ _).trans h)
    omega
  · have h := (Nat.le_max_left _ _).trans (hPH n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_right _ _).trans h)
    omega
  · have h := (Nat.le_max_right _ _).trans (hPH n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_left _ _).trans h)
    omega
  · have h := (Nat.le_max_right _ _).trans (hPH n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_right _ _).trans h)
    omega
  · have h := (Nat.le_max_left
      (max (((familyDual.radiusLeft (horizontal n) : Int) +
        familyDual.baseLeft 1 - familyDual.baseBottom 1).toNat)
        (((familyDual.radiusRight (horizontal n) : Int) +
          familyDual.baseRight 1 - familyDual.baseBottom 1).toNat)) _).trans
      (hDV n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_left _ _).trans h)
    omega
  · have h := (Nat.le_max_left
      (max (((familyDual.radiusLeft (horizontal n) : Int) +
        familyDual.baseLeft 1 - familyDual.baseBottom 1).toNat)
        (((familyDual.radiusRight (horizontal n) : Int) +
          familyDual.baseRight 1 - familyDual.baseBottom 1).toNat)) _).trans
      (hDV n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_right _ _).trans h)
    omega
  · have h := (Nat.le_max_right _ _).trans (hDV n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_left _ _).trans h)
    omega
  · have h := (Nat.le_max_right _ _).trans (hDV n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_right _ _).trans h)
    omega
  · have h := (Nat.le_max_left _ _).trans (hDH n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_left _ _).trans h)
    omega
  · have h := (Nat.le_max_left _ _).trans (hDH n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_right _ _).trans h)
    omega
  · have h := (Nat.le_max_right _ _).trans (hDH n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_left _ _).trans h)
    omega
  · have h := (Nat.le_max_right _ _).trans (hDH n)
    have := int_le_nat_of_toNat_le_paired ((Nat.le_max_right _ _).trans h)
    omega


theorem exists_pairedMixedGridDimensions
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    (horizontalMargin verticalMargin minimumX minimumY : Nat) :
    ∃ extentX extentY width height widthDual heightDual : Nat,
      minimumX ≤ extentX ∧ minimumY ≤ extentY ∧
      0 < width ∧ 0 < height ∧ 0 < widthDual ∧ 0 < heightDual ∧
      (family.baseLeft 0 + horizontalMargin + width -
        (family.baseRight 0 - horizontalMargin) : Int) = extentX ∧
      (familyDual.baseLeft 0 + horizontalMargin + widthDual -
        (familyDual.baseRight 0 - horizontalMargin) : Int) = extentX ∧
      (family.baseBottom 1 + verticalMargin + height -
        (family.baseTop 1 - verticalMargin) : Int) = extentY ∧
      (familyDual.baseBottom 1 + verticalMargin + heightDual -
        (familyDual.baseTop 1 - verticalMargin) : Int) = extentY := by
  let left : Site 2 := family.baseLeft + horizontalShift horizontalMargin
  let right : Site 2 := family.baseRight +
    horizontalShift (-(horizontalMargin : Int))
  let bottom : Site 2 := family.baseBottom + verticalShift verticalMargin
  let top : Site 2 := family.baseTop +
    verticalShift (-(verticalMargin : Int))
  let leftDual : Site 2 :=
    familyDual.baseLeft + horizontalShift horizontalMargin
  let rightDual : Site 2 := familyDual.baseRight +
    horizontalShift (-(horizontalMargin : Int))
  let bottomDual : Site 2 :=
    familyDual.baseBottom + verticalShift verticalMargin
  let topDual : Site 2 := familyDual.baseTop +
    verticalShift (-(verticalMargin : Int))
  obtain ⟨extentX, extentY, hminX, hminY,
      hx, hxDual, hy, hyDual⟩ :=
    exists_commonPreferenceExtents_ge left right bottom top
      leftDual rightDual bottomDual topDual minimumX minimumY
  let width := boundaryGridWidth extentX left right
  let height := boundaryGridHeight extentY bottom top
  let widthDual := boundaryGridWidth extentX leftDual rightDual
  let heightDual := boundaryGridHeight extentY bottomDual topDual
  have hwidth : 0 < width := boundaryGridWidth_pos _ _ _ hx
  have hheight : 0 < height := boundaryGridHeight_pos _ _ _ hy
  have hwidthDual : 0 < widthDual :=
    boundaryGridWidth_pos _ _ _ hxDual
  have hheightDual : 0 < heightDual :=
    boundaryGridHeight_pos _ _ _ hyDual
  refine ⟨extentX, extentY, width, height, widthDual, heightDual,
    hminX, hminY, hwidth, hheight, hwidthDual, hheightDual,
    ?_, ?_, ?_, ?_⟩
  · have hnonneg : 0 ≤ right 0 + (extentX : Int) - left 0 := hx.le
    have hwidthCast : (width : Int) = right 0 + extentX - left 0 := by
      dsimp only [width, boundaryGridWidth]
      rw [Int.toNat_of_nonneg hnonneg]
    rw [hwidthCast]
    simp [left, right]
    omega
  · have hnonneg :
      0 ≤ rightDual 0 + (extentX : Int) - leftDual 0 := hxDual.le
    have hwidthCast :
        (widthDual : Int) = rightDual 0 + extentX - leftDual 0 := by
      dsimp only [widthDual, boundaryGridWidth]
      rw [Int.toNat_of_nonneg hnonneg]
    rw [hwidthCast]
    simp [leftDual, rightDual]
    omega
  · have hnonneg : 0 ≤ top 1 + (extentY : Int) - bottom 1 := hy.le
    have hheightCast : (height : Int) = top 1 + extentY - bottom 1 := by
      dsimp only [height, boundaryGridHeight]
      rw [Int.toNat_of_nonneg hnonneg]
    rw [hheightCast]
    simp [bottom, top]
    omega
  · have hnonneg :
      0 ≤ topDual 1 + (extentY : Int) - bottomDual 1 := hyDual.le
    have hheightCast :
        (heightDual : Int) = topDual 1 + extentY - bottomDual 1 := by
      dsimp only [heightDual, boundaryGridHeight]
      rw [Int.toNat_of_nonneg hnonneg]
    rw [hheightCast]
    simp [bottomDual, topDual]
    omega


end StatMech.FK.PeriodicPlanar
