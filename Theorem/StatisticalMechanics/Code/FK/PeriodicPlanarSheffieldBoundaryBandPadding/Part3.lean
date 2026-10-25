/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandPadding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepTemplateGridAssembly
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldOrientedBoundary
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandPadding.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


@[simp] theorem boundaryBandPreferenceColor_eq_true_of_lower
    {margin extent position : Nat} {epsilon preferred opposite : Real}
    (hposition : position ≤ margin) :
    boundaryBandPreferenceColor margin extent position
      epsilon preferred opposite = true := by
  simp [boundaryBandPreferenceColor, hposition]

@[simp] theorem boundaryBandPreferenceColor_eq_false_of_upper
    {margin extent position : Nat} {epsilon preferred opposite : Real}
    (hsep : 2 * margin < extent)
    (hposition : extent ≤ position + margin) :
    boundaryBandPreferenceColor margin extent position
      epsilon preferred opposite = false := by
  have hnot : ¬position ≤ margin := by omega
  simp [boundaryBandPreferenceColor, hnot, hposition]


theorem boundaryBandPreferenceColor_true_imp
    {margin extent position : Nat} {epsilon preferred opposite p : Real}
    (hepsilon : 0 ≤ epsilon) (hsep : 2 * margin < extent)
    (hopposite : opposite ≤ 1)
    (hlower : position ≤ margin → p ≤ preferred)
    (hdefect : 1 - p ≤ epsilon)
    (hcolor : boundaryBandPreferenceColor margin extent position
      epsilon preferred opposite = true) :
    opposite ≤ preferred + epsilon := by
  by_cases hlowerBand : position ≤ margin
  · linarith [hlower hlowerBand]
  by_cases hupperBand : extent ≤ position + margin
  · simp [boundaryBandPreferenceColor, hlowerBand, hupperBand] at hcolor
  · have hdecide : decide (opposite ≤ preferred + epsilon) = true := by
      simpa [boundaryBandPreferenceColor, hlowerBand, hupperBand] using hcolor
    exact of_decide_eq_true hdecide


theorem boundaryBandPreferenceColor_false_imp
    {margin extent position : Nat} {epsilon preferred opposite p : Real}
    (hepsilon : 0 ≤ epsilon) (hsep : 2 * margin < extent)
    (hpreferred : preferred ≤ 1)
    (hupper : extent ≤ position + margin → p ≤ opposite)
    (hdefect : 1 - p ≤ epsilon)
    (hcolor : boundaryBandPreferenceColor margin extent position
      epsilon preferred opposite = false) :
    preferred ≤ opposite + epsilon := by
  by_cases hlowerBand : position ≤ margin
  · simp [boundaryBandPreferenceColor, hlowerBand] at hcolor
  by_cases hupperBand : extent ≤ position + margin
  · linarith [hupper hupperBand]
  · have hdecide : decide (opposite ≤ preferred + epsilon) = false := by
      simpa [boundaryBandPreferenceColor, hlowerBand, hupperBand] using hcolor
    have hnot : ¬opposite ≤ preferred + epsilon := of_decide_eq_false hdecide
    linarith

end StatMech.FK.PeriodicPlanar
