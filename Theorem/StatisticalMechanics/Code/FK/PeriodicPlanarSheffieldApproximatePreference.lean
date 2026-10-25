/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldApproximatePreference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceClosure
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice


theorem exists_common_approximate_preference_grid_witness
    {n m : Nat} (hn : 0 < n) (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (bottom top left right : PreferenceGridVertex n m → Real)
    (hbottom : ∀ i : Fin (n + 1),
      top (i, 0) ≤ bottom (i, 0) + epsilon)
    (htop : ∀ i : Fin (n + 1),
      bottom (i, Fin.last m) + epsilon < top (i, Fin.last m))
    (hleft : ∀ j : Fin (m + 1),
      right (0, j) ≤ left (0, j) + epsilon)
    (hright : ∀ j : Fin (m + 1),
      left (Fin.last n, j) + epsilon < right (Fin.last n, j)) :
    ∃ x xVertical xHorizontal : PreferenceGridVertex n m,
      top x ≤ bottom x + epsilon ∧
      right x ≤ left x + epsilon ∧
      KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧
      bottom xVertical ≤ top xVertical + epsilon ∧
      KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧
      left xHorizontal ≤ right xHorizontal + epsilon := by
  let vertical : PreferenceGridVertex n m → Bool := fun x =>
    decide (top x ≤ bottom x + epsilon)
  let horizontal : PreferenceGridVertex n m → Bool := fun x =>
    decide (right x ≤ left x + epsilon)
  have hvBottom : ∀ i : Fin (n + 1), vertical (i, 0) = true := by
    intro i
    simp [vertical, hbottom i]
  have hvTop : ∀ i : Fin (n + 1), vertical (i, Fin.last m) = false := by
    intro i
    simp [vertical, not_le.mpr (htop i)]
  have hhLeft : ∀ j : Fin (m + 1), horizontal (0, j) = true := by
    intro j
    simp [horizontal, hleft j]
  have hhRight : ∀ j : Fin (m + 1), horizontal (Fin.last n, j) = false := by
    intro j
    simp [horizontal, not_le.mpr (hright j)]
  obtain ⟨x, hxv, hxh, ⟨xVertical, hxVertical, hxvFalse⟩,
      ⟨xHorizontal, hxHorizontal, hxhFalse⟩⟩ :=
    exists_common_preference_grid_witness hn vertical horizontal true false
      hvBottom hvTop (by decide) hhLeft hhRight
  have hxv' : top x ≤ bottom x + epsilon := by
    simpa [vertical] using hxv
  have hxh' : right x ≤ left x + epsilon := by
    simpa [horizontal] using hxh
  have hxvNot : ¬top xVertical ≤ bottom xVertical + epsilon := by
    simpa [vertical] using hxvFalse
  have hxhNot : ¬right xHorizontal ≤ left xHorizontal + epsilon := by
    simpa [horizontal] using hxhFalse
  exact ⟨x, xVertical, xHorizontal, hxv', hxh', hxVertical,
    by linarith, hxHorizontal, by linarith⟩


theorem exists_common_weak_approximate_preference_grid_witness
    {n m : Nat} (hn : 0 < n) (hm : 0 < m)
    (epsilon : Real) (hepsilon : 0 ≤ epsilon)
    (bottom top left right : PreferenceGridVertex n m → Real)
    (hbottom : ∀ i : Fin (n + 1),
      top (i, 0) ≤ bottom (i, 0) + epsilon)
    (htop : ∀ i : Fin (n + 1),
      bottom (i, Fin.last m) ≤ top (i, Fin.last m) + epsilon)
    (hleft : ∀ j : Fin (m + 1),
      right (0, j) ≤ left (0, j) + epsilon)
    (hright : ∀ j : Fin (m + 1),
      left (Fin.last n, j) ≤ right (Fin.last n, j) + epsilon) :
    ∃ x xVertical xHorizontal : PreferenceGridVertex n m,
      top x ≤ bottom x + epsilon ∧
      right x ≤ left x + epsilon ∧
      KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧
      bottom xVertical ≤ top xVertical + epsilon ∧
      KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧
      left xHorizontal ≤ right xHorizontal + epsilon := by
  let vertical : PreferenceGridVertex n m → Bool := fun x =>
    if x.2 = Fin.last m then false else
      decide (top x ≤ bottom x + epsilon)
  let horizontal : PreferenceGridVertex n m → Bool := fun x =>
    if x.1 = Fin.last n then false else
      decide (right x ≤ left x + epsilon)
  have hzeroLastM : (0 : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hzeroLastN : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hvBottom : ∀ i : Fin (n + 1), vertical (i, 0) = true := by
    intro i
    simp [vertical, hzeroLastM, hbottom i]
  have hvTop : ∀ i : Fin (n + 1),
      vertical (i, Fin.last m) = false := by
    intro i
    simp [vertical]
  have hhLeft : ∀ j : Fin (m + 1), horizontal (0, j) = true := by
    intro j
    simp [horizontal, hzeroLastN, hleft j]
  have hhRight : ∀ j : Fin (m + 1),
      horizontal (Fin.last n, j) = false := by
    intro j
    simp [horizontal]
  obtain ⟨x, hxv, hxh, ⟨xVertical, hxVertical, hxvFalse⟩,
      ⟨xHorizontal, hxHorizontal, hxhFalse⟩⟩ :=
    exists_common_preference_grid_witness hn vertical horizontal true false
      hvBottom hvTop (by decide) hhLeft hhRight
  have hxv' : top x ≤ bottom x + epsilon := by
    by_cases htopRow : x.2 = Fin.last m
    · simp [vertical, htopRow] at hxv
    · simpa [vertical, htopRow] using hxv
  have hxh' : right x ≤ left x + epsilon := by
    by_cases hrightCol : x.1 = Fin.last n
    · simp [horizontal, hrightCol] at hxh
    · simpa [horizontal, hrightCol] using hxh
  have hxvOpposite : bottom xVertical ≤ top xVertical + epsilon := by
    by_cases htopRow : xVertical.2 = Fin.last m
    · have hxEq : xVertical = (xVertical.1, Fin.last m) :=
        Prod.ext rfl htopRow
      rw [hxEq]
      exact htop xVertical.1
    · have hnot : ¬top xVertical ≤ bottom xVertical + epsilon := by
        simpa [vertical, htopRow] using hxvFalse
      linarith
  have hxhOpposite : left xHorizontal ≤ right xHorizontal + epsilon := by
    by_cases hrightCol : xHorizontal.1 = Fin.last n
    · have hxEq : xHorizontal = (Fin.last n, xHorizontal.2) :=
        Prod.ext hrightCol rfl
      rw [hxEq]
      exact hright xHorizontal.2
    · have hnot : ¬right xHorizontal ≤ left xHorizontal + epsilon := by
        simpa [horizontal, hrightCol] using hxhFalse
      linarith
  exact ⟨x, xVertical, xHorizontal, hxv', hxh', hxVertical,
    hxvOpposite, hxHorizontal, hxhOpposite⟩


end StatMech.FK.PeriodicPlanar
