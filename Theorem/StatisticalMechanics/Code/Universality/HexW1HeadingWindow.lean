/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1HeadingWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexW1Sides.Part3


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexW1_heading_eq_of_dvd_six_of_bound (h0 : ℤ) (H : ℤ) (ts : List ℤ)
    (hdvd : (6 : ℤ) ∣ (hexInfra_headAccum h0 ts - H))
    (hbound : |hexInfra_headAccum h0 ts - H| < 6) :
    hexInfra_headAccum h0 ts = H := by
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at hbound
  rw [abs_lt] at hbound
  have hk0 : k = 0 := by omega
  omega


theorem hexW1_heading_window_of_eq (h0 : ℤ) (H w : ℤ) (ts : List ℤ)
    (heq : hexInfra_headAccum h0 ts = H) (hHL : w ≤ H) (hHU : H < w + 6) :
    w ≤ hexInfra_headAccum h0 ts ∧ hexInfra_headAccum h0 ts < w + 6 := by
  rw [heq]; exact ⟨hHL, hHU⟩


theorem hexW1_bound_does_not_force_eq (H : ℤ) :
    |(H + 3) - H| < 6 ∧ (H + 3) ≠ H := by
  refine ⟨?_, by omega⟩
  rw [show (H + 3) - H = 3 by ring]; decide


end StatMech.Universality
