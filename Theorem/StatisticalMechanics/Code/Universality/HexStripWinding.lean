/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripWinding.lean -/

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
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexW1HeadingWindow.Part4
import Def.StatisticalMechanics.Code.Universality.HexStripWinding


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


@[simp] theorem hexStripWinding_runningHead_zero (h0 : ℤ) (ts : List ℤ) :
    hexStripWinding_runningHead h0 ts 0 = h0 := by
  unfold hexStripWinding_runningHead; simp


@[simp] theorem hexStripWinding_runningHead_length (h0 : ℤ) (ts : List ℤ) :
    hexStripWinding_runningHead h0 ts ts.length = hexInfra_headAccum h0 ts := by
  unfold hexStripWinding_runningHead
  rw [hexInfra_headAccum_eq_add_sum, List.take_length]


theorem hexStripWinding_runningHead_succ (h0 : ℤ) (ts : List ℤ) (k : ℕ) (hk : k < ts.length) :
    hexStripWinding_runningHead h0 ts (k + 1)
      = hexStripWinding_runningHead h0 ts k + ts[k] := by
  unfold hexStripWinding_runningHead
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.sum_append]
  simp only [List.sum_cons, List.sum_nil, add_zero, Option.toList_some]
  ring


theorem hexStripWinding_headAccum_sub (h0 H : ℤ) (ts : List ℤ) :
    hexInfra_headAccum h0 ts - H = ts.sum - (H - h0) := by
  rw [hexInfra_headAccum_eq_add_sum]; ring


end StatMech.Universality
