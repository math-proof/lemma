/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexParityBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexCounterexample.Part2
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge
open Finset


namespace StatMech.Sharpness

theorem shb_evenCurrentSeries_eq_cosh (x : ℝ) :
    shbEvenCurrentSeries x = Real.cosh x := by
  unfold shbEvenCurrentSeries
  exact (Real.cosh_eq_tsum x).symm

theorem shb_oddCurrentSeries_eq_sinh (x : ℝ) :
    shbOddCurrentSeries x = Real.sinh x := by
  unfold shbOddCurrentSeries
  exact (Real.sinh_eq_tsum x).symm


end StatMech.Sharpness
