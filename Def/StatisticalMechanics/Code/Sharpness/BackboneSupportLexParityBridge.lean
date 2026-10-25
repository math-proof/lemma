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
open Finset


namespace StatMech.Sharpness

noncomputable def shbEvenCurrentSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ, x ^ (2 * k) / (2 * k).factorial


noncomputable def shbOddCurrentSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ, x ^ (2 * k + 1) / (2 * k + 1).factorial

end StatMech.Sharpness
