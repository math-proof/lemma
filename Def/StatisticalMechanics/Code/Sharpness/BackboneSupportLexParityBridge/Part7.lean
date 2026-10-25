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
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part6
open Finset


namespace StatMech.Sharpness

noncomputable def shbK4DirectRhoSeries
    (E : Finset shbK4Edge) (x : ℝ) : ℝ :=
  shbK4DirectFiberSeriesMass E x / shbK4VacuumSeriesMass E x


end StatMech.Sharpness
