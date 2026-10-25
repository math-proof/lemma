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
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part4
open Finset


namespace StatMech.Sharpness

noncomputable def shbK4DirectRhoPolynomial (E : Finset shbK4Edge) (t : ℝ) : ℝ :=
  shbK4DirectFiberPolynomial E t / shbK4VacuumPolynomial E t

end StatMech.Sharpness
