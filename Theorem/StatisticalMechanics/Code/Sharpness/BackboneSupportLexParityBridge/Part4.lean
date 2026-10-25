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
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part4
open Finset


namespace StatMech.Sharpness

theorem shbK4DirectFiberMass_cast (E : Finset shbK4Edge) (t : ℚ) :
    (shbK4DirectFiberMass E t : ℝ) = shbK4DirectFiberPolynomial E t := by
  unfold shbK4DirectFiberMass shbK4DirectFiberPolynomial
  push_cast
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : shbK4SelectsDirect03 A <;> simp [h]

theorem shbK4VacuumMass_cast (E : Finset shbK4Edge) (t : ℚ) :
    (shbK4VacuumMass E t : ℝ) = shbK4VacuumPolynomial E t := by
  unfold shbK4VacuumMass shbK4VacuumPolynomial
  push_cast
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : shbK4Boundary A = ∅ <;> simp [h]


end StatMech.Sharpness
