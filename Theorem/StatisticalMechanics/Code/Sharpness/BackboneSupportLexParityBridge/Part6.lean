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
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part6
open Finset


namespace StatMech.Sharpness

theorem shbK4DirectFiberSeriesMass_eq (E : Finset shbK4Edge) (x : ℝ) :
    shbK4DirectFiberSeriesMass E x =
      Real.cosh x ^ E.card * shbK4DirectFiberPolynomial E (Real.tanh x) := by
  exact shb_paritySeriesMassOn_eq_cosh_mul_polynomial
    E shbK4SelectsDirect03 x

theorem shbK4VacuumSeriesMass_eq (E : Finset shbK4Edge) (x : ℝ) :
    shbK4VacuumSeriesMass E x =
      Real.cosh x ^ E.card * shbK4VacuumPolynomial E (Real.tanh x) := by
  exact shb_paritySeriesMassOn_eq_cosh_mul_polynomial
    E (fun A ↦ shbK4Boundary A = ∅) x


end StatMech.Sharpness
