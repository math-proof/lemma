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
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part5
open Finset


namespace StatMech.Sharpness

theorem shbK4DirectRho_cast (E : Finset shbK4Edge) (t : ℚ) :
    (shbK4DirectRho E t : ℝ) = shbK4DirectRhoPolynomial E t := by
  rw [shbK4DirectRho, shbK4DirectRhoPolynomial, Rat.cast_div,
    shbK4DirectFiberMass_cast, shbK4VacuumMass_cast]


theorem shb_supportLex_realParity_P3_counterexample :
    shbK4DirectRhoPolynomial shbK4H (2 / 3) <
      shbK4DirectRhoPolynomial shbK4G (2 / 3) := by
  have h := shb_supportLex_edgeDomain_P3_counterexample
  have hH := shbK4DirectRho_cast shbK4H (2 / 3)
  have hG := shbK4DirectRho_cast shbK4G (2 / 3)
  norm_num at hH hG
  rw [← hH, ← hG]
  exact_mod_cast h


theorem shb_tanh_artanh_two_thirds :
    Real.tanh (Real.artanh (2 / 3)) = (2 / 3 : ℝ) := by
  rw [Real.tanh_artanh]
  norm_num


end StatMech.Sharpness
