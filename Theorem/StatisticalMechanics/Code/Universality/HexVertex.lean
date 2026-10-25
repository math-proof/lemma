/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace StatMech.Universality

open Complex


theorem hexExpI_mul (a b : ℝ) :
    Complex.exp ((a : ℂ) * Complex.I) * Complex.exp ((b : ℂ) * Complex.I)
      = Complex.exp (((a + b : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring


theorem hexExpI_zpow (a : ℝ) (k : ℤ) :
    (Complex.exp ((a : ℂ) * Complex.I)) ^ k
      = Complex.exp ((((k : ℝ) * a : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_int_mul]; congr 1; push_cast; ring


theorem hexExpI_add_neg (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)
      = 2 * (Real.cos θ : ℂ) := by
  rw [show ((-θ : ℝ) : ℂ) = -(θ : ℂ) by push_cast; ring,
      ← Complex.two_cos, Complex.ofReal_cos]


end StatMech.Universality
