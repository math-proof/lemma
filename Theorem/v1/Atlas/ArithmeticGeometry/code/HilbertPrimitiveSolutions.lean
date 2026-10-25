/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertSymbol
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertFormulaOdd
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Hilbert2Adic
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Hilbert2AdicCore
import Def.v1.Atlas.ArithmeticGeometry.code.HilbertFormulaOdd
import Def.v1.Atlas.ArithmeticGeometry.code.Hilbert2Adic
import Def.v1.Atlas.ArithmeticGeometry.code.Hilbert2AdicCore.Part2
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions.Part2
open scoped Classical


section PadicBilinearHelpers

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

open HilbertSymbol

/-- The $p$-adic field $\mathbb{Q}_p$ is a `HilbertBilinearField`: the Hilbert symbol
$(-,-)_{\mathbb{Q}_p}$ is bilinear and nondegenerate. -/
lemma real_unit_not_square_neg (c : ℝˣ) (hc : ¬ IsSquare (c : ℝ)) : (c : ℝ) < 0 := by
  by_contra h
  push Not at h
  apply hc
  have hpos : 0 < (c : ℝ) := lt_of_le_of_ne h (Ne.symm c.ne_zero)
  exact ⟨Real.sqrt c, by rw [← sq, Real.sq_sqrt hpos.le]⟩

/-- If $a > 0$ is real, then $z^2 = a x^2 + b y^2$ is solvable with $(x, y, z) = (1/\sqrt{a}, 0, 1)$,
so the real Hilbert symbol $(a, b)_{\mathbb{R}} = 1$ for any $b$. -/
lemma real_pos_isSolvable (a : ℝˣ) (ha : 0 < (a : ℝ)) (b : ℝˣ) :
    HilbertSymbol.IsSolvable ℝ a b := by
  refine ⟨1 / Real.sqrt a, 0, ?_⟩
  simp only [mul_zero, sq (0 : ℝ), add_zero]
  rw [div_pow, one_pow, Real.sq_sqrt ha.le]
  field_simp

/-- If $(a, c)_{\mathbb{R}} = -1$ then $a < 0$ (contrapositive of `real_pos_isSolvable`). -/
lemma real_hilbert_neg_one_imp_neg_left (a c : ℝˣ)
    (h : hilbertSymbol ℝ a c = -1) : (a : ℝ) < 0 := by
  by_contra ha
  push Not at ha
  have hpos : 0 < (a : ℝ) := lt_of_le_of_ne ha (Ne.symm a.ne_zero)
  rw [hilbertSymbol.eq_neg_one_iff] at h
  exact h (real_pos_isSolvable a hpos c)

end PadicBilinearHelpers
