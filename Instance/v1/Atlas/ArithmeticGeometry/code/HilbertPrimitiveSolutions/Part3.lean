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
import Theorem.v1.Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions
open scoped Classical


section PadicBilinearHelpers

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

open HilbertSymbol

/-- The real field $\mathbb{R}$ is a `HilbertBilinearField`: bilinearity holds because two
negative reals multiply to a positive one, and nondegeneracy holds because $-1$ pairs nontrivially
with itself. -/
noncomputable instance instHilbertBilinearFieldReal : HilbertBilinearField ℝ where
  isSolvable_mul_of_both_neg := by
    intro a b c ha hb
    have ha_neg : (a : ℝ) < 0 := real_hilbert_neg_one_imp_neg_left a c ha
    have hb_neg : (b : ℝ) < 0 := real_hilbert_neg_one_imp_neg_left b c hb
    have hab_pos : 0 < ((a * b : ℝˣ) : ℝ) := by
      simp only [Units.val_mul]
      exact mul_pos_of_neg_of_neg ha_neg hb_neg
    rw [hilbertSymbol.eq_one_iff]
    exact real_pos_isSolvable (a * b) hab_pos c
  nondegenerate := by
    intro c hc
    have hc_neg : (c : ℝ) < 0 := real_unit_not_square_neg c hc
    refine ⟨c, ?_⟩
    rw [hilbertSymbol.eq_neg_one_iff]
    rintro ⟨x, y, h⟩
    have h1 : (c : ℝ) * x ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc_neg.le (sq_nonneg x)
    have h2 : (c : ℝ) * y ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc_neg.le (sq_nonneg y)
    linarith

end PadicBilinearHelpers
