/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertPrimitiveSolutions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertSymbol
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertFormulaOdd
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Hilbert2Adic
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Hilbert2AdicCore
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.HilbertFormulaOdd
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Hilbert2Adic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Hilbert2AdicCore
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

open scoped Classical

/-- A characteristic-zero field on which the Hilbert symbol is bilinear and nondegenerate.
The two structural axioms encode: (i) if both $(a,c)_F$ and $(b,c)_F$ equal $-1$ then
$(ab,c)_F = 1$ (used to derive bilinearity); (ii) for every non-square unit $c$ there
exists $b$ with $(b,c)_F = -1$ (nondegeneracy of the Hilbert pairing). -/
class HilbertBilinearField (F : Type*) [Field F] extends CharZero F where
  isSolvable_mul_of_both_neg : ∀ (a b c : Fˣ),
    hilbertSymbol F a c = -1 → hilbertSymbol F b c = -1 →
    hilbertSymbol F (a * b) c = 1
  nondegenerate : ∀ (c : Fˣ), ¬ IsSquare (c : F) →
    ∃ b : Fˣ, hilbertSymbol F b c = -1

section PadicBilinearHelpers

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

open HilbertSymbol

/-- Decidability of `hasPrimSolMod8_one_loc` via finite search over `ZMod 8`. -/
instance (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Decidable (hasPrimSolMod8_one_loc u₀ v₀) :=
  Fintype.decidableExistsFintype
/-- Decidability of `hasPrimSolMod8_two_loc` via finite search over `ZMod 8`. -/
instance (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Decidable (hasPrimSolMod8_two_loc u₀ v₀) :=
  Fintype.decidableExistsFintype


/-- Decidable witness predicate for $2$-adic nondegeneracy: a unit $w_0 \in (\mathbb{Z}/8)^\times$
has either a unit $v_0$ with $z^2 = v_0 x^2 + w_0 y^2$ insolvable mod $8$, or a unit $v_0$
with $z^2 = 2v_0 x^2 + w_0 y^2$ insolvable mod $8$. -/
@[reducible] def nondeg_unit_combined (w₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  (∃ (v₀ : (ZMod (2 ^ 3))ˣ), ¬ hasPrimSolMod8_one_loc v₀ w₀) ∨
  (∃ (v₀ : (ZMod (2 ^ 3))ˣ), ¬ hasPrimSolMod8_two_loc v₀ w₀)

/-- Decidability of `nondeg_unit_combined` from decidability of each disjunct. -/
instance (w₀ : (ZMod (2 ^ 3))ˣ) : Decidable (nondeg_unit_combined w₀) :=
  instDecidableOr

/-- Decidability of `nondeg_two_prop` via finite search over $(\mathbb{Z}/8)^\times$. -/
instance (w₀ : (ZMod (2 ^ 3))ˣ) : Decidable (nondeg_two_prop w₀) :=
  Fintype.decidableExistsFintype

/-- Reduction modulo $8$ of a $2$-adic unit, producing a unit of $\mathbb{Z}/8$. -/
noncomputable def toZMod8Unit (w : ℤ_[2]ˣ) : (ZMod (2 ^ 3))ˣ :=
  ((PadicInt.isUnit_toZModPow_iff (show 0 < 3 from by omega)).mpr w.isUnit).unit

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

namespace hilbertSymbol

variable {F : Type*} [Field F]

/-- Wrapper exposing `HilbertBilinearField.isSolvable_mul_of_both_neg` in the
`hilbertSymbol` namespace. -/
theorem isSolvable_mul_of_both_neg [HilbertBilinearField F]
    (a b c : Fˣ)
    (ha : hilbertSymbol F a c = -1) (hb : hilbertSymbol F b c = -1) :
    hilbertSymbol F (a * b) c = 1 :=
  HilbertBilinearField.isSolvable_mul_of_both_neg a b c ha hb

/-- Nondegeneracy axiom of `HilbertBilinearField`, exposed in the `hilbertSymbol` namespace:
every non-square unit pairs to $-1$ with some element. -/
theorem nondegenerate [HilbertBilinearField F] (c : Fˣ) (hc : ¬ IsSquare (c : F)) :
    ∃ b : Fˣ, hilbertSymbol F b c = -1 :=
  HilbertBilinearField.nondegenerate c hc

end hilbertSymbol
