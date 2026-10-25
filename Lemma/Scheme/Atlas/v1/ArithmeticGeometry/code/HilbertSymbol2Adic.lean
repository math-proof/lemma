import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol2Adic
open PadicInt HilbertSymbol


/--
[hasPrimSolMod8_one_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol2Adic.lean)
-/
@[path]
lemma hasPrimSolMod8_one_eq
  {u v : ℤ_[2]ˣ} :
-- imply
  HasPrimitiveSolutionMod8_one u v ↔ hasPrimSolMod8_one_dec (toZModPow_unit 3 u) (toZModPow_unit 3 v) := by
-- proof
  simp only [HasPrimitiveSolutionMod8_one, hasPrimSolMod8_one_dec, toZModPow_unit_coe]

/--
[hasPrimSolMod8_two_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol2Adic.lean)
-/
@[path]
lemma hasPrimSolMod8_two_eq
  {u v : ℤ_[2]ˣ} :
-- imply
  HasPrimitiveSolutionMod8_two u v ↔ hasPrimSolMod8_two_dec (toZModPow_unit 3 u) (toZModPow_unit 3 v) := by
-- proof
  simp only [HasPrimitiveSolutionMod8_two, hasPrimSolMod8_two_dec, toZModPow_unit_coe]

/--
[hilbert_eq_formula_of_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol2Adic.lean)
-/
@[path]
lemma hilbert_eq_formula_of_iff
  {a b : ℚ_[2]ˣ}
  {solMod : Prop}
  [Decidable solMod]
  {f : ℤ}
-- given
  (h_iff : padicHilbertSymbol 2 a b = 1 ↔ HasPrimitiveSolution a b)
  (h_lift : HasPrimitiveSolution a b ↔ solMod)
  (hf : f = 1 ∨ f = -1)
  (h_formula : solMod ↔ f = 1) :
-- imply
  padicHilbertSymbol 2 a b = f := by
-- proof
  obtain h | h := padicHilbertSymbol.eq_one_or_neg_one a b
  · rw [h]
    obtain hf1 | hf1 := hf
    · exact hf1.symm
    · exfalso
      have hsol : solMod := h_lift.mp (h_iff.mp h)
      rw [h_formula.mp hsol] at hf1; exact absurd hf1 (by omega)
  · rw [h]
    obtain hf1 | hf1 := hf
    · exfalso
      have hf1' : f = 1 := hf1
      rw [← h_formula] at hf1'
      have := h_lift.mpr hf1'
      rw [← h_iff] at this
      rw [this] at h; exact absurd h (by omega)
    · exact hf1.symm

/--
[twoQp_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol2Adic.lean)
-/
@[path]
lemma twoQp_val
-- imply
  (twoQp : ℚ_[2]) = 2 :=
-- proof
  IsUnit.unit_spec _

/--
[padicUnit_two_eq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol2Adic.lean)
-/
@[path]
lemma padicUnit_two_eq_mul
  {v : ℤ_[2]ˣ} :
-- imply
  padicUnit_two v = twoQp * padicUnit_one v := by
-- proof
  ext
  simp only [padicUnit_two_val, twoQp_val, padicUnit_one_val, Units.val_mul]

/--
[padicUnit_two_eq_mul'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol2Adic.lean)
-/
@[path]
lemma padicUnit_two_eq_mul'
  {u : ℤ_[2]ˣ} :
-- imply
  padicUnit_two u = padicUnit_one u * twoQp := by
-- proof
  ext
  simp only [padicUnit_two_val, twoQp_val, padicUnit_one_val, Units.val_mul, mul_comm]

/--
[twoQp_eq_padicUnit_two_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol2Adic.lean)
-/
@[path]
lemma twoQp_eq_padicUnit_two_one
-- imply
  twoQp = padicUnit_two 1 := by
-- proof
  ext
  simp only [twoQp_val, padicUnit_two_val, Units.val_one]
  push_cast
  ring

/--
[neg_one_eq_padicUnit_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol2Adic.lean)
-/
@[path]
lemma neg_one_eq_padicUnit_one
-- imply
  (-1 : ℚ_[2]ˣ) = padicUnit_one (-1 : ℤ_[2]ˣ) := by
-- proof
  ext
  simp only [padicUnit_one_val, Units.val_neg, Units.val_one]
  push_cast
  ring

/--
[toZModPow_unit_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol2Adic.lean)
-/
@[path]
lemma toZModPow_unit_one
-- imply
  toZModPow_unit 3 (1 : ℤ_[2]ˣ) = 1 := by
-- proof
  ext
  simp only [toZModPow_unit_coe, Units.val_one, map_one]

/--
[toZModPow_unit_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol2Adic.lean)
-/
@[path]
lemma toZModPow_unit_neg_one
-- imply
  toZModPow_unit 3 (-1 : ℤ_[2]ˣ) = -1 := by
-- proof
  ext
  simp only [toZModPow_unit_coe, Units.val_neg, Units.val_one, map_neg, map_one]

/--
[thm_10_9_one_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol2Adic.lean)
-/
@[path]
lemma thm_10_9_one_one
  {u v : ℤ_[2]ˣ} :
-- imply
  padicHilbertSymbol 2 (padicUnit_one u) (padicUnit_one v) = hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v) 0 0 := by
-- proof
  exact hilbert_eq_formula_of_iff
    (hilbert_eq_one_iff_hasPrimitiveSolution (padicUnit_one u) (padicUnit_one v))
    ((lemma_10_8_one u v).trans (hasPrimSolMod8_one_eq u v))
    (formula_eq_one_or_neg_one _ _ 0 0)
    (formula_one_one_verified _ _)

/--
[thm_10_9_two_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol2Adic.lean)
-/
@[path]
lemma thm_10_9_two_one
  {u v : ℤ_[2]ˣ} :
-- imply
  padicHilbertSymbol 2 (padicUnit_two u) (padicUnit_one v) = hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v) 1 0 := by
-- proof
  exact hilbert_eq_formula_of_iff
    (hilbert_eq_one_iff_hasPrimitiveSolution (padicUnit_two u) (padicUnit_one v))
    ((lemma_10_8_two u v).trans (hasPrimSolMod8_two_eq u v))
    (formula_eq_one_or_neg_one _ _ 1 0)
    (formula_two_one_verified _ _)

/--
[thm_10_9_one_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol2Adic.lean)
-/
@[path]
lemma thm_10_9_one_two
  {u v : ℤ_[2]ˣ} :
-- imply
  padicHilbertSymbol 2 (padicUnit_one u) (padicUnit_two v) = hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v) 0 1 := by
-- proof
  rw [show padicHilbertSymbol 2 (padicUnit_one u) (padicUnit_two v) =
    padicHilbertSymbol 2 (padicUnit_two v) (padicUnit_one u) from
    hilbertSymbol.symm _ _]
  exact hilbert_eq_formula_of_iff
    (hilbert_eq_one_iff_hasPrimitiveSolution (padicUnit_two v) (padicUnit_one u))
    ((lemma_10_8_two v u).trans (hasPrimSolMod8_two_eq v u))
    (formula_eq_one_or_neg_one _ _ 0 1)
    (formula_one_two_verified _ _)

/--
[thm_10_9_two_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol2Adic.lean)
-/
@[path]
lemma thm_10_9_two_two
  {u v : ℤ_[2]ˣ} :
-- imply
  padicHilbertSymbol 2 (padicUnit_two u) (padicUnit_two v) = hilbert2Adic_formula (toZModPow_unit 3 u) (toZModPow_unit 3 v) 1 1 := by
-- proof
  have h1 : padicHilbertSymbol 2 (padicUnit_two u) (padicUnit_two v) =
    padicHilbertSymbol 2 (padicUnit_two u) twoQp *
    padicHilbertSymbol 2 (padicUnit_two u) (padicUnit_one v) := by
    simp only [padicHilbertSymbol]
    rw [padicUnit_two_eq_mul v, hilbertSymbol.mul_right]
  have h2 : padicHilbertSymbol 2 (padicUnit_two u) twoQp =
    padicHilbertSymbol 2 (padicUnit_one u) twoQp *
    padicHilbertSymbol 2 twoQp twoQp := by
    simp only [padicHilbertSymbol]
    rw [padicUnit_two_eq_mul' u, hilbertSymbol.mul_left]
  have h3 : padicHilbertSymbol 2 (padicUnit_one u) twoQp =
    padicHilbertSymbol 2 twoQp (padicUnit_one u) :=
    hilbertSymbol.symm _ _
  have h4 : padicHilbertSymbol 2 twoQp twoQp =
    hilbertSymbol ℚ_[2] (-1) twoQp :=
    hilbertSymbol.hilbert_self_eq_neg_one twoQp
  have h5 : padicHilbertSymbol 2 twoQp (padicUnit_one u) =
    hilbert2Adic_formula (toZModPow_unit 3 (1 : ℤ_[2]ˣ)) (toZModPow_unit 3 u) 1 0 := by
    rw [twoQp_eq_padicUnit_two_one]
    exact thm_10_9_two_one 1 u
  have h6 : hilbertSymbol ℚ_[2] (-1) twoQp =
    hilbert2Adic_formula (toZModPow_unit 3 (-1 : ℤ_[2]ˣ)) (toZModPow_unit 3 (1 : ℤ_[2]ˣ)) 0 1 := by
    rw [neg_one_eq_padicUnit_one, twoQp_eq_padicUnit_two_one]
    exact thm_10_9_one_two (-1) 1
  have h7 := thm_10_9_two_one u v
  rw [h1, h2, h3, h4, h5, h6, h7]
  rw [toZModPow_unit_one, toZModPow_unit_neg_one]
  exact (formula_bilinear_identity _ _).symm


-- created on 2026-10-23
