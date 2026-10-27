import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.BooleanFunctions.code.FourierExpansion
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion


namespace BooleanFourier

/--
[fourierCoeff_eq_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierSampling.lean)
-/
@[path]
lemma fourierCoeff_eq_expectation
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {S : Finset (Fin n)} :
-- imply
  fourierCoeff f S = (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x * chi S x := by
-- proof
  rfl

end BooleanFourier

namespace BooleanFourier

/--
[abs_chi_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierSampling.lean)
-/
@[path]
lemma abs_chi_eq_one
  {n : ℕ}
  {S : Finset (Fin n)}
  {x : Fin n → Bool} :
-- imply
  |chi S x| = 1 := by
-- proof
  have h := chi_sq (S := S) (x := x)
  have hne := chi_ne_zero (S := S) (x := x)
  have habs_sq : |chi S x| ^ 2 = 1 := by
    rw [sq_abs]; exact h
  have habs_nn : (0 : ℝ) ≤ |chi S x| := abs_nonneg _
  nlinarith [sq_nonneg (|chi S x| - 1)]

end BooleanFourier

namespace BooleanFourier

/--
[sample_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierSampling.lean)
-/
@[path]
lemma sample_bounded
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {S : Finset (Fin n)}
  {x : Fin n → Bool}
-- given
  (hf : ∀ x, |f x| ≤ 1) :
-- imply
  |f x * chi S x| ≤ 1 := by
-- proof
  rw [abs_mul, abs_chi_eq_one (S := S) (x := x), mul_one]
  exact hf x

end BooleanFourier


-- created on 2026-10-23
-- updated on 2026-10-27
