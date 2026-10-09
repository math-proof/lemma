import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.Wiman

open Complex.Wiman

/--
[wimanTerm_abs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman.lean)
-/
@[path]
private lemma wiman_term_abs_eq
-- given
  (f : ℂ → ℂ)
  (r : ℝ)
  (n : ℕ) :
-- imply
  wimanTerm f |r| n = wimanTerm f r n := by
-- proof
  apply wimanTerm_abs f r n


/--
[wimanMaximumTerm_abs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman.lean)
-/
@[path]
private lemma wiman_maximum_term_abs_eq
-- given
  (f : ℂ → ℂ)
  (r : ℝ) :
-- imply
  wimanMaximumTerm f |r| = wimanMaximumTerm f r := by
-- proof
  apply wimanMaximumTerm_abs f r


/--
[wimanMaximumModulus_abs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman.lean)
-/
@[path]
private lemma wiman_maximum_modulus_abs_eq
-- given
  (f : ℂ → ℂ)
  (r : ℝ) :
-- imply
  wimanMaximumModulus f |r| = wimanMaximumModulus f r := by
-- proof
  apply wimanMaximumModulus_abs f r


/--
[wimanTerm_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman.lean)
-/
@[path]
private lemma wiman_term_neg_eq
-- given
  (f : ℂ → ℂ)
  (r : ℝ)
  (n : ℕ) :
-- imply
  wimanTerm f (-r) n = wimanTerm f r n := by
-- proof
  apply wimanTerm_neg f r n


/--
[wimanMaximumTerm_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman.lean)
-/
@[path]
private lemma wiman_maximum_term_neg_eq
-- given
  (f : ℂ → ℂ)
  (r : ℝ) :
-- imply
  wimanMaximumTerm f (-r) = wimanMaximumTerm f r := by
-- proof
  apply wimanMaximumTerm_neg f r


/--
[wimanMaximumModulus_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman.lean)
-/
@[path]
private lemma wiman_maximum_modulus_neg_eq
-- given
  (f : ℂ → ℂ)
  (r : ℝ) :
-- imply
  wimanMaximumModulus f (-r) = wimanMaximumModulus f r := by
-- proof
  apply wimanMaximumModulus_neg f r


/--
[norm_le_wimanMaximumModulus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman.lean)
-/
@[path]
private lemma norm_le_wiman_maximum_modulus_eq
-- given
  {f : ℂ → ℂ}
  {r : ℝ}
  {z : ℂ}
  (hf : Continuous f)
  (hz : ‖z‖ = r) :
-- imply
  ‖f z‖ ≤ wimanMaximumModulus f r := by
-- proof
  apply norm_le_wimanMaximumModulus hf hz


/--
[cube_le_cube_mul_log_sq_of_wiman](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman.lean)
-/
@[path]
private lemma cube_le_cube_mul_log_sq_of_wiman_eq
-- given
  {M μ : ℝ}
  (hM : 0 ≤ M)
  (hμ : 0 ≤ μ)
  (hlog : 0 ≤ Real.log μ)
  (hWiman : M ≤ μ * Real.log μ ^ (2 / 3 : ℝ)) :
-- imply
  M ^ 3 ≤ μ ^ 3 * Real.log μ ^ 2 := by
-- proof
  apply cube_le_cube_mul_log_sq_of_wiman hM hμ hlog hWiman


-- created on 2026-10-10
