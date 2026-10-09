import Mathlib
import sympy.Basic
import sympy.Analysis.Calculus.ArcsinDivSinIntegral

/--
[arcsin_div_sin_integral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/ArcsinDivSinIntegral.lean)
-/
@[path]
private lemma arcsin_div_sin_integral_eq
-- given
  :
-- imply
  (∫ x in (0 : ℝ)..(Real.pi / 2), Real.arcsin
    ((Real.sin x) ^ 2) / Real.sin x) = -2 * tsum
  (fun n : ℕ => (-1 : ℝ) ^ n / ((2 * (n : ℝ) + 1) ^ 2)) - Real.pi ^ 2 / (2 * Real.sqrt 2) + 1 /
  (8 * Real.sqrt 2) *
  (tsum (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + (1 / 8 : ℝ)) ^ 2)) + tsum
  (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + (3 / 8 : ℝ)) ^ 2))) :=
-- proof
  Real.Calculus.ArcsinDivSinIntegral.arcsin_div_sin_integral


-- created on 2026-10-09
