import Mathlib
import Initialize.Tactic.Attr.Basic
open Complex Real
open scoped FourierTransform


/--
[gaussian_fourier_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GammaFunction.lean)
-/
@[path]
lemma gaussian_fourier_self :
-- imply
  (𝓕 fun (x : ℝ) ↦ cexp (-(π : ℂ) * (x : ℂ) ^ 2)) = fun (y : ℝ) ↦ cexp (-(π : ℂ) * (y : ℂ) ^ 2) := by
-- proof
  have := fourier_gaussian_pi (b := 1) (by simp : (0 : ℝ) < (1 : ℂ).re)
  simp only [mul_one, div_one, one_cpow, one_div, one_mul] at this
  exact this


-- created on 2026-10-23
-- updated on 2026-10-28
