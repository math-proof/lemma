import Mathlib
import sympy.Basic
import Theorem.Analysis.Calculus.NewtonMethod
open Real.Calculus.NewtonMethod


/--
[newton_method_local_quadratic_convergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/NewtonMethod.lean)
-/
@[path]
private lemma newton_method_local_quadratic_convergence_eq
-- given
  {f : ℝ → ℝ} {c : ℝ}
  (hf : ContDiff ℝ 2 f) (hc : f c = 0) (hderiv : deriv f c ≠ 0) :
-- imply
  ∃ δ > 0, ∃ C : ℝ, ∀ x0 ∈ Set.Ioo (c - δ) (c + δ),
    ∀ X : ℕ → ℝ, X 0 = x0 →
      (∀ n, X (n + 1) = X n - f (X n) / deriv f (X n)) →
      (∀ n, X n ∈ Set.Ioo (c - δ) (c + δ)) ∧
      (∀ n, |X (n + 1) - c| ≤ C * |X n - c| ^ 2) ∧
      Filter.Tendsto X Filter.atTop (nhds c) := by
-- proof
  apply newton_method_local_quadratic_convergence hf hc hderiv

/--
[newton_step_sub_root_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/NewtonMethod.lean)
-/
@[path]
private lemma newton_step_sub_root_abs_le_eq
  {f : ℝ → ℝ} {c x m : ℝ} {K : NNReal}
-- given
  (hf : Differentiable ℝ f)
  (hc : f c = 0)
  (hm : 0 < m)
  (hK : LipschitzOnWith K (deriv f) (Set.uIcc c x))
  (hderiv : m ≤ |deriv f x|) :
-- imply
  |x - f x / deriv f x - c| ≤ ((K : ℝ) / m) * |x - c| ^ 2 := by
-- proof
  apply newton_step_sub_root_abs_le hf hc hm hK hderiv


-- created on 2026-10-09
-- updated on 2026-10-23
