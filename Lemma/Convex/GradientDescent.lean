import Mathlib
import sympy.Basic
import sympy.Analysis.Convex.GradientDescent

open Convex.GradientDescent

/-- [gradient_descent_convex_sublinear_rate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/GradientDescent.lean) -/
@[path]
private lemma gradient_descent_convex_sublinear_rate_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {f : E → ℝ} {L : ℝ} (hL : 0 < L)
  (hconvex : ConvexOn ℝ Set.univ f)
  (hdiff : Differentiable ℝ f)
  (hsmooth : LipschitzWith ⟨L, le_of_lt hL⟩ (gradient f))
  {xstar : E} (hmin : ∀ x, f xstar ≤ f x)
  {η : ℝ} (hη : η ∈ Set.Ioc 0 (1 / L))
  {X : ℕ → E} (hX : ∀ k, X (k + 1) = X k - η • gradient f (X k)) :
-- imply
  ∀ k : ℕ, 0 < k →
    f (X k) - f xstar ≤ ‖X 0 - xstar‖ ^ 2 / (2 * η * (k : ℝ)) := by
-- proof
  apply gradient_descent_convex_sublinear_rate hL hconvex hdiff hsmooth hmin hη hX

-- created on 2026-10-10
