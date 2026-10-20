import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.ODE.ExplicitEuler
open MathlibExt.Analysis.ODE.ExplicitEulerWanted


/--
[_root_.ODE.exists_explicitEuler_localTruncationError_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/ExplicitEuler.lean)
-/
@[path]
private lemma ODE_exists_explicitEuler_localTruncationError_le_eq
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E → E}
  {t₀ T : ℝ}
  {x : ℝ → E}
-- given
  (hT : t₀ < T)
  (hf : ContDiff ℝ 2 (Function.uncurry f))
  (hx : ∀ t ∈ Set.Icc t₀ T, HasDerivAt x (f t (x t)) t) :
-- imply
  ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ Set.Ioc 0 (T - t₀),
    ∀ t ∈ Set.Icc t₀ T, t + h ≤ T →
    ‖x (t + h) - (x t + h • f t (x t))‖ ≤ C * h ^ 2 := by
-- proof
  apply ODE.exists_explicitEuler_localTruncationError_le f t₀ T hT hf x hx

/--
[explicit_euler_first_order_convergence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/ExplicitEuler.lean)
-/
@[path]
private lemma explicit_euler_first_order_convergence_eq
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E}
  {t₀ T : ℝ}
  {x₀ : E}
  {L : NNReal}
-- given
  (hT : t₀ < T)
  (hf : ContDiff ℝ 2 (Function.uncurry f))
  (hlip : ∀ t ∈ Set.Icc t₀ T, LipschitzWith L (f t)) :
-- imply
  ∃ x : ℝ → E, x t₀ = x₀ ∧ (∀ t ∈ Set.Icc t₀ T, HasDerivAt x (f t (x t)) t) ∧
    ∃ C : ℝ, ∀ h ∈ Set.Ioc 0 (T - t₀), ∀ X : ℕ → E, X 0 = x₀ →
    (∀ n, X (n + 1) = X n + h • f (t₀ + (n : ℝ) * h) (X n)) →
    ∀ n : ℕ, (n : ℝ) * h ≤ T - t₀ →
    ‖X n - x (t₀ + (n : ℝ) * h)‖ ≤ C * h := by
-- proof
  apply MathlibExt.Analysis.ODE.ExplicitEulerWanted.explicit_euler_first_order_convergence f t₀ T x₀ L hT hf hlip

/--
[explicit_euler_local_truncation_error](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/ExplicitEuler.lean)
-/
@[path]
private lemma explicit_euler_local_truncation_error_eq
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E → E}
  {t₀ T : ℝ}
  {x₀ : E}
  {x : ℝ → E}
-- given
  (hT : t₀ < T)
  (hf : ContDiff ℝ 2 (Function.uncurry f))
  (hx0 : x t₀ = x₀)
  (hx : ∀ t ∈ Set.Icc t₀ T, HasDerivAt x (f t (x t)) t) :
-- imply
  ∃ C : ℝ, ∀ h ∈ Set.Ioc 0 (T - t₀), ∀ t ∈ Set.Icc t₀ T, t + h ≤ T →
    ‖x (t + h) - (x t + h • f t (x t))‖ ≤ C * h ^ 2 := by
-- proof
  apply MathlibExt.Analysis.ODE.ExplicitEulerWanted.explicit_euler_local_truncation_error f t₀ T x₀ hT hf x hx0 hx


-- created on 2026-10-20
