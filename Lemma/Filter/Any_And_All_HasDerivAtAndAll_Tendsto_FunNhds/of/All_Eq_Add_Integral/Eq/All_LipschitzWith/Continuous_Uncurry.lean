import Mathlib
import sympy.Basic
import Theorem.Analysis.ODE.PicardIteration

/--
[PicardIteration](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/PicardIteration.lean)
-/
@[path]
private lemma picard_iterates_converge_eq
-- given
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (f : ℝ → E → E)
  (t₀ : ℝ)
  (x₀ : E)
  (L : NNReal)
  (u : ℕ → ℝ → E)
  (hfcont : Continuous (Function.uncurry f))
  (hlip : ∀ t, LipschitzWith L (f t))
  (hu0 : u 0 = fun _ => x₀)
  (hu : ∀ n t, u (n + 1) t = x₀ + ∫ s in t₀..t, f s (u n s)) :
-- imply
  ∃ x : ℝ → E, x t₀ = x₀ ∧ (∀ t, HasDerivAt x (f t (x t)) t) ∧
    ∀ t, Filter.Tendsto (fun n => u n t) Filter.atTop (nhds (x t)) := by
-- proof
  apply ODE.PicardIterationWanted.picard_iterates_converge f t₀ x₀ L hfcont hlip u hu0 hu

/--
[PicardIteration](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/PicardIteration.lean)
-/
@[path]
private lemma picard_iterates_tendsto_of_has_deriv_at_is
-- given
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (f : ℝ → E → E)
  (t₀ : ℝ)
  (x₀ : E)
  (L : NNReal)
  (u : ℕ → ℝ → E)
  (y : ℝ → E)
  (hfcont : Continuous (Function.uncurry f))
  (hlip : ∀ t, LipschitzWith L (f t))
  (hu0 : u 0 = fun _ => x₀)
  (hu : ∀ n t, u (n + 1) t = x₀ + ∫ s in t₀..t, f s (u n s))
  (hy₀ : y t₀ = x₀)
  (hy : ∀ t, HasDerivAt y (f t (y t)) t) :
-- imply
  ∀ t, Filter.Tendsto (fun n => u n t) Filter.atTop (nhds (y t)) := by
-- proof
  apply ODE.PicardIterationWanted.picard_iterates_tendsto_of_hasDerivAt
    f t₀ x₀ L hfcont hlip u hu0 hu y hy₀ hy

/--
[PicardIteration](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/ODE/PicardIteration.lean)
-/
@[path]
private lemma picard_iterates_step_estimate_le
-- given
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : ℝ → E → E)
  (t₀ : ℝ)
  (x₀ : E)
  (L : NNReal)
  (u : ℕ → ℝ → E)
  (M : ℝ)
  (hfcont : Continuous (Function.uncurry f))
  (hlip : ∀ t, LipschitzWith L (f t))
  (hu0 : u 0 = fun _ => x₀)
  (hu : ∀ n t, u (n + 1) t = x₀ + ∫ s in t₀..t, f s (u n s))
  (hM : ∀ s, ‖f s x₀‖ ≤ M) :
-- imply
  ∀ n t, ‖u (n + 1) t - u n t‖ ≤
    M * (L : ℝ) ^ n * |t - t₀| ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
-- proof
  apply ODE.PicardIterationWanted.picard_iterates_step_estimate f t₀ x₀ L hfcont hlip u hu0 hu M hM

-- created on 2026-10-10
