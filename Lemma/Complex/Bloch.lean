import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.Bloch

open Complex.BlochWanted

/--
[bloch](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Bloch.lean)
-/
@[path]
private lemma bloch_eq :
-- imply
  ∃ B : ℝ, 0 < B ∧
    ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) → deriv f 0 = 1 →
      ∃ V : Set ℂ, ∃ w : ℂ,
        IsOpen V ∧ V ⊆ Metric.ball (0 : ℂ) 1 ∧ IsConnected V ∧
          Set.InjOn f V ∧ f '' V = Metric.ball w B := by
-- proof
  apply bloch


-- created on 2026-10-09
