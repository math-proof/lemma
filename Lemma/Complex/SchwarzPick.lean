import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.SchwarzPick

open Complex.SchwarzPick

/--
[schwarzPick](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/SchwarzPick.lean)
-/
@[path]
private lemma schwarzPick_eq
-- given
  {f : ℂ → ℂ}
  (hf_diff : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
  (hf_maps : Set.MapsTo f (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1)) :
-- imply
  ∀ z ∈ Metric.ball (0 : ℂ) 1, ∀ w ∈ Metric.ball (0 : ℂ) 1,
    ‖(f z - f w) / (1 - star (f w) * f z)‖ ≤ ‖(z - w) / (1 - star w * z)‖ := by
-- proof
  apply schwarzPick hf_diff hf_maps


-- created on 2026-10-09
