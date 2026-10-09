import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.Rouche

open Complex.Rouche

/--
[rouche_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Rouche.lean)
-/
@[path]
private lemma rouche_closedBall_eq
-- given
  {c : ℂ} {R : ℝ} (hR : 0 < R)
  {f g : ℂ → ℂ}
  (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
  (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
  (hfg : ∀ z ∈ Metric.sphere c R, ‖g z‖ < ‖f z‖) :
-- imply
  (finsum fun z => MeromorphicOn.divisor f (Metric.ball c R) z) =
    finsum fun z => MeromorphicOn.divisor (fun z => f z + g z) (Metric.ball c R) z := by
-- proof
  apply rouche_closedBall hR hf hg hfg


-- created on 2026-10-09
