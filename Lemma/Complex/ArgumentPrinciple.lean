import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.ArgumentPrinciple

open Complex.ArgumentPrinciple

/--
[argumentPrinciple_closedBall_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/ArgumentPrinciple.lean)
-/
@[path]
private lemma argumentPrinciple_closedBall_general_eq
-- given
  {c : ℂ} {R : ℝ} (hR : 0 < R)
  {f : ℂ → ℂ}
  (hf : MeromorphicOn f (Metric.closedBall c R))
  (hf_top : ∀ z ∈ Metric.closedBall c R, meromorphicOrderAt f z ≠ ⊤)
  (hbd : ∀ z ∈ Metric.sphere c R,
    MeromorphicOn.divisor f (Metric.closedBall c R) z = 0) :
-- imply
  circleIntegral (logDeriv f) c R =
    2 * Real.pi * Complex.I * ↑(finsum fun z => MeromorphicOn.divisor f (Metric.ball c R) z) := by
-- proof
  apply argumentPrinciple_closedBall_general hR hf hf_top hbd


/--
[argumentPrinciple_closedBall](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/ArgumentPrinciple.lean)
-/
@[path]
private lemma argumentPrinciple_closedBall_eq
-- given
  {c : ℂ} {R : ℝ} (hR : 0 < R)
  {f : ℂ → ℂ}
  (hf : MeromorphicOn f (Metric.closedBall c R))
  (hf_top : ∀ z ∈ Metric.closedBall c R, meromorphicOrderAt f z ≠ ⊤)
  (hbd : ∀ z ∈ Metric.sphere c R,
    MeromorphicOn.divisor f (Metric.closedBall c R) z = 0)
  (hint : CircleIntegrable (logDeriv f) c R) :
-- imply
  circleIntegral (logDeriv f) c R =
    2 * Real.pi * Complex.I * ↑(finsum fun z => MeromorphicOn.divisor f (Metric.ball c R) z) := by
-- proof
  apply argumentPrinciple_closedBall hR hf hf_top hbd hint


-- created on 2026-10-09
