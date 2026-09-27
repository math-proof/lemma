import Lemma.Random.Expect.le.ExpectAbs
import Lemma.Int.LeAbs.of.LeNeg.Le
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {f : Ω → ℝ}
-- given
  (h : Integrable f μ) :
-- imply
  |∫ ω, f ω ∂μ| ≤ ∫ ω, |f ω| ∂μ := by
-- proof
  have h₁ := Random.Expect.le.ExpectAbs h
  have h₂ := Random.Expect.le.ExpectAbs h.neg
  simp only [Pi.neg_apply, abs_neg, integral_neg] at h₂
  exact Int.LeAbs.of.LeNeg.Le h₂ h₁


-- created on 2026-09-26
