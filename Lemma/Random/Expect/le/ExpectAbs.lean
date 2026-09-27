import Lemma.Int.GeAbs
import Lemma.Random.LeExpect.of.Le
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {f : Ω → ℝ}
-- given
  (h : Integrable f μ) :
-- imply
  ∫ ω, f ω ∂μ ≤ ∫ ω, |f ω| ∂μ := by
-- proof
  have h₁ : ∀ ω, f ω ≤ |f ω| := fun ω => Int.GeAbs (f ω)
  exact Random.LeExpect.of.Le h₁ h h.abs


-- created on 2026-09-26
