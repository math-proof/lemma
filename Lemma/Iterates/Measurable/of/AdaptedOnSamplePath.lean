import sympy.stats.iterates
import sympy.Basic
import Lemma.Measure.Measurable_FrestrictLe_PiLE
open MeasureTheory Measure


@[main]
private lemma main
  {S Z : Type*} [MeasurableSpace S] [MeasurableSpace Z]
  {x : ℕ → (ℕ → S) → Z}
-- given
  (h : AdaptedOnSamplePath x)
  (n : ℕ) :
-- imply
  Measurable[Filtration.piLE n] (x n) := by
-- proof
  obtain ⟨xn, hxnm, hxn⟩ := h.property n
  rw [funext hxn]
  exact hxnm.comp (Measurable_FrestrictLe_PiLE n)


-- created on 2026-09-26