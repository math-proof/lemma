import Instance.MeasureTheory.Integral.IntervalIntegral.Integrals.Part4


@[path]
private lemma main
  {a b d : ℝ}
  {f : ℝ → ℝ} :
-- imply
  ∫ x : ℝ in a..b, f x = ∫ x : ℝ in (a - d)..(b - d), f (x + d) := by
-- proof
  simp


-- created on 2020-06-05
-- updated on 2026-10-26
