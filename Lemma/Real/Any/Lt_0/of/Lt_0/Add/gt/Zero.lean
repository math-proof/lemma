import Lemma.Real.Any.Lt_0.of.Lt_0.Add.ge.Zero


@[main]
private lemma main
  {a b c : ℝ}
-- given
  (h₀ : a < 0)
  (h₁ : b ^ 2 - 4 * a * c > 0) :
-- imply
  ∃ x, a * x ^ 2 + b * x + c < 0 := by
-- proof
  exact Real.Any.Lt_0.of.Lt_0.Add.ge.Zero h₀ (by linarith)


-- created on 2022-04-03
