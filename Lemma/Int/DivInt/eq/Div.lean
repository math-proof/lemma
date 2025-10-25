import sympy.Basic


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  Rat.divInt n d = (n:ℚ) / (d:ℚ) := by
-- proof
  norm_cast


-- created on 2025-03-30
