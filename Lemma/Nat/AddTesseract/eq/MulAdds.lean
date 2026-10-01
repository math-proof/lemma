import sympy.sets.sets
import sympy.Basic


@[main]
private lemma quartic
  {x y : ℂ} :
-- imply
  x ^ 4 + 4 * y ^ 4 = (x ^ 2 + 2 * x * y + 2 * y ^ 2) * (x ^ 2 - 2 * x * y + 2 * y ^ 2) := by
-- proof
  ring


-- created on 2023-04-30
