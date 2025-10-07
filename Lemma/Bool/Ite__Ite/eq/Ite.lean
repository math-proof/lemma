import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  {a a' b : α} :
-- imply
  (if p then
    a
  else if p then
    a'
  else
    b) = if p then
    a
  else
    b := by
-- proof
  -- Split the proof into two cases based on the truth value of p
  by_cases h : p <;>
    simp_all


-- created on 2025-04-28
