import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {c : Prop}
  [Decidable c]
  {a b d e : ℝ} :
-- imply
  (if c then a + b else d + e) = (if c then a else d) + (if c then b else e) := by
-- proof
  split_ifs <;> rfl


-- created on 2026-09-27
