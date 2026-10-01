import sympy.Basic


@[main]
private lemma Comm
  [CommMagma α]
-- given
  (a b : α) :
-- imply
  a * b = b * a :=
-- proof
  mul_comm a b


@[main]
private lemma scale
  {a b c d : ℝ} :
-- imply
  (a / 2 + b / 2 - c) * d = (a + b - 2 * c) * d / 2 := by
-- proof
  ring


@[main]
private lemma distribute
  [Field α]
  {a b c d r : α} :
-- imply
  -r * (a - b - c) / d = (-r * a + r * b + r * c) / d := by
-- proof
  ring


-- created on 2018-08-19
-- updated on 2026-09-27
