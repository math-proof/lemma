import sympy.Basic


@[main]
private lemma main
  {c : Prop} [Decidable c]
  {a b : α}
-- given
  (h : c) :
-- imply
  (if c then a else b) = a := by
-- proof
  rw [if_pos h]


@[main]
private lemma invert
  {c : Prop} [Decidable c]
  {a b : α}
-- given
  (h : ¬c) :
-- imply
  (if c then a else b) = b := by
-- proof
  rw [if_neg h]


-- created on 2026-09-27
