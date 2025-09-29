import sympy.Basic


@[main]
private lemma main
  {a b c : Prop} :
-- imply
  (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b :=
-- proof
  and_right_comm


-- created on 2025-03-26
