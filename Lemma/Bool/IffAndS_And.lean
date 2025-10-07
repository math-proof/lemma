import sympy.Basic


@[main]
private lemma main
  {a b c : Prop} :
-- imply
  a ∧ b ∧ c ↔ b ∧ a ∧ c :=
-- proof
  and_left_comm


-- created on 2025-03-26
