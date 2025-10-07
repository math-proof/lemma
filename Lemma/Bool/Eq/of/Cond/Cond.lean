import sympy.Basic


@[main]
private lemma main
  {p : Prop}
-- given
  (h_a : p)
  (h_b : p):
-- imply
  h_a = h_b :=
-- proof
  proof_irrel h_a h_b


-- created on 2025-07-13
