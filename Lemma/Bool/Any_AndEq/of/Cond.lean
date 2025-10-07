import sympy.Basic


@[main]
private lemma main
  {f : α → Prop}
-- given
  (h : f e) :
-- imply
  ∃ i : α, i = e ∧ f i := by
-- proof
  use e


-- created on 2025-07-19
