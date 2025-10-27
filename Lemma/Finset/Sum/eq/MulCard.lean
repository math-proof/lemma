import sympy.Basic


@[main]
private lemma main
  [AddCommMonoid β]
-- given
  (s : Finset α)
  (b : β) :
-- imply
  ∑ _ ∈ s, b = s.card • b :=
-- proof
  Finset.sum_const b


-- created on 2025-07-19
