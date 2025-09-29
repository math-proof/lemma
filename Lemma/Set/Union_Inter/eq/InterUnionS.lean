import sympy.Basic


@[main]
private lemma main
  {s t u : Set α} :
-- imply
  s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) := by
-- proof
  rw [Set.union_inter_distrib_left]


-- created on 2024-07-01
