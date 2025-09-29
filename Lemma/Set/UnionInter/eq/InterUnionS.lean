import sympy.Basic


@[main]
private lemma main
  {s t u : Set α} :
-- imply
  s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) := by
-- proof
  rw [Set.inter_union_distrib_right]


-- created on 2024-07-01
