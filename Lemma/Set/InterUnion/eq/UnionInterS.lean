import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
-- given
  (s t u : Set α) :
-- imply
  (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u := by
-- proof
  rw [Set.union_inter_distrib_right]


-- created on 2024-07-01
-- updated on 2026-10-26
