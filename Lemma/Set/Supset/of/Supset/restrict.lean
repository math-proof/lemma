import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {A B S : Set α}
-- given
  (h : A ⊇ B) :
-- imply
  A ⊇ B ∩ S :=
-- proof
  subset_trans Set.inter_subset_left h


-- created on 2021-07-05
-- updated on 2026-10-26
