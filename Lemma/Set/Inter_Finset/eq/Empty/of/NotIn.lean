import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {e : α}
  {s : Set α}
-- given
  (h : e ∉ s) :
-- imply
  s ∩ {e} = ∅ :=
-- proof
  Set.inter_singleton_of_notMem h


-- created on 2019-01-31
-- updated on 2026-10-26
