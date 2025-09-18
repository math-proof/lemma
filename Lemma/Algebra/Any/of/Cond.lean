import Lemma.Basic


@[main]
private lemma main
  {p : α → Prop}
-- given
  (h : p e) :
-- imply
  ∃ e, p e := by
-- proof
  use e


-- created on 2025-07-19
