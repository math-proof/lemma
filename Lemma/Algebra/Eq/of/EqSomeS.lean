import Lemma.Basic


@[main]
private lemma main
  {a b : α}
-- given
  (h : some a = some b) :
-- imply
  a = b := by
-- proof
  simp_all


-- created on 2025-06-02
