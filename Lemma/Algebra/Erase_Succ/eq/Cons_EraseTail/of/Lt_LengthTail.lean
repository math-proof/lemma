import Lemma.Basic


@[main]
private lemma main
  {v : List α}
-- given
  (h : i < v.tail.length)
  (default : α):
-- imply
  v.eraseIdx i.succ = v.headD default :: v.tail.eraseIdx i := by
-- proof
  cases v
  ·
    contradiction
  ·
    rfl


-- created on 2025-06-09
