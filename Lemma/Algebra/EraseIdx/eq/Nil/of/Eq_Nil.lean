import Lemma.Basic


@[main]
private lemma main
  {v : List α}
-- given
  (h : v = []) :
-- imply
  v.eraseIdx i = [] := by
-- proof
  simp_all


-- created on 2025-06-24
