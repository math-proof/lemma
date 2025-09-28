import Lemma.Basic


@[main]
private lemma main
  {v : List α}
-- given
  (h : j < (v.take n).length) :
-- imply
  have : j < v.length := by simp_all
  (v.take n)[j] = v[j] := by
-- proof
  simp


-- created on 2025-06-07
-- updated on 2025-06-28
