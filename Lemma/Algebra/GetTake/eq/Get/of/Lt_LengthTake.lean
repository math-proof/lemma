import Lemma.Basic


@[main]
private lemma main
  {v : List α}
-- given
  (h : j < (v.take n).length) :
-- imply
  have : j < v.length := by simp_all [h]
  (v.take n)[j] = v[j] := by
-- proof
  simp_all


-- created on 2025-06-07
-- updated on 2025-06-28
