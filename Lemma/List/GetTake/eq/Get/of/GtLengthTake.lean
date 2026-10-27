import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {s : List α}
-- given
  (h : j < (s.take n).length) :
-- imply
  have : j < s.length := by simp_all
  (s.take n)[j] = s[j] := by
-- proof
  simp


-- created on 2025-06-07
-- updated on 2026-10-26
