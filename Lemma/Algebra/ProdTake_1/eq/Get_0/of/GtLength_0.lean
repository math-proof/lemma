import Lemma.Basic


@[main]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h_s : s.length > 0) :
-- imply
  (s.take 1).prod = s[0] := by
-- proof
  aesop


-- created on 2025-07-08
-- updated on 2025-07-17
