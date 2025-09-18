import stdlib.SEq
import stdlib.List.Vector


@[main]
private lemma main
  {a : List.Vector α n}
  {b : List.Vector α m}
-- given
  (h : a ≃ b) :
-- imply
  a.length = b.length := by
-- proof
  simp [h.left]


-- created on 2025-05-31
