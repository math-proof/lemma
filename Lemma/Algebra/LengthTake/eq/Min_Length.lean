import Lemma.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (n : ℕ) :
-- imply
  (s.take n).length = n ⊓ s.length := by
-- proof
  simp [min]


-- created on 2025-05-13
-- updated on 2025-05-17
