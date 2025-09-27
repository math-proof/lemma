import Lemma.Basic


@[main]
private lemma main
-- given
  (v : List α)
  (n : ℕ) :
-- imply
  v.splitAt n = ⟨v.take n, v.drop n⟩ := by
-- proof
  apply List.splitAt_eq


-- created on 2025-06-15
