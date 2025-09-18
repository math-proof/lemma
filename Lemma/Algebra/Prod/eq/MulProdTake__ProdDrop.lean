import Lemma.Basic


@[main]
private lemma main
  [Monoid α]
-- given
  (v : List α)
  (i : ℕ):
-- imply
  v.prod = (v.take i).prod * (v.drop i).prod := by
-- proof
  simp


-- created on 2025-06-08
