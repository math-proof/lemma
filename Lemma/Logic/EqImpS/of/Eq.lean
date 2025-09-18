import Lemma.Basic


@[main]
private lemma main
  {f g : α → Sort}
-- given
  (h : f = g) :
-- imply
  ((x : α) → f x) = ((x : α) → g x) := by
-- proof
  rw [h]


-- created on 2025-07-16
