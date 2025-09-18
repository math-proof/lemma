import Lemma.Basic


@[main]
private lemma main
  {a b : α}
  {p : α → Prop}
-- given
  (h₀ : a = b)
  (h₁ : p a) :
-- imply
  p b := by
-- proof
  rwa [← h₀]


-- created on 2025-07-29
