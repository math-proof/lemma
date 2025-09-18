import Lemma.Basic


@[main]
private lemma main
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a = b)
  (h₁ : b < c) :
-- imply
  a < c := by
-- proof
  rwa [← h₀] at h₁


-- created on 2025-07-06
