import Lemma.Basic


@[main]
private lemma main
  [Preorder α]
  {a b x : α}
-- given
  (h₀ : a < x)
  (h₁ : b > x) :
-- imply
  b > a := 
-- proof
  h₀.trans h₁


-- created on 2025-08-05
