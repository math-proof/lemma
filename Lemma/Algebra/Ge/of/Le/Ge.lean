import Lemma.Basic


@[main]
private lemma main
  [Preorder α]
  {a b x : α}
-- given
  (h₀ : x ≤ a)
  (h₁ : x ≥ b) :
-- imply
  a ≥ b :=
-- proof
  h₁.trans h₀


-- created on 2025-08-04
