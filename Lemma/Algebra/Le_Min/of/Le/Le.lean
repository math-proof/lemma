import Lemma.Basic


@[main]
private lemma main
  [LinearOrder α]
  {a b c : α}
-- given
  (h₀ : c ≤ a)
  (h₁ : c ≤ b) :
-- imply
  c ≤ a ⊓ b :=
-- proof
  le_min h₀ h₁


-- created on 2025-06-07
