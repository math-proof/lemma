import Lemma.Basic


@[main]
private lemma main
  {a b : ℕ}
-- given
  (h₀ : c ≤ a)
  (h₁ : a < b) :
-- imply
  a - c < b - c :=
-- proof
  Nat.sub_lt_sub_right h₀ h₁


-- created on 2025-06-19
