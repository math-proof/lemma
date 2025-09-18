import Lemma.Basic


@[main]
private lemma nat
  {x y : ℕ}
-- given
  (h : x ≤ y)
  (z : ℕ) :
-- imply
  x - z ≤ y - z :=
-- proof
  Nat.sub_le_sub_right h z


-- created on 2024-07-01
