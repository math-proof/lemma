import Lemma.Basic


@[main]
private lemma nat
  {a b : ℕ}
-- given
  (h : a ≥ b)
  (c : ℕ) :
-- imply
  c - a ≤ c - b :=
-- proof
  Nat.sub_le_sub_left h c


@[main]
private lemma main
  [AddGroup α]
  [LE α]
  [AddLeftMono α]
  [AddRightMono α]
  {a b : α}
-- given
  (h : a ≥ b)
  (c : α) :
-- imply
  c - a ≤ c - b :=
-- proof
  sub_le_sub_left h c


-- created on 2025-06-19
