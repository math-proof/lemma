import Lemma.Nat.Le_Sub.is.LeAdd.of.Le
open Nat


@[main]
private lemma main
  {a b c : ℕ}
-- given
  (h : a + b ≤ c) :
-- imply
  a ≤ c - b := by
-- proof
  apply Le_Sub.of.LeAdd.Le _ h
  linarith


@[main]
private lemma left
  {a b c : ℕ}
-- given
  (h : a + b ≤ c) :
-- imply
  b ≤ c - a := by
-- proof
  apply Le_Sub.of.LeAdd.Le.left _ h
  linarith


-- created on 2025-08-02
-- updated on 2025-10-16
